-- 
-- (C) Susumu Katayama
--
{-# LANGUAGE CPP #-}
module MagicHaskeller.Analytical.Synthesize where

import Data.List(transpose, genericLength, genericTake)
-- import Control.Monad.Search.RecompDL -- a version using DList, but did not actually improve the efficiency.
import Control.Monad -- hiding (guard)
import Control.Monad.State -- hiding (guard)
import qualified Data.IntMap as IntMap

import Language.Haskell.TH

import Control.Monad.Search.Combinatorial
import MagicHaskeller.CoreLang hiding (C)
import qualified MagicHaskeller.Types as Types
import MagicHaskeller.TyConLib
import MagicHaskeller.PriorSubsts hiding (unify)

import MagicHaskeller.Analytical.Syntax
import MagicHaskeller.Analytical.Parser
import MagicHaskeller.Analytical.UniT
import MagicHaskeller.Analytical.FMExpr

import Data.Int
import Data.Word

-- | function specification by examples.
data Fun a = BKF {maxNumBVs :: Int, arity :: Int, iopairs :: [IOPair a], fmexpr :: FMExpr [IOPair a]} -- ^ the function is really a background knowledge (and thus there is no need for loop check)     
           | Rec {maxNumBVs :: Int, arity :: Int, iopairs :: [IOPair a], fmexpr :: FMExpr [IOPair a], toBeSought :: TBS} -- ^ it is actually a recursive call.
mkBKFun          iops@(iop:_) = BKF {maxNumBVs = maximum $ map numUniIDs iops, arity = length $ inputs iop, iopairs = iops, fmexpr = iopsToFME iops}
mkRecFun ari tbs iops@(iop:_) = Rec {maxNumBVs = maximum $ map numUniIDs iops, arity = ari, iopairs = iops, fmexpr = iopsToVisFME tbs iops, toBeSought = tbs} -- arity = filter id tbs, but it is usually know beforehand
mkInitRecFun     iops@(iop:_) = let aritar = length $ inputs iop in mkRecFun aritar (replicate aritar True) iops
setIOPairs iops recfun@Rec{toBeSought=tbs} = recfun{iopairs = iops, fmexpr = iopsToVisFME tbs iops}
type BK a = [Types.Typed (Fun a)]      -- ^ background knowledge.

applyFun s fun = fun{iopairs = applyIOPs s (iopairs fun)}


analyticSynth :: Search m => TyConLib -> VarLib -> [Dec] -> [Dec] -> m CoreExpr
analyticSynth tcl vl target bkdec = fst $ analyticSynthAndInfType tcl vl target bkdec
analyticSynthAndInfType :: Search m => TyConLib -> VarLib -> [Dec] -> [Dec] -> (m CoreExpr, Types.Type)
analyticSynthAndInfType tcl vl target bkdec
    = case unPS (liftM2 (,) (parseTypedIOPairss tcl xvl target) (parseTypedIOPairss tcl xvl bkdec)) Types.emptySubst 0 of
        Nothing -> error "Type error occurred while reading the IO pairs."
        Just (([],_),_,_) ->error "MagicHaskeller.Synthesize.analyticSynth*: No I/O pairs are defined as the target."
        Just (([(targetFunName, iops@(iop:_) Types.:::ty)],bktups),_,mx) ->
               let (bknames, bktiopss) = unzip bktups
                   (bkiopss, bktypes)  = unzipTyped bktiopss
                   target = mkRecFun aritar tbs iops
                   tbs = replicate aritar True                   
                   aritar = length $ inputs iop
                   aritar8 = fromIntegral aritar
                   bk = reverse $ zipWith (Types.:::) (map mkBKFun $ bkiopss) bktypes
               in (fmap (\e -> napply (length bktups) FunLambda $ napply aritar Lambda (Fix e aritar8 [aritar8-1, aritar8-2..0])) $   --  $ Fix e $ map X [arity-1, arity-2 .. 0]) $     -- 本当はこの結果のそれぞれに bknamesを適用したいのだが，bknamesなHValueがないので.... てゆーか，Expなら作れる．CoreExprも，BKが全部VarLibにはいっていれば作れる．
                   fastAnalSynthNoUniT bk (target Types.::: ty)
                  ,foldr (Types.:->) ty bktypes)
        _ -> error "MagicHaskeller.Synthesize.analyticSynth*: More than one I/O pairs are defined as the target."
    where xvl = mkXVarLib vl


fastAnalSynthNoUniT bk tfun@(fun Types.::: _) | any hasExistential $ map output $ iopairs fun = analSynthNoUniT bk tfun
                                              | otherwise                                  = fastAnalSynthmNoUniT bk tfun

--fastAnalSynthNoUniT = fastAnalSynthmNoUniT
fastAnalSynthmNoUniT bk tfun
    = others `mplus` delay bkRelated
  where newbk = tfun : bk
        bkRelated = headSpine analSynthNoUniT introBKm newbk tfun 
        others    = headSpine fastAnalSynthNoUniT (introConstr +++ introVarm +++ ndelayIntro 2 introCase) newbk tfun

analSynthNoUniT bk tfun
  = headSpine analSynthNoUniT (introConstr +++ introVarm' +++ ndelayIntro 2 introCase +++ ndelayIntro 1 introBKm) (tfun:bk) tfun

{-
The following definition of analSynth should work even if 
- existential variables are included in BK or in Fun, e.g. a function binding 
  f a = b
  is included
  or
- the same variable name appear multiple times in the LHS (input examples) of an I/O example in BK or in Fun, E.g. a function binding
  f a a = 1
  is included.
Those bindings are not valid Haskell, nor accepted by Template Haskell, so a library like haskell-src has to be used for parsing them.
-}
analSynth, analSynthm, fastAnalSynthNoUniT :: Search m => BK a -> Types.Typed (Fun a) -> m CoreExpr
analSynth bk tfun@(fun Types.::: _) | any hasExistential $ map output $ iopairs fun = fmap fst $ runStateT (analSynthUTm bk tfun) emptySt
                                    | otherwise                                  = analSynthm bk tfun
analSynthm bk tfun
    = others `mplus` delay bkRelated
  where newbk = tfun : bk
        bkRelated = headSpine analSynth introBKm newbk tfun 
        others    = headSpine analSynthm (introConstr +++ introVarm +++ ndelayIntro 2 introCase) newbk tfun
headSpine rec intro bk tfun 
  = do (hd, subfuns, mbpivot) <- intro bk tfun
       subexps <- mapM (\subfun -> let arisub = fromIntegral $ arity $ Types.typee subfun :: Int8 in fmap (\e -> Fix e arisub (mkArgs mbpivot arisub)) $ rec bk subfun)  subfuns
       return (hd subexps)
#ifdef DEBUG
headSpine_debug rec trs intro bk tfun 
  = do (hd, subfuns, mbpivot) <- intro bk tfun
       subexps <- zipWithM (\tr subfun -> let arisub = fromIntegral $ arity $ Types.typee subfun in fmap (\e -> Fix e arisub (mkArgs mbpivot arisub)) $ rec tr bk subfun) trs subfuns
       return (hd subexps)
#endif

analSynthUTm :: Search m => BK a -> Types.Typed (Fun a) -> UniT a m CoreExpr
-- analSynthm ([], _, _) = mzero -- If there is no example, nothing can be done. (But is this line necessary?)
analSynthUTm bk (fun Types.::: ty)
    = do 
         s <- gets subst
         let aptfun = applyFun s fun Types.::: ty
             newbk  = aptfun : bk
         headSpine analSynthUTm introAny newbk aptfun

mkArgs Nothing arisub = [arisub-1,arisub-2..0]
mkArgs (Just pivot) arisub = genericTake pivot [arisub,arisub-1..] ++ [arisub-pivot-1,arisub-pivot-2..0]

#ifdef DEBUG
analyticSynthNoUniT_debug :: Search m => Tree (Introducer a m) ->  TyConLib -> VarLib -> [Dec] -> [Dec] -> m CoreExpr
analyticSynthNoUniT_debug tree tcl vl target bkdec
    = case unPS (liftM2 (,) (parseTypedIOPairss tcl xvl target) (parseTypedIOPairss tcl xvl bkdec)) Types.emptySubst 0 of
        Nothing -> error "Type error occurred while reading the IO pairs."
        Just (([],_),_,_) ->error "TypedIOPairs.analyticSynth*: No I/O pairs are defined as the target."
        Just (([(targetFunName, iops@(iop:_) Types.:::ty)],bktups),_,mx) ->
               let (bknames, bktiopss) = unzip bktups
                   (bkiopss, bktypes)  = unzipTyped bktiopss
                   target = mkRecFun aritar tbs iops
                   tbs = replicate aritar True                   
                   aritar = length $ inputs iop
                   bk = reverse $ zipWith (Types.:::) (map mkBKFun $ bkiopss) bktypes
               in (fmap (\e -> napply (length bktups) FunLambda $ napply aritar Lambda (Fix e aritar [aritar-1, aritar-2..0])) $   --  $ Fix e $ map X [arity-1, arity-2 .. 0]) $     -- 本当はこの結果のそれぞれに bknamesを適用したいのだが，bknamesなHValueがないので.... てゆーか，Expなら作れる．CoreExprも，BKが全部VarLibにはいっていれば作れる．
                   analSynthNoUniT_debug tree bk (target Types.:::ty)
                  )
        _ -> error "TypedIOPairs.analyticSynth*: More than one I/O pairs are defined as the target."
    where xvl = mkXVarLib vl
analSynthNoUniT_debug (Br intro trs) bk tfun
  = headSpine_debug analSynthNoUniT_debug trs intro (tfun:bk) tfun


data Tree x = Br x [Tree x] deriving Show
tryall, tryVar :: Search m => Tree (IntroUniT a m)
tryall = Br introAny (repeat tryall)
tryVar = Br introVarUTm []
tryVarm :: (Functor m, MonadPlus m) => Tree (Introducer a m)
tryVarm = Br introVarm []

analyticSynth_debug :: Search m => Tree (IntroUniT a m) -> TyConLib -> VarLib -> [Dec] -> [Dec] -> m CoreExpr
analyticSynth_debug tree tcl vl target bkdec
    = do ((tgt,bktups),_,mx) <-
             unPS (liftM2 (,) (parseTypedIOPairss tcl xvl target) (parseTypedIOPairss tcl xvl bkdec)) Types.emptySubst 0
         case tgt of
           [] -> error "analyticSynth: No I/O pairs are defined as the target."
           [(targetFunName, iops@(iop:_) Types.:::ty)] ->
               let (bknames, bktiopss) = unzip bktups
                   (bkiopss, bktypes)  = unzipTyped bktiopss
                   target = mkRecFun aritar tbs iops
                   tbs = replicate aritar True
                   aritar = length $ inputs iop
                   bk = reverse $ zipWith (Types.:::) (map mkBKFun $ bkiopss) bktypes
               in fmap (\(e,_st) -> napply (length bktups) FunLambda $ napply aritar Lambda (Fix e aritar [aritar-1, aritar-2..0])) $   --  $ Fix e $ map X [arity-1, arity-2 .. 0]) $     -- 本当はこの結果のそれぞれに bknamesを適用したいのだが，bknamesなHValueがないので.... てゆーか，Expなら作れる．CoreExprも，BKが全部VarLibにはいっていれば作れる．
                        runStateT (analSynthUT_debug tree bk (target Types.::: ty)) emptySt -- ONLY DIFFER HERE.
           _ -> error "analyticSynth: More than one I/O pairs are defined as the target."
    where xvl = mkXVarLib vl

-- | 'analSynthUT_debug' can be used to try only the given introducer at each selection point. @analSynthUT = analSynthUT_debug tryall@
analSynthUT_debug :: Search m => Tree (IntroUniT a m) -> BK a -> Types.Typed (Fun a) -> UniT a m CoreExpr
analSynthUT_debug (Br intro iss) bk (fun Types.::: ty)
    = do
         s <- gets subst
         let aptfun = applyFun s fun Types.::: ty
             newbk   = aptfun : bk
         (hd, subfuns, mbpivot) <- intro newbk aptfun
         subexps <- zipWithM (\is subfun -> let arisub = arity $ Types.typee subfun in fmap (\e -> Fix e arisub (mkArgs mbpivot arisub)) $ analSynthUT_debug is newbk subfun) iss subfuns
         return (hd subexps)
#endif

type Introducer a m = BK a -> Types.Typed (Fun a) -> m ([CoreExpr] -> CoreExpr, [Types.Typed (Fun a)], Maybe Int8)
type IntroUniT  a m = Introducer a (UniT a m)
-- NB: We should not use @StateT Env@ where @Env=(BK a,TBS)@ because the Env affects only subexpressions.

il +++ ir = \bk iops -> il bk iops `mplus` ir bk iops
ndelayIntro n intro = \e a -> ndelay n $ intro e a

introAny :: Search m => IntroUniT a m
introAny     =          introConstr +++ {- +/ -} (
                        introVarUTm +++
                        ndelayIntro 1 introBKUTm +++
                        ndelayIntro 2 introCase )

(+/) :: MonadPlus m => IntroUniT a [] -> IntroUniT a m -> IntroUniT a m
m +/ n = \bk iops ->
         do st <- get
       	    case runStateT (m bk iops) st of [] -> n bk iops
                                             ts -> StateT $ \_ -> msum $ map return ts
liftList :: MonadPlus m => StateT s [] a -> StateT s m a
liftList = mapStateT (msum . map return)

introVarm, introVarm', introConstr, introCase :: (Functor m, MonadPlus m) => Introducer a m -- introConstrでは，実際にはCoreExprはConstrでよい．
introBKm :: (Search m) => Introducer a m -- introConstrでは，実際にはCoreExprはConstrでよい．
introVarUTm, introBKUTm :: MonadPlus m => IntroUniT a m
-- introVarUTmは一連のIgor関係の論文にはないものの，introBKが有効に働くには必要．これがないと，fを作るのにBKとしてfを使っても，introBKだけで終わってくれず，生成されない．
{- introBKのあとのintroVarUTmをintroBKに含めようとして，やっぱ止めた．
introVarUTm (iops,_,_,True) = mzero
introVarUTm (iops,_,_,False)  = msum $ map (\(ix,_) -> return (const (X ix), [])) $ filter (\(_,inp) -> inp == map output iops) $ zip [0..] $ transpose $ map inputs iops
-}
-- introVarUTm (iops,_,_,_)  = msum $ map (\(ix,_) -> return (const (X ix), [])) $ filter (\(_,inp) -> inp == map output iops) $ zip [0..] $ transpose $ map inputs iops
introVarUTm b f = liftList $ introVar (zipWithM_ appUnifyUT) b f
-- introVarm b f  = introVar (zipWithM_ unify) b f  *************************************** これはデバッグ時に有用なことも．
introVarm   = introVar (\a b -> guard $ a==b)

introVarm' = introVar (zipWithM_ unify)

introVar :: MonadPlus m => ([Expr a] -> [Expr a] -> m ()) -> Introducer a m
introVar cmp _ (fun Types.::: ty)
               = do let (argtys, retty) = Types.splitArgs ty
                        iops = iopairs fun
                        arifun = arity fun
                    let trins = transpose $ map inputs iops
--                    (ix,inps Types.::: argty) <- msum $ map return $ zip [0..] trins
                    (ix,argty,inps) <- msum [ return t | t@(_,aty,_) <- zip3 [0..] argtys $ visibles (toBeSought fun) trins, Types.mgu aty retty /= Nothing]

-- The following four lines should be equivalent to
                    cmp (map output iops) inps
-- but use of Maybe and simpler substitutions should be good for efficiency.
{-
                    st0 <- get
                    case runStateT (zipWithM_ appUnifyUT (map output iops) inps) st0{subst=[]} of
                              Just ((),st) -> put (st{subst= subst st `plusSubst` subst st0})
	  	     	      Nothing      -> mzero
-}
                    return (const (X ix), [], Nothing)

introConstr bk (fun Types.::: ty)
    = let argtys = Types.getArgs ty 
          iops   = iopairs fun
      in
      case [ output iop | iop <- iops ] of
        outs@(C _ _ (cid Types.::: cty) flds : rest)
            | all (`sConstrIs` cid) rest -> return (foldl (:$) (PrimCon cid),
                                                    zipWith (\iops retty -> setIOPairs iops fun Types.::: Types.popArgs argtys retty)
                                                            (transpose [ divideIOP iop | iop <- iops ])
                                                            (case Types.revSplitArgs cty of (_,fieldtys,_) -> fieldtys),
                                                    Nothing)
        _                        -> mzero
divideIOP (IOP bvs ins out) = map (IOP bvs ins) $ fields out -- The actual number of buondVars may reduce, but not updating the field would not hurt.

shareConstr (C _ _ (cid Types.::: _) _ : iops) = all (`sConstrIs` cid) iops 
shareConstr _                = False
-- typeが違うと同じcidを異なるconstructorで使い得る場合，typeごと比較する必要があるが，現在はそうではないので．
C _ _ (c Types.::: _) _ `sConstrIs` cid = cid==c
_                       `sConstrIs` cid = False


select []     []      = []
select (b:bs) (p:ps) | b         = (p, False:bs) : rest
                     | otherwise = rest
            where rest = [ (result, b:newbs) | (result,newbs) <- select bs ps ]

introCase bk (fun Types.::: ty) = msum $ reverse $ zipWith introCase' [0..] $ select (toBeSought fun) trins
    where trins = transpose $ map inputs iops
          (argtys,retty) = Types.splitArgs ty
          iops   = iopairs fun
          arifun = arity fun
          {-
          introCase' :: MonadPlus m =>
                         Int              -- ^ the pivot position
                         -> ([Expr a],TBS)  -- ^ (the pivot expression for each I/O pair, the next TBS)
                         -> m ([CoreExpr] -> CoreExpr, [Types.Typed (Fun a)], Maybe Int)
          -}          
          introCase' pos (pivots, tbs) -- includes variable cases. Overlapping patterns are not supported yet.
              = case mapM maybeCtor pivots of 
                  Nothing -> mzero
                  Just ctors
                      -> let
                             pipairs = zip pivots iops -- :: [(Expr a, IOPair a)]
                             ts      = IntMap.toList $ IntMap.fromListWith (\(t,xs) (_,ys) -> (t,xs++ys)) $
                                           zipWith (\(c Types.::: ct) x -> (fromIntegral c,(ct,[x]))) ctors pipairs
                                              -- :: [(Constr, (Types.Type, [(Expr a,IOPair a)]))]
                  -- Array.accum can also be used instead of IntMap because we can tell the range from that of VarLib.
                             hd ces = Case (X $ fromIntegral pos)
                                            (zipWith (\(constr, (_, (pivot,_):_)) ce -> (fromIntegral constr, genericLength (fields pivot), ce))
                                                     ts
                                                     ces)
                             iopss  = [ Rec { maxNumBVs  = maxNumBVs fun, 
                                              arity      = arifun-1+lenflds,
                                              iopairs    = iops,
                                              fmexpr     = iopsToVisFME newtbs iops,
                                              toBeSought = newtbs
                                            }
                                          Types.::: Types.popArgs (dropNth pos argtys) (Types.popArgs (Types.getArgs cty) retty)
                                      | (_c, (cty, nextpipairs@((C _ _ _ flds', _):_))) <- ts,
                                        let lenflds = length flds'
                                            iops    = [ IOP bvs (reverse flds ++ is) o | (C _ _ _c flds, IOP bvs is o) <- nextpipairs ]
                                            newtbs  = replicate lenflds True ++ tbs
                                      ]
                         in return (hd, iopss, Just (fromIntegral $ arifun - pos-1))

dropNth pos bs = case splitAt pos bs of (tk,_:dr) -> tk ++ dr



introBKm   bk tfun = fromMx $ toMx $ introBK subtractIOPairsFromIOPairsBKm subtractIOPairsFromIOPairsm bk tfun
introBKUTm bk tfun = liftList $ introBK (const subtractIOPairsFromIOPairsBKUTm) (const subtractIOPairsFromIOPairsUTm) bk tfun
introBK subBK sub bk (fun Types.:::ty) = do          
                              let (argtys, retty) = Types.splitArgs ty
                              (ix, bkfun Types.::: bkty) <- msum $ map return $ tail $ zip [0..] bk
                                              -- The tail function here is used to avoid generating expressions like
                                              -- fix (\fa x1 ... xn -> fa ...).
                                              -- Such expressions would be excluded by the loop checker even without the tail function, 
                                              -- but we exclude them beforehand for efficiency reasons.
                              let (bkargtys, bkretty) = Types.splitArgs bkty
                              substy <- Types.match bkretty retty
                              iopss <- case bkfun of BKF{maxNumBVs=addendum} -> subBK (-addendum) (iopairs fun) bkfun
                                                     Rec{maxNumBVs=addendum} -> sub (-addendum) initTS fun bkfun
                              return (foldl (:$) (FunX ix),
                                      [ setIOPairs iops fun Types.::: tys 
                                      | iops Types.::: tys <- reverse $ 
                                                              zipWith (\x retty -> x Types.::: Types.popArgs argtys retty)
                                                                      (transpose iopss)
                                                                      (map (Types.apply substy) bkargtys) ],
                                      Nothing)



subtractIOPairsFromIOPairsBKUTm :: MonadPlus m => [IOPair a] -> (Fun a) -> UniT a m [[IOPair a]]
{-
subtractIOPairsFromIOPairsBK funs bks = foldr (liftM2 (:)) (return []) $ map (flip subtractIOPairs bks) funs
-}
subtractIOPairsFromIOPairsBKUTm []         bkf = return []
subtractIOPairsFromIOPairsBKUTm (fun:funs) bkf = do 
                                                 iops <- subtractIOPairsBKUTm fun bkf
                                                 iopss <- subtractIOPairsFromIOPairsBKUTm funs bkf -- iopsは，subfunctionが複数あって，それらsubfunctionsのそれぞれに関してIOPair1個ずつに過ぎない．
                                                 return (iops:iopss)
-- Applying substitutions to funs is not currently necessary (because funs does not include existential variables), but that will be useful in future versions which fill gaps of input examples.

{-
subtractIOPairs :: IOPair -> [IOPair] -> [[IOPair]] -- 内側リストの基数はfunのarity, 外側はbkのIO pairのうちmatchするのはいくつあるか
                                                    -- てゆーか，内側はbkのarityでは？
subtractIOPairs fun bkpairs = [ iops | bk <- bkpairs, iops <- subtractIOPair fun bk ]
-}
subtractIOPairsBKUTm :: MonadPlus m => IOPair a -> (Fun a) -> UniT a m [IOPair a] -- 内側リストの基数はfunのarity, 外側はbkのIO pairのうちmatchするのはいくつあるか
                                                    -- てゆーか，内側はbkのarityでは？
subtractIOPairsBKUTm tgt bkf = do 
                               s <- gets subst
                               let aptgt = applyIOP  s tgt
                                   apbkf = applyIOPs s $ iopairs bkf
                               bkiop <- msum $ map return apbkf
                               subtractIOPairUTm aptgt bkiop
subtractIOPairsFromIOPairsUTm :: MonadPlus m => TermStat -> Fun a -> Fun a -> UniT a m [[IOPair a]]
subtractIOPairsFromIOPairsUTm ts tgt bkf = subtractIOPairsFromIOPairsUTm' ts (iopairs tgt) bkf
subtractIOPairsFromIOPairsUTm' :: MonadPlus m => TermStat -> [IOPair a] -> Fun a -> UniT a m [[IOPair a]]
{-
subtractIOPairsFromIOPairs funs bks = foldr (\fun rest -> do iops <- subtractIOPairs fun bks
                                                             iopss <- rest
                                                             return (iops:iopss)) (return []) funs
-}
subtractIOPairsFromIOPairsUTm' ts []         bkf = return []
subtractIOPairsFromIOPairsUTm' ts (fun:funs) bkf = do
                                (iops,newts) <- subtractIOPairsUTm ts fun bkf
                                iopss        <- subtractIOPairsFromIOPairsUTm' newts funs bkf -- iopsは，subfunctionが複数あって，それらsubfunctionsのそれぞれに関してIOPair1個ずつに過ぎない．
                                return (iops:iopss)
subtractIOPairsUTm :: MonadPlus m => TermStat -> IOPair a -> (Fun a) -> UniT a m ([IOPair a], TermStat) -- 内側リストの基数はfunのarity, 外側はbkのIO pairのうちmatchするのはいくつあるか
                                                    -- てゆーか，内側はbkのarityでは？
subtractIOPairsUTm ts tgt bkf = do
                                s <- gets subst
                                let aptgt = applyIOP s tgt
                                    bktbs = toBeSought bkf
                                    -- apbkf = applyIOPs s bkf
                                    apvistgt = reverse $ visibles (reverse bktbs) $ reverse $ inputs aptgt
                                bkiop <- msum $ map return $ iopairs bkf
                                let visbki = visibles bktbs $ inputs bkiop
                                guard $ evalTS $ updateTS visbki apvistgt ts  -- applyするまえのbkfで投機的にfilterしてみたけど，いまいち．
                                let apvisbki = map (apply s) visbki
                                iops <- subtractIOPairUTm aptgt bkiop{inputs=apvisbki, output=apply s $ output bkiop}
                                let newts = updateTS apvisbki apvistgt ts -- This makes sure that the generated program does not go into a loop.
                                guard $ evalTS newts
--                                guard $ lessExprss (reverse bkis) (reverse apis)
                                return (iops, newts)

-- 例えば，join [x,y] [z,w] = [x,y,z,w]からbk [a,b] [c,d] = [a,c,b,d]を引くことを考える．
-- join [x,y] [z,w] = bk (f [x,y] [z,w]) (g [x,y] [z,w])においてf [x,y] [z,w] = [x,z], g [x,y] [z,w] = [y,w]なので，
-- subtractIOPair IOP{inputs=[[x,y],[z,w]],output=[x,y,z,w]} IOP{inputs=[[a,b],[c,d]],output=[a,c,b,d]} = [IOP{inputs=[[x,y],[z,w]],output=[x,z]}, IOP{inputs=[[x,y],[z,w]],output=[y,w]}]
-- ということになる．
subtractIOPairUTm :: MonadPlus m => IOPair a -> IOPair a -> UniT a m [IOPair a]
subtractIOPairUTm fun bkiop
                      = do frbkiop <- freshIOP bkiop
                           unifyUT (output frbkiop) (output fun)
                           s <- gets subst
                           return [ fun{output=apply s o} | o <- inputs frbkiop ] -- This @apply@ is necessary here because introBKm will soon forget the substitution.

subtractIOPairsFromIOPairsm :: Int -- maxNumBVsでゲットできる値．
                               -> TermStat -> Fun a -> Fun a -> [] [[IOPair a]]
subtractIOPairsFromIOPairsm addendum ts tgt bkf
    = subtractIOPairsFromIOPairsmFME addendum ts (length $ filter id $ toBeSought tgt) -- the actual arity
        (iopairs tgt) bkf addendum
subtractIOPairsFromIOPairsmFME :: Int -> TermStat -> Int -> [IOPair a] -> Fun a -> Int -> [] [[IOPair a]]
{-
subtractIOPairsFromIOPairsBK funs bks = foldr (liftM2 (:)) (return []) $ map (flip subtractIOPairs bks) funs
-}
subtractIOPairsFromIOPairsmFME addendum ts ary []         bkf offset = return []
subtractIOPairsFromIOPairsmFME addendum ts ary (fun:funs) bkf offset = do 
                                                 (iops,newts) <- subtractIOPairsmFME ts ary fun bkf offset
                                                 iopss <- subtractIOPairsFromIOPairsmFME addendum newts ary funs bkf (offset+addendum) -- iopsは，subfunctionが複数あって，それらsubfunctionsのそれぞれに関してIOPair1個ずつに過ぎない．
                                                 return (iops:iopss)
-- Applying substitutions to funs is not currently necessary (because funs does not include existential variables), but that will be useful in future versions which fill gaps of input examples.

subtractIOPairsmFME :: TermStat -> Int -> IOPair a -> Fun a -> Int -> [([IOPair a], TermStat)] -- 返り値の[IOPair]は各引数に対応
subtractIOPairsmFME ts ary tgtiop bkf offset 
  = case output tgtiop of E{}  -> [(replicate (arity bkf) tgtiop, ts)] -- targetの返り値が単にexistential variableの場合，使われないのでなんでもよい．が，arityを揃える必要がある．
                          tgto -> do 
                                let vistgt = reverse $ visibles (reverse $ toBeSought bkf) $ reverse $ inputs tgtiop
                                visbkis <- unifyingIOPairs tgto (fmexpr bkf) offset
                                let iops = [ tgtiop{output=o} | o <- visbkis ]
                                let newts = updateTS visbkis vistgt ts -- This makes sure that the generated program does not go into a loop.
                                guard $ evalTS newts
--                                guard $ lessExprss (reverse bkis) (reverse apis)
                                return (iops, newts)
                                
                                
subtractIOPairsFromIOPairsBKm :: Int -- maxNumBVsでゲットできる値．
                                 -> [IOPair a] -> (Fun a) -> [] [[IOPair a]]
subtractIOPairsFromIOPairsBKm addendum tgt bkf = subtractIOPairsFromIOPairsBKmFME addendum tgt (iopsToFME $ iopairs bkf) addendum
subtractIOPairsFromIOPairsBKmFME :: Int -> [IOPair a] -> FMExpr [IOPair a] -> Int -> [] [[IOPair a]]
{-
subtractIOPairsFromIOPairsBK funs bks = foldr (liftM2 (:)) (return []) $ map (flip subtractIOPairs bks) funs
-}
subtractIOPairsFromIOPairsBKmFME addendum []         bkf offset = return []
subtractIOPairsFromIOPairsBKmFME addendum (fun:funs) bkf offset = do 
                                                 iops <- subtractIOPairsBKmFME fun bkf offset
                                                 iopss <- subtractIOPairsFromIOPairsBKmFME addendum funs bkf (offset+addendum) -- iopsは，subfunctionが複数あって，それらsubfunctionsのそれぞれに関してIOPair1個ずつに過ぎない．
                                                 return (iops:iopss)
-- Applying substitutions to funs is not currently necessary (because funs does not include existential variables), but that will be useful in future versions which fill gaps of input examples.
                              
                                
                                
subtractIOPairsBKmFME :: IOPair a -> FMExpr [IOPair a] -> Int -> [] [IOPair a] -- 返り値の[IOPair a]は各引数に対応
subtractIOPairsBKmFME tgtiop bkfme offset = do 
                                visbkis <- unifyingIOPairs (output tgtiop) bkfme offset
                                return [ tgtiop{output=o} | o <- visbkis ]


unifyingIOPairs :: Expr a -> FMExpr [IOPair a] -> Int -> [] [Expr a]
unifyingIOPairs e fme 0      = [ inputs iop | (iops, _) <- unifyFME e fme, iop <- iops ]
unifyingIOPairs e fme offset = [ map (mapE (offset+) . apfresh s) $ inputs iop | (iops, s) <- unifyFME e fme, iop <- iops ]
