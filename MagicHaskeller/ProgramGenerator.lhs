-- 
-- (c) Susumu Katayama
--

\begin{code}
{-# OPTIONS -cpp #-}

module MagicHaskeller.ProgramGenerator where
import MagicHaskeller.Types
import MagicHaskeller.TyConLib
import Control.Monad
import Data.Monoid
import MagicHaskeller.CoreLang
import Control.Monad.Search.Combinatorial
import MagicHaskeller.PriorSubsts
import Data.List(partition, sortBy, genericLength)
import Data.Ix(inRange)

import MagicHaskeller.Instantiate

import MagicHaskeller.Expression

import MagicHaskeller.T10
import qualified Data.Map as Map

import Debug.Trace

import Data.Monoid
import System.Random

import MagicHaskeller.MyDynamic

import qualified MagicHaskeller.PolyDynamic as PD

import MagicHaskeller.Options

#if __GLASGOW_HASKELL__ >= 710
import Prelude hiding ((<$>))
#endif

-- replacement of LISTENER. Now replaced further with |guess|
-- listen = False

-- | annotated 'Typed [CoreExpr]'
type Prim = (Int, Int, Type, TyVar, Typed [CoreExpr])

class WithCommon a where
    extractCommon :: a -> Common

-- | ProgramGenerator is a generalization of the old @Memo@ type. 
class WithCommon a => ProgramGenerator a where
    -- | |mkTrie| creates the generator with the default parameters.
    mkTrie :: Common -> [Typed [CoreExpr]] -> [[Typed [CoreExpr]]] -> a
    mkTrie cmn c t = mkTrieOpt cmn c t t
    mkTrieOpt :: Common -> [Typed [CoreExpr]] -> [[Typed [CoreExpr]]] -> [[Typed [CoreExpr]]] -> a
    mkTrieOpt cmn c _ t = mkTrie cmn c t
                         -- error "This program generator does not take an optional primitive set."
    matchingPrograms, matchingProgramsWOAbsents, unifyingPrograms :: Search m => Type -> a -> m AnnExpr
    matchingPrograms ty memodeb = unifyingPrograms (quantify ty) memodeb
    matchingProgramsWOAbsents ty memodeb = mapDepth (filter (not . isAbsent (getArity ty) . toCE)) $ matchingPrograms ty memodeb
class WithCommon a => ProgramGeneratorIO a where
    -- | |mkTrie| creates the generator with the default parameters.
    mkTrieIO :: Common -> [Typed [CoreExpr]] -> [[Typed [CoreExpr]]] -> IO a
    mkTrieIO cmn c t = mkTrieOptIO cmn c t t
    mkTrieOptIO :: Common -> [Typed [CoreExpr]] -> [[Typed [CoreExpr]]] -> [[Typed [CoreExpr]]] -> IO a
    mkTrieOptIO cmn c _ t = mkTrieIO cmn c t
                         -- error "This program generator does not take an optional primitive set."
    -- | Use memoization requiring IO
    matchingProgramsIO, unifyingProgramsIO :: Type -> a -> RecompT IO AnnExpr -- Should I define SearchT?
    matchingProgramsIO ty memodeb = unifyingProgramsIO (quantify ty) memodeb
    -- Another option might be to create @newtype MemoToFile = NT (RecompT (StateT Params IO))@, and define @instance Search MemoToFile@. One drawback of this approach is that @Params@ is separated from @Options@.  
extractTCL :: WithCommon a => a -> TyConLib
extractTCL = tcl . extractCommon
extractVL :: WithCommon a => a -> VarLib
extractVL = vl . extractCommon
extractRTrie :: WithCommon a => a -> RTrie
extractRTrie = rt . extractCommon
reducer :: Common -> CoreExpr -> Dynamic
reducer cmn = execute (opt cmn) (vl cmn)

data Common = Cmn {opt :: Opt (), tcl :: TyConLib, vl :: VarLib, pvl :: VarLib, vpl :: VarPriorityLib, rt :: RTrie}

mkCommon :: Options -> [Primitive] -> [Primitive] -> [Int] -> Common
mkCommon opts totals partials priorities
    = let cmn = initCommon opts totals in
      updateCommon (map (primitiveToDynamic $ tcl cmn) totals) (map (primitiveToDynamic $ tcl cmn) partials) priorities cmn
initCommon :: Options -> [Primitive] -> Common
initCommon opts totals = let
                           tyconlib = primitivesToTCL totals
                           optunit  = forget opts
                         in Cmn {opt = optunit, tcl = tyconlib, rt = mkRandTrie (nrands opts) tyconlib (stdgen opts)}
-- | 'updateCommon' can be used for incremetal learning
updateCommon :: [PD.Dynamic] -> [PD.Dynamic] -> [Int] -> Common -> Common
updateCommon totals partials priorities cmn = cmn{vl = dynamicsToVL totals, pvl = dynamicsToVL partials, vpl = prioritiesToVPL priorities}

-- | options for limiting the hypothesis space.
type Options = Opt [[Primitive]]

retsTVar (_, _, TV tv, _, _) = True
retsTVar _                   = False

annotateTCEs :: Typed [CoreExpr] -> Prim
annotateTCEs tx@(_:::t) = let (numcs, arity, retty) = getAritiesRet t
                          in (numcs, arity, retty, maxVarID t + 1, tx) -- arity is the shorter arity that does not count contexts.

splitPrims :: [Typed [CoreExpr]] -> ([Prim],[Prim])
splitPrims = partition retsTVar . map annotateTCEs

splitPrimss :: [[Typed [CoreExpr]]] -> ([[Prim]],[[Prim]])
splitPrimss = unzip . map splitPrims

{-
splitPrimss :: Search m => [[Typed [CoreExpr]]] -> (m Prim, m Prim)
splitPrimss pss = case unzip $ map splitPrims pss of (pssf, psss) -> (fromMx $ Mx pssf, fromMx $ Mx psss)
-}

mapSum :: (MonadPlus m, Delay m) => (a -> m b) -> [[a]] -> m b
mapSum f = foldr (\xs y -> msum (map f xs) `mplus` delay y) mzero 


-- availにしろTypeにしろapplyされている．
-- だからこそ，runAnotherPS的にemptySubstに対して実行した方が効率的なはず？ でも，Substitutionってそんなにでかくならなかったのでは？FiniteMapでもassoc listでも変わらなかった気が．


applyDo :: (Functor m, Monad m) => ([Type] -> Type -> PriorSubsts m a) -> [Type] -> Type -> PriorSubsts m a
applyDo fun avail ty = do subst <- getSubst
                          fun (map (apply subst) avail) (apply subst ty)

wind :: (a->a) -> ([Type] -> Type -> a) -> [Type] -> Type -> a
wind g f avail (t0 :-> t1) = g $ wind g f (t0 : avail) t1
wind _ f avail reqret      = f avail reqret

wind_ :: ([Type] -> Type -> a) -> [Type] -> Type -> a
wind_ = wind id


{-# SPECIALIZE fromAssumptions :: (Search m) => Common -> Int -> (Type -> PriorSubsts m [CoreExpr]) -> (Type -> Type -> PriorSubsts m ()) -> Type -> [Type] -> PriorSubsts m [CoreExpr] #-}
fromAssumptions :: (Search m, Expression e) => Common -> Int -> (Type -> PriorSubsts m [e]) -> (Type -> Type -> PriorSubsts m ()) -> Type -> [Type] -> PriorSubsts m [e]
fromAssumptions cmn lenavails behalf mps reqret avail = msum $ map (retMono cmn lenavails behalf (flip mps reqret)) (fromAvail avail)

retMono :: (Search m, Expression e) => Common -> Int -> (Type -> PriorSubsts m [e]) -> (Type -> PriorSubsts m ()) -> (Int8, (Int,[Type],Type)) -> PriorSubsts m [e]
retMono cmn lenavails behalf tok fromBlah
                  = do let (n, (arity,args,retty)) = fromBlah
                       tok retty
                       convertPS (ndelay $ fromIntegral arity) $
                              fap behalf args (map (mkHead (reducer cmn) lenavails 0 arity) [X n])
fromAvail :: [Type] -> [(Int8, (Int,[Type],Type))]
fromAvail = zipWith (\ n t -> (n, revSplitArgs t)) [0..]


-- ConstrLではmatchではダメ．理由はDec. 2, 2007のnotesを参照．
mguAssumptions :: (Functor m, MonadPlus m) => Type -> [Type] -> PriorSubsts m [CoreExpr]
mguAssumptions  patty assumptions = applyDo mguAssumptions' assumptions patty
mguAssumptions' assumptions patty = msum $ zipWith (\n t -> mguPS patty t >> return [X n]) [0..] assumptions

{-# SPECIALIZE matchAssumptions :: (Functor m, MonadPlus m) => Common -> Int -> Type -> [Type] -> PriorSubsts m [CoreExpr] #-}
matchAssumptions :: (Functor m, MonadPlus m, Expression e) => Common -> Int -> Type -> [Type] -> PriorSubsts m [e]
matchAssumptions cmn lenavails reqty assumptions
    = do s <- getSubst
         let newty = apply s reqty
             (numcxts, arity) = getArities newty
         msum $ zipWith (\n t -> matchPS newty t >> return [mkHead (reducer cmn) lenavails numcxts arity (X n)]) [0..] assumptions
-- match の場合，通常はreqtyの方だけapply substすればよい．

-- not sure if this is more efficient than doing mguAssumptions and returning ().
mguAssumptions_ :: (Functor m, MonadPlus m) => Type -> [Type] -> PriorSubsts m ()
mguAssumptions_  patty assumptions = applyDo mguAssumptions_' assumptions patty
mguAssumptions_' assumptions patty = msum $ map (mguPS patty) assumptions


{-# SPECIALIZE retPrimMono ::  (Search m) => Common -> Int -> (Type -> PriorSubsts m [CoreExpr]) -> (Type -> PriorSubsts m [CoreExpr]) -> (Type -> PriorSubsts m [CoreExpr]) -> (Type -> Type -> PriorSubsts m ()) -> Type -> Prim -> PriorSubsts m [CoreExpr] #-}
retPrimMono :: (Search m, Expression e) => Common -> Int -> (Type -> PriorSubsts m [e]) -> (Type -> PriorSubsts m [e]) -> (Type -> PriorSubsts m [e]) -> (Type -> Type -> PriorSubsts m ()) -> Type -> Prim -> PriorSubsts m [e]
retPrimMono cmn lenavails clbehalf lltbehalf behalf mps reqret (numcxts, arity, retty, numtvs, xs:::ty)
                                              = do tvid <- reserveTVars numtvs
                                                   mps (mapTV (tvid+) retty) reqret
                                                   convertPS (ndelay $ fromIntegral arity) $
                                                             funApSub clbehalf lltbehalf behalf (mapTV (tvid+) ty) (map (mkHead (reducer cmn) lenavails numcxts arity) xs)
funApSub :: (Search m, Expression e) => (Type -> PriorSubsts m [e]) -> (Type -> PriorSubsts m [e]) -> (Type -> PriorSubsts m [e]) -> Type -> [e] -> PriorSubsts m [e]
funApSub = funApSubOp (<$>)
funApSubOp op clbehalf lltbehalf behalf = faso
    where faso (t:=>ts) funs
              = do args <- clbehalf t
                   faso ts (liftM2 op funs args)
          faso (t:> ts) funs
              = do args <- lltbehalf t
                   faso ts (liftM2 op funs args)
          -- original. 
          faso (t:->ts) funs
              = do args <- behalf t
                   faso ts (liftM2 op funs args)
          faso _        funs = return funs
-- originalでrevGetArgs経由にすると，foldMを使った場合と同じ効率になる．
{-
funApSub behalf t funs = fap behalf (revGetArgs t) funs
revGetArgs (t:->u) = t : revGetArgs u
revGetArgs _       = []
-}
{-
fap behalf (t:ts) funs = do args <- behalf t
                            fap behalf ts (liftM2 (<$>) funs args)
fap _      _      funs = return funs
-}
{- mapMを使う 一番遅い．
fap behalf ts funs = do args <- mapM behalf ts
                        return (foldl (liftM2 (<$>)) funs args)
-}
 -- foldMを使う．なぜかこれが一番速い
fap behalf ts funs = foldM (\fs t -> do args <- behalf t
                                        return $ liftM2 (<$>) fs args)
                           funs
                           ts

-- fap behalf ts funs = mapAndFoldM (liftM2 (<$>)) funs behalf ts
mapAndFoldM op n f []     = return n
mapAndFoldM op n f (x:xs) = do y <- f x
                               mapAndFoldM op (n `op` y) f xs



{-# SPECIALIZE retGen :: (Search m) => Common -> Int -> (Type -> Type -> [CoreExpr] -> [CoreExpr]) -> (Type -> PriorSubsts m [CoreExpr]) -> (Type -> PriorSubsts m [CoreExpr]) -> (Type -> PriorSubsts m [CoreExpr]) -> Type -> Prim -> PriorSubsts m [CoreExpr] #-}
retGen, retGenOrd, retGenTV1
    :: (Search m, Expression e) => Common -> Int -> (Type -> Type -> [e] -> [e]) -> (Type -> PriorSubsts m [e]) -> (Type -> PriorSubsts m [e]) -> (Type -> PriorSubsts m [e]) -> Type -> Prim -> PriorSubsts m [e]
retGen cmn lenavails fe clbehalf lltbehalf behalf = retGen' (funApSub clbehalf lltbehalf behalf) cmn lenavails fe clbehalf lltbehalf behalf
retGen' fas cmn lenavails fe clbehalf lltbehalf behalf reqret (numcxts, arity, _retty, numtvs, xs:::ty)
                                          = convertPS (ndelay $ fromIntegral arity) $
                                            do tvid <- reserveTVars numtvs -- この（最初の）IDそのもの（つまり返り値のtvID）はすぐに使われなくなる
                                               -- let typ = apply (unitSubst tvid reqret) (mapTV (tvid+) ty) -- mapTVとapplyはhylo-fusionできるはずだが，勝手にされる？
                                               --                                                              -- unitSubstをinlineにしないと駄目か
                                               a <- mkSubsts (tvndelay $ opt cmn) tvid reqret
                                               exprs <- funApSub clbehalf lltbehalf behalf (mapTV (tvid+) ty) (map (mkHead (reducer cmn) lenavails numcxts (arity+a)) xs)
                                               gentvar <- applyPS (TV tvid)
                                               guard (orderedAndUsedArgs gentvar) -- この辺のcheckをTVnに入る前の早い段階にやるのは1つの考え方だが，TVn中にreplaceされたりはしないのか?
                                               fas gentvar (fe gentvar ty exprs)
-- retGenOrd can be used instead of retGen, when not reorganizing.
retGenOrd cmn lenavails fe clbehalf lltbehalf behalf = retGen' (funApSub'' False) cmn lenavails fe clbehalf lltbehalf behalf
    where
--                    funApSub'' filtexp (TV _ :-> _)     funs = mzero -- mkSubstsで導入されたtyvarsが使われていないケース．replaceされた結果TVってケースはとりあえず無視....
                    funApSub'' filtexp (t:->ts@(u:->_)) funs
--                        | t > u     = mzero
                        | otherwise = do args  <- behalf t
                                         funApSub'' (t==u) ts (if filtexp then [ f <$> e | f <- funs, e <- args, let _:$d = toCE f, d <= toCE e ]
                                                                         else liftM2 (<$>) funs args)
-- てゆーかtとuが同じならばもっといろんなことができそう．
                    funApSub'' filtexp (t:->ts) funs
                                    = do args  <- behalf t
                                         return (if filtexp then [ f <$> e | f <- funs, e <- args, let _:$d = toCE f, d <= toCE e]
                                                            else liftM2 (<$>) funs args)
                    funApSub'' _fe _t funs = return funs

orderedAndUsedArgs (TV _ :-> _) = False -- mkSubstsで導入されたtyvarsが使われていないケース．replaceされた結果TVってケースはとりあえず無視....
orderedAndUsedArgs (t:->ts@(u:->_)) | t > u     = False
                             | otherwise = orderedAndUsedArgs ts
orderedAndUsedArgs _ = True

usedArg n (TV m :-> _) = n /= m
usedArg _ _            = True

retGenTV1 cmn lenavails fe clbehalf lltbehalf behalf reqret (numcxts, arity, _retty, numtvs, xs:::ty)
                                          = convertPS (ndelay $ fromIntegral arity) $
                                            do tvid <- reserveTVars numtvs -- この（最初の）IDそのもの（つまり返り値のtvID）はすぐに使われなくなる
                                               -- let typ = apply (unitSubst tvid reqret) (mapTV (tvid+) ty) -- mapTVとapplyはhylo-fusionできるはずだが，勝手にされる？
                                               --                                                              -- unitSubstをinlineにしないと駄目か
                                               a <- mkSubst (tvndelay $ opt cmn) tvid reqret
                                               exprs <- funApSub clbehalf lltbehalf behalf (mapTV (tvid+) ty) (map (mkHead (reducer cmn) lenavails numcxts (arity+a)) xs)
                                               gentvar <- applyPS (TV tvid)
                                               guard (usedArg (tvid+1) gentvar)
                                               funApSub clbehalf lltbehalf behalf gentvar (fe gentvar ty exprs)

retGenTV0 cmn lenavails fe clbehalf lltbehalf behalf reqret (numcxts, arity, _retty, numtvs, xs:::ty)
                                          = convertPS (ndelay $ fromIntegral arity) $
                                            do tvid <- reserveTVars numtvs -- この（最初の）IDそのもの（つまり返り値のtvID）はすぐに使われなくなる
                                               -- let typ = apply (unitSubst tvid reqret) (mapTV (tvid+) ty) -- mapTVとapplyはhylo-fusionできるはずだが，勝手にされる？
                                               --                                                              -- unitSubstをinlineにしないと駄目か
                                               updatePS (unitSubst tvid reqret)
                                               exprs <- funApSub clbehalf lltbehalf behalf (mapTV (tvid+) ty) (map (mkHead (reducer cmn) lenavails numcxts arity) xs)
                                               gentvar <- applyPS (TV tvid)
                                               return $ fe gentvar ty exprs

filtExprs :: Expression e => Bool -> Type -> Type -> [e] -> [e]
filtExprs g a b | g         = filterExprs a b
                | otherwise = id

-- LISTENERかDESTRUCTIVEがdefineされているときの，各ケースのoptimization
filterExprs :: Expression e => Type -> Type -> [e] -> [e]
filterExprs gentvar ty = filter (cond . getArgExprs . toCE)
    where cond es = case gentvar of _:->_ -> not (retSameVal ty es) && not (includesStrictArg es) && anyRec ty es && not (constEq ty es)
                                    _     -> not (retSameVal ty es) && not (includesStrictArg es)

getArgExprs e = gae e []
gae (f:$e) es = gae f (e:es)
gae _      es = es

-- forall w x y. list_para w (\_ -> x) (\c d e f -> e (blah)) = \_ -> x 的なもの.
constEq (t:->u) (e@(Lambda d):es) | returnsAtoA t = recHead t e && constEq u es
                                  | otherwise     = not (isUsed 0 d) && ceq e u es
constEq (t:->u) (_:_)             = False -- not case/cata/para, so should pass.
constEq (_:> u) (_           :es) = constEq u es
constEq _       []                = True
ceq d (t:->u) (e@(Lambda _):es) | returnsAtoA t = recHead t e && ceq d u es
                                | otherwise     = d == e      && ceq d u es
ceq d (t:->u) (_:_)             = False -- not case/cata/para, so should pass.
ceq d (_:> u) (_           :es) = ceq d u es
ceq _ _       []                = True

recHead (t:->u@(_:->_))     (Lambda e)                   = recHead u e
recHead (TV tv0 :-> TV tv1) (Lambda (Lambda (X 1 :$ _))) = tv0 == 0 && tv1 == 0   -- 複数recがある場合，最後の奴だけrecとして認めることになっちゃうので，最適化の意味ではちょっとだけザル
recHead _u                  _e                           = False


-- windUntilRecってのがあれば共有可能 (CPSな感じ)



retSameVal (_:>u)  (_:es) = retSameVal u es
retSameVal (t:->u) (e:es) = (returnsId t e && rsv u es) || rsv' (retVal t e) u es
retSameVal _       _      = False
rsv (_:>u)  (_:es) = rsv u es
rsv (t:->u) (e:es) = (returnsId t e && rsv u es) || rsv' (retVal t e) u es
rsv _       _      = True
rsv' rve (_:>u)  (_:es) = rsv' rve u es
rsv' rve (t:->u) (e:es) = (returnsId t e || retVal t e == rve) && rsv' rve u es
rsv' _   _       _      = True



-- returnsAtoA is True when the type returns a->a, where the tvID of a is 0.
returnsAtoA (TV tv0 :-> TV tv1) = tv0 == 0 && tv1 == 0
returnsAtoA (t      :-> u)      = returnsAtoA u
returnsAtoA _                   = False

-- 同時にreturnsAtoAもチェックしてるのもポイント．
returnsId (t:->u@(_:->_))     (Lambda e)     = returnsId u e
returnsId (TV tv0 :-> TV tv1) e              = tv0 == 0 && tv1 == 0 && isId e
returnsId _u                  _e             = False -- ここで(_u,_e)が(TV _, Lambda _)ってこともあり得る．_uがt:->uなのに_eがLambdaでないってのはありえないか．
{- これだと，結果として最後の引数と返り値の型が同じだけどもともとのPrim上では違う，という可能性があり得る．
returnsId (t:->u) (Lambda e) = returnsId u e
returnsId (_:->_) _          = error "returnsId: impossible"
returnsId (TV tv) (X 0)      = tvID tv == 0
returnsId _u      _e         = False -- ここで(_u,_e)が(TV _, Lambda _)ってこともあり得る．_uがt:->uなのに_eがLambdaでないってのはありえないか．
-}

-- isId checks if the argument is eta-equivalent to id, i.e. (Lambda (X 0)). Note that expressions are eta-expanded.
-- for example, isId (Lambda (Lambda (Lambda ((X 2 :$ X 1) :$ X 0)))) is True.
-- There is no need to tell that isId (Lambda ((Lambda (X 0)) :$ X 0)) is True, because this beta-reducible expression would not be synthesized.
isId e = isId' 0 e
isId' n (Lambda e) = isId' (n+1) e
isId' n e          = isId'' n 0 e
isId'' n m (e :$ X i) = i==m && isId'' n (m+1) e
isId'' n m (X i)      = i==m && n == m+1
isId'' _ _ _          = False


retVal t e = rv t 0 e
rv (_:->t) n (Lambda e) = rv t (n+1) e
rv (_:->_) _ _          = error "rv: impossible"
rv _       n e          = mapsub n e

-- mapsub n ~= gmap (subtract n), but I will have to rewrite the definition of CoreExpr to prevent gmap from updating other Ints.
mapsub n (X m)      = X (m-n)
mapsub n (a :$ b)   = mapsub n a :$ mapsub n b
mapsub n (Lambda e) = Lambda (mapsub n e)
mapsub n e          = e

isConstrExpr (X _)      = False
isConstrExpr (Lambda _) = False
isConstrExpr (Context _) = False
isConstrExpr (f :$ _)   = isConstrExpr f
isConstrExpr (Primitive _) = False
isConstrExpr (PrimCon _) = True

isClosed = isClosed' 0
isClosed' dep (X n)      = n < dep
isClosed' dep (Lambda e) = isClosed' (dep+1) e
isClosed' dep (f :$ e)   = isClosed' dep f && isClosed' dep e
isClosed' _   _          = True


-- 効率のことを考えると，strictArgは最初に持ってくることになる．（将来的には，最初になるように並べ変えてgenerateし，終ってから元に戻すことになる）
-- （少なくとも，最初にexpandする．制限が多いので分岐しにくいから．）
includesStrictArg (X n : es) = any (isUsed n) es
-- caseのデータなのでLambdaは来ない．あと，Quantifyは最初からexcludeされている．というわけで，ここには実際には((_:$_):_)か[]しか来ない．
-- 関数適用の場合はめんどくさいしチェックもコストがかかるので素通しにする．
includesStrictArg _        = False
{-
includesStrictArg [] = False
includesStrictArg es = case last es of X n  -> any (isUsed n) (init es)
                                       _:$_ -> False -- 関数適用の場合はめんどくさいしチェックもコストがかかるので素通しにする．
-- caseのデータなのでLambdaは来ない．あと，Quantifyは最初からexcludeされている．
-}

anyRec (_:>t)  (_:es) = anyRec t es
anyRec (t:->u) (e:es) = -- trace ("ar: t = "++show t++" and u = "++ show u) $
                    recursive t e || anyRec u es
anyRec (_:->_) _ = error "hoge"
anyRec _       []     = False
{- typeの方をひっくり返す場合
anyRec (hd:tl@(_:_)) (f:$e) = recursive hd e || anyRec tl f
anyRec _             _      = False
-}

recursive (t:->u@(_:->_))     (Lambda e) = recursive u e
recursive (TV tv0 :-> TV tv1) (Lambda e) = tv0 == 0 && tv1 == 0 && isUsed 0 e && not (constRec 0 e) -- これだと，recursiveのやつとnot const.recのやつが同じでなくてはならないが，その条件は必要か？ （listでやっている限りは気にしなくていいって話もあるけど）
recursive _                   _          = False

constRec dep (Lambda e) = constRec (dep+1) e
constRec dep (X n :$ e) | n == dep = not (belowIsUsed n e)
constRec _   _          = False
belowIsUsed dep (X n)      = dep > n
belowIsUsed dep (Lambda e) = belowIsUsed (dep+1) e
belowIsUsed dep (f :$ e)   = belowIsUsed dep f || belowIsUsed dep e
belowIsUsed _   _          = False

{-
lastarg (_:->t@(_:->_)) = let Just (la,n) = lastarg t in Just (la, n+1)
lastarg (t:->_)         = Just (t, 1)
lastarg _               = Nothing

isRec n expr = isUsed (-n) expr
-}
isUsed dep (X n)      = dep==n
isUsed dep (Lambda e) = isUsed (dep+1) e
isUsed dep (f :$ e)   = isUsed dep f || isUsed dep e
isUsed _   _          = False


mkSubsts :: Search m => Int -> TyVar -> Type -> PriorSubsts m Int
mkSubsts n tvid reqret  = base `mplus` ndelayPS n recurse
    where base    = do updatePS (unitSubst tvid reqret) -- ここをsetSubstにして，mguProgsを呼び出すたびに結果のSubstをplusSubstするようにした方が，無駄にSubstが大きくならない．
                                                     -- めんどくさいからこうしてるけど，もしlookupSubstが時間を食い過ぎるなら考える．
                       return 0
          recurse = do v <- newTVar
                       arity <- mkSubsts n tvid (TV v :-> reqret)
                       return (arity+1)

mkSubst :: Search m => Int -> TyVar -> Type -> PriorSubsts m Int
mkSubst n tvid reqret  = base `mplus` ndelayPS n first
    where base    = do updatePS (unitSubst tvid reqret) -- ここをsetSubstにして，mguProgsを呼び出すたびに結果のSubstをplusSubstするようにした方が，無駄にSubstが大きくならない．
                                                     -- めんどくさいからこうしてるけど，もしlookupSubstが時間を食い過ぎるなら考える．
                       return 0
          first   = do v <- newTVar
                       updatePS (unitSubst tvid (TV v :-> reqret))
                       return 1
mkRetty t = (getRet t, t)
-- getRet (t0:->t1) = getRet t1
-- getRet t         = t

-- MemoStingyとかでは
-- reorganize_ :: ([Type] -> PriorSubsts BF ()) -> [Type] -> PriorSubsts BF ()
-- として使われるのだが，G4ipでは下記の型じゃないと．
reorganizer_ :: ([Type] -> a) -> [Type] -> a
reorganizer_ fun avail = fun $ uniqSort avail


-- moved from T10.hs to make T10 independent of Types

-- hit decides whether to memoize or not.
hit :: Type -> [Type] -> Bool
-- hit ty tys = True -- always memo
-- hit ty tys = areMono (ty:tys) -- memo only tycons ... Substいらないし，availsToReplacerなしで（newavailなしで）判定できる．あとそもそも，MapTypeにtvやevalがいらないし，encode/decodeもいらなくなる．ただ，monomorphicしからやないのって，ちょっと少な過ぎる気もする．
-- hit ty tys = sum (map size (ty:tys)) < 7
-- hit ty tys = sum (map size (ty:tys)) < 2
-- hit ty tys = sum (map size (ty:tys)) < 5
-- hit ty tys = sum (map size (ty:tys)) < 12
hit ty tys = sum (map size (ty:tys)) < 10


-- areMono = all (null.tyvars)

combs 0 xs = [[]]
combs n xs = []  : [ y:zs | y:ys <- tails xs, zs <- combs (n-1) ys ]
tails []        = []
tails xs@(_:ys) = xs : tails ys


\end{code}

