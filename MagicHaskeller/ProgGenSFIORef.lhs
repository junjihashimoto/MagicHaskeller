-- 
-- (c) Susumu Katayama
--

\begin{code}
{-# LANGUAGE CPP, RelaxedPolyRec, FlexibleInstances #-}
module MagicHaskeller.ProgGenSFIORef(ProgGenSFIORef, PGSFIOR) where
import MagicHaskeller.Types
import MagicHaskeller.TyConLib
import Control.Monad
import MagicHaskeller.CoreLang
import Control.Monad.Search.Combinatorial
import MagicHaskeller.PriorSubsts
import Data.List(partition, sortBy, sort, nub, (\\))
import Data.Ix(inRange)

import MagicHaskeller.ClassifyDM

import MagicHaskeller.Instantiate

import MagicHaskeller.ProgramGenerator
import MagicHaskeller.ProgGen(mkCL, ClassLib(..), mguPrograms)
import MagicHaskeller.ProgGenSF(funApSub_, funApSub_spec, lookupNormalized, tokoro10fst)
import MagicHaskeller.Options(Opt(..))

import MagicHaskeller.Expression

import MagicHaskeller.MemoToFiles hiding (freezePS, fps, memoRTIO)

import MagicHaskeller.T10(mergesortWithBy, diffSortedBy)

import qualified Data.Map as M

import MagicHaskeller.DebMT

import MagicHaskeller.FMType
import Data.IORef
import Data.Array
import Data.Ix

import MagicHaskeller.ShortString(readBriefly, showBriefly)
import System.Directory(doesFileExist, createDirectoryIfMissing)

import Debug.Trace
-- trace str = id

reorganize_ = reorganizer_
-- reorganize_ = id

reorganizerId' :: (Functor m, Expression e) => ([Type] -> m e) -> [Type] -> m e
reorganizerId' = reorganizeId'
--reorganizerId' = id

classify = True
traceExpTy _ = id
-- traceExpTy fty = trace ("lookupexp "++ show fty)
traceTy _    = id
-- traceTy fty = trace ("lookup "++ show fty)

-- Memoization table, created from primitive components
type ProgGenSFIORef = PGSFIOR CoreExpr
data PGSFIOR e = PGSFIOR (ExpTrie e) (MemoDeb e) -- internal data representation.
-- ^ Program generator with synergetic filtration.
--   This program generator employs filtration by random testing, and rarely generate semantically equivalent expressions more than once, while different expressions will eventually appear (for most of the types, represented with Prelude types, whose arguments are instance of Arbitrary and which return instance of Ord).
--   The idea is to apply random numbers to the generated expressions, compute the quotient set of the resulting values at each depth of the search tree, and adopt the complete system of representatives for the depth and push the remaining expressions to one step deeper in the search tree.
--   (Thus, adoption of expressions that may be equivalent to another already-generated-expression will be postponed until their \"uniqueness\" is proved.)
--   As a result, (unlike "ProgGen",) expressions with size N may not appear at depth N but some deeper place.
--
--   "ProgGenSF" is more efficient along with a middle-sized primitive set (like @reallyall@ found in LibTH.hs),
--   but is slower than "ProgGen" for a small-sized one.
--
--   Also note that "ProgGenSF" depends on hard use of unsafe* stuff, so if there is a bug, it may segfault....

type ExpTrie  e = IORef (FMType (Array Int [e]))
-- type ExpTrie  e = MapType (ExpMatrix e) -- PGSF, PGSFIOだとこっちだった．

type TypeTrie = MapType (Matrix (Type, Subst, TyVar))

filtBFm cmn ty | classify  = inconsistentDBTToRcT . fmap fromAnnExpr . filterDM cmn ty . fmap (toAnnExprWind (execute (opt cmn) (vl cmn)) ty)  .  mapDepthDB uniqSorter
               | otherwise = dbtToRcT . mapDepthDB uniqSorter

lmtty mt fty = traceTy fty $
               lookupMT mt fty

--memocond i = 3<i
-- memocond i = i<10
memocond i = True

-- memocond ty = size ty < 10 -- popArgs avail tしてからやるのはちょっと無駄．と思ったけど，実際は関係ないみたい．
-- memocond av ty = size ty + sum (map size av) < 10


instance ProgramGeneratorIO (PGSFIOR CoreExpr) where
    mkTrieOptIO cmn classes tcesopt tces = do expTrie <- newIORef EmptyFMT
                                              return $ PGSFIOR expTrie (mkTrieOptSF cmn classes tcesopt tces)
    unifyingProgramsIO ty px = catBags $ fmap (\ (es,_,_) -> map (toAnnExpr $ reducer $ extractCommon px) es) $ dbtToRcT $ unifyingPossibilitiesIO ty px
instance Expression e => WithCommon (PGSFIOR e) where
    extractCommon    (PGSFIOR _ (_,_,_,cmn))      = cmn

unifyingPossibilitiesIO ty pg = unPS (unifyableExprsIO pg [] ty) emptySubst 0


type MemoDeb e = (ClassLib e, TypeTrie, (([[Prim]],[[Prim]]),([[Prim]],[[Prim]])), Common)

mkTrieOptSF :: Common -> [Typed [CoreExpr]] -> [[Typed [CoreExpr]]] -> [[Typed [CoreExpr]]] -> MemoDeb CoreExpr
mkTrieOptSF cmn classes txsopt txs
    = let memoDeb = (mkCL cmn classes, typeTrie, (qtlopt,qtl), cmn)
          typeTrie = mkMTty (tcl cmn) (\ty -> freezePS ty (specTypes memoDeb ty))
      in memoDeb
    where qtlopt = splitPrimss txsopt
          qtl    = splitPrimss txs
-- 非効率だけど，DBoundTに矛盾があってもいいやつ．
inconsistentDBTToRcT :: (Functor m, Monad m, Ord a) => DBoundT m a -> RecompT m a
inconsistentDBTToRcT (DBT f) = RcT $ \d -> do tss <- mapM f [0..d-1]
                                              ts  <- f d
                                              return $ foldl (diffSortedBy compare) (map fst ts) (map (map fst) tss)
-- what to memoize about exptrie
computeExpTip :: PGSFIOR CoreExpr -> Type -> RecompT IO CoreExpr
computeExpTip md@(PGSFIOR _ (_,_,_,cmn)) ty = filtBFm cmn ty $ matchFunctionsIO md ty

mkMTty = mkMT
mkMTexp = mkMT

mondepth = zipDepthRc (\d xs -> trace ("depth="++show d++", and the length is "++show (length xs)) xs) -- depthと表示するなら+1するべきであった．(0から始まるので)


type BFT = Recomp
unBFM = unMx


freezePS :: Type -> PriorSubsts Recomp Type -> Matrix (Type,Subst,TyVar)
freezePS ty ps
    = let mxty = maxVarID ty
      in mapDepth tokoro10ap $ toMx $ fmap fst $ Rc $ unDB $ fromRc $ unPS ps emptySubst (mxty+1) 

tokoro10ap :: [(Type,s,i)] -> [(Type,s,i)]
tokoro10ap = M.elems . M.fromListWith const . map (\ t@(ty,_,_) -> (ty, t))




specializedTypes :: (Search m) => MemoDeb CoreExpr -> [Type] -> Type -> PriorSubsts m ([Type],Type)
specializedTypes memodeb avail t = do specializedCases memodeb avail t
                                      subst <- getSubst
                                      return (map (apply subst) avail, apply subst t)
-- specializedCases is the same as unifyableExprs, except that the latter returns PriorSubsts BF [CoreExpr], and that the latter considers memodepth.
specializedCases, specCases, specCases' :: (Search m) => MemoDeb CoreExpr -> [Type] -> Type -> PriorSubsts m ()
specializedCases memodeb = applyDo (specCases memodeb)
specCases memodeb = wind_ (\avail reqret -> reorganize_ (\newavail -> uniExprs_ memodeb newavail reqret) avail)
{- どっちがわかりやすいかは不明
specCases memodeb avail (t0:->t1) = specCases memodeb (t0 : avail) t1
specCases memodeb avail reqret = reorganize_ (\newavail -> uniExprs_ memodeb newavail reqret) avail
-}





uniExprs_ :: (Search m) => MemoDeb CoreExpr -> [Type] -> Type -> PriorSubsts m ()
uniExprs_ memodeb avail t
    = convertPS fromRc $ psListToPSRecomp lfp
    where lfp depth
              | memocond depth     = lookupUniExprs memodeb avail t depth >> return ()
              | otherwise          = makeUniExprs memodeb avail t depth >> return ()

lookupUniExprs :: Expression e => MemoDeb e -> [Type] -> Type -> Int -> PriorSubsts [] Type
lookupUniExprs memodeb@(_,mt,_,_) avail t depth
    = lookupNormalized  (\tn -> unMx (lmtty mt tn) !! depth) avail t

makeUniExprs :: MemoDeb CoreExpr -> [Type] -> Type -> Int -> PriorSubsts [] Type
makeUniExprs memodeb avail t depth
    = convertPS tokoro10fst $
                do psRecompToPSList (reorganize_ (\av -> specCases' memodeb av t) avail) depth
                   sub   <- getSubst
                   return $ quantify (apply sub $ popArgs avail t)


-- entry point for memoization
specTypes :: (Search m) => MemoDeb CoreExpr -> Type -> PriorSubsts m Type
specTypes memodeb ty
                           = do let (avail,t) = splitArgs ty
                                reorganize_ (\av -> specCases' memodeb av t) avail
-- quantifyはmemo先で既にやられているので不要
                                typ <- applyPS ty
                                return (normalize typ)


-- specCases' trie prims@(primgen,primmono) avail reqret = msum (map (retMono.fromPrim) primmono) `mplus` msum (map retMono fromAvail ++ map retGen primgen)
specCases' memodeb@(CL classLib, ttrie, (prims@(primgen,primmono),_),cmn) avail reqret
 = mapSum retPrimMono primmono `mplus` msum (map retMono avail) `mplus` mapSum retGen primgen
    where fas | constrL $ opt cmn = funApSub_ clbehalf lltbehalf behalf
              | otherwise         = funApSub_spec      clbehalf behalf
              where behalf    = specializedCases memodeb avail
                    lltbehalf = flip mguAssumptions_ avail
                    clbehalf  ty = mguPrograms classLib [] ty >> return ()
          -- retPrimMono :: (Int, Type, Int, Typed [CoreExpr]) -> PriorSubsts BFT ()
          retPrimMono (_, arity, retty, numtvs, _xs:::ty)
                                              = napply arity delayPS $
                                                do tvid <- reserveTVars numtvs
                                                   mguPS reqret (mapTV (tvid+) retty)
                                                   fas (mapTV (tvid+) ty)
          -- retMono :: Type -> PriorSubsts BFT ()
          retMono ty = napply (getArity ty) delayPS $
                       do mguPS reqret (getRet ty)
                          fas ty
          -- retGen :: (Int, Type, Int, Typed [CoreExpr]) -> PriorSubsts BFT ()
          retGen (_, arity, _r, numtvs, _s:::ty) = napply arity delayPS $
                                             do tvid <- reserveTVars numtvs -- この（最初の）IDそのもの（つまり返り値のtvID）はすぐに使われなくなる
                                               -- let typ = apply (unitSubst tvid reqret) (mapTV (tvid+) ty) -- mapTVとapplyはhylo-fusionできるはずだが，勝手にされる？
                                               --                                                              -- unitSubstをinlineにしないと駄目か
                                                mkSubsts (tvndelay $ opt cmn) tvid reqret
                                                fas (mapTV (tvid+) ty)

                                                gentvar <- applyPS (TV tvid)

                                                guard (orderedAndUsedArgs gentvar)
                                                fas gentvar

type Generator m e = PGSFIOR e -> [Type] -> Type -> PriorSubsts m [e]

unifyableExprsIO :: Generator (DBoundT IO) CoreExpr
unifyableExprsIO memodeb = applyDo (wind (fmap (map (mapCE Lambda))) (lookupNormalized (lookupTypeTrieIO memodeb)))

memocondexp _ d = 0<d -- なんか条件がProgGenSFIOでは逆になってるかも．
memodepth _ = 1


lookupTypeTrieIO :: PGSFIOR CoreExpr -> Type -> DBoundT IO ([CoreExpr], Subst, TyVar)
lookupTypeTrieIO md@(PGSFIOR _ (_, mt, _, _)) t
    = DBT $ \db -> fmap concat $ mapM (procTup md db) $ unMx (lmtty mt t) !! db
procTup :: PGSFIOR CoreExpr -> Int -> (Type, Subst, TyVar) -> IO [(([CoreExpr],Subst,TyVar),Int)]
procTup md db (ty, s, i) = mapM (\depth -> unRcT (lookupReorganizedIO md ty) depth >>= \ys -> return ((ys, s, i), db-depth)) [0..db]
{-
lookupTypeTrieRcIO :: Expression e => MemoDeb e -> Type -> RecompT IO ([e], Subst, Int)
lookupTypeTrieRcIO md@((mt,_), _, _) t
    = RcT $ \d -> mapM (procTupRc md d) $ unMx (lmtty mt t) !! d
procTupRc md d (ty, s, i) = do mx <- lmtIO md ty
                               return (unMx mx !! d, s, i)
-}

lookupReorganizedIO md typ = let (avs, retty) = splitArgs $ normalize typ
                             in reorganizerId' (\av -> lmtIO md $ popArgs av retty) avs

-- ホントはProgGenSFのmtを使ったほうが速いはず．
lmtIO :: PGSFIOR CoreExpr -> Type -> RecompT IO CoreExpr
lmtIO md@(PGSFIOR fmtref (_,_,_,cmn)) ty = memoRTIO fmtref (computeExpTip md) ty

memoRTIO :: (Expression e) => ExpTrie e -> (Type -> RecompT IO e) -> Type -> RecompT IO e
memoRTIO fmtref compute ty
    = RcT $ \depth -> if memocondexp ty depth then ensureAtHand fmtref compute ty depth 
                                           else unRcT (compute ty) depth

ensureAtHand fmtref compute ty depth
    = do fmt <- readIORef fmtref
         case lookupFMT ty fmt of
           Nothing -> makeAtHand fmtref compute ty depth
           Just ar | inRange (bounds ar) depth -> return $ ar!depth
                   | otherwise                 -> makeAtHand fmtref compute ty depth

makeAtHand fmtref compute ty depth = do result <- unRcT (compute ty) depth
                                        if memocondexp ty (depth-1) then do ensureAtHand fmtref compute ty (depth-1)
{-
                                                                            modifyIORef fmtref (fst . addToLast ty depth result)
                                                                            return result
-}
                                                                            atomicModifyIORef fmtref (addToLast ty depth result)
{-
                                                                    else do modifyIORef fmtref (fst . mkSingle ty depth result)
                                                                            return result
-}
                                                                    else atomicModifyIORef fmtref (mkSingle ty depth result)
-- exptipをlookupするときもnormalizeすべき．と思ったけど，typetipにあるtypeはnormalizeされてる．

addToLast :: Expression e => Type -> Int -> [e] -> FMType (Array Int [e]) -> (FMType (Array Int [e]), [e])
addToLast ty depth result fmt = (updateFMT upd (error "addToLast: cannot happen") ty fmt, result)
    where upd ar = array (lo,depth) ((depth,result) : assocs ar)
                   where (lo,_hi) = bounds ar
mkSingle :: Expression e => Type -> Int -> [e] -> FMType (Array Int [e]) -> (FMType (Array Int [e]), [e])
mkSingle ty depth result fmt = (updateFMT (error "mkSingle: I think this cannot happen") (array (depth,depth) [(depth,result)]) ty fmt, result)


{-
modify :: Type -> Int -> FMType (Array Int [AnnExpr]) -> (FMType (Array Int [AnnExpr]), [AnnExpr])
modify ty depth fmt
    = case lookupFMT fmt ty of
        Nothing -> do result <- compute  ってことは, IO が間に入るので, atomic ではない.

atomicかどうかは後で考える．

要は，
・該当箇所がmemo対象でない場合，computeして終了．
            memo対象の場合(X)，memoにあるなら，それを取ってきて終了．
                                     ないのであれば，{result <- compute;
                                                      該当箇所の1個浅いところがmemo対象でない場合，該当箇所のみをもつsingleton arrayを書き込んで終了(A)
                                                                               memo対象なら，{(X)を１こ浅いところで実行（結果は捨て）;
                                                                                              （１個浅いところまでのarrayができてるので，）該当箇所を末尾に加えて終了(B)}}

atomicallyにやるのは(A)と(B)だけか．atomicModifyIORef :: IORef a -> (a -> (a, b)) -> IO b
実はmemocondexpで(memodepthなしで)できそう．
関数(X)が本質的．loopするので．(X)をensureAtHandという名前に．
-}



-- entry for memoization
matchFunctionsIO :: PGSFIOR CoreExpr -> Type -> DBoundT IO CoreExpr
matchFunctionsIO memodeb ty = case splitArgs (saferQuantify ty) of (avail,t) -> matchFunsIO memodeb avail t

-- saferQuantify ty = let offset = maxVarID (unquantify ty) + 1 in quantify' $ mapTV (offset+) ty

matchFunsIO :: PGSFIOR CoreExpr -> [Type] -> Type -> DBoundT IO CoreExpr
matchFunsIO memodeb avail reqret = catBags $ runPS (matchFuns' unifyableExprsIO memodeb avail reqret)

matchFuns' :: (Search m) => Generator m CoreExpr -> Generator m CoreExpr
-- matchFuns' = generateFuns matchPS filtExprs lookupListrie -- MemoDebの型の違いでこれはうまくいかなんだ．
matchFuns' rec md@(PGSFIOR _ (CL classLib, _, (_,(primgen,primmono)),cmn)) avail reqret
    = let clbehalf  = mguPrograms classLib []
          behalf    = rec md avail
          lltbehalf = lookupListrie lenavails rec md avail -- heuristic filtration
          lenavails = length avail
--          fe :: Type -> Type -> [CoreExpr] -> [CoreExpr] -- ^ heuristic filtration
          fe        = filtExprs (guess $ opt cmn)
      in fromAssumptions cmn lenavails behalf (\a b -> guard $ a==b) reqret avail `mplus`
          mapSum (retPrimMono cmn lenavails clbehalf lltbehalf behalf matchPS reqret) primmono `mplus`
          mapSum ((    if tv0 $ opt cmn then retGenTV0 else
                        if tv1 $ opt cmn then retGenTV1 else retGenOrd) cmn lenavails fe clbehalf lltbehalf behalf reqret) primgen

lookupListrie :: (Search m, Expression e) => Int -> Generator m e -> Generator m e
lookupListrie lenavails rec memodeb@(PGSFIOR _ (_,_,_,cmn)) avail t
                                    | constrL opts = matchAssumptions cmn lenavails t avail
                                    | guess opts = do
                                       args <- rec memodeb avail t
                                       let args' = filter (not.isClosed.toCE) args
                                       when (null args') mzero
                                       return args'
                                    | otherwise = do
                                       args <- rec memodeb avail t
                                       let args' = filter (not.isConstrExpr.toCE) args
                                       when (null args') mzero
                                       return args'
    where opts = opt cmn

\end{code}
