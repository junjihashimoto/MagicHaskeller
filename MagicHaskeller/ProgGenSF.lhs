-- 
-- (c) Susumu Katayama
--

\begin{code}
{-# LANGUAGE CPP, RelaxedPolyRec, FlexibleInstances #-}
module MagicHaskeller.ProgGenSF(ProgGenSF, PGSF(..), freezePS, funApSub_, funApSub_spec, lookupNormalized, tokoro10fst, mkTrieOptSFIO) where
import MagicHaskeller.Types
import MagicHaskeller.TyConLib
import Control.Monad
import MagicHaskeller.CoreLang -- also imports unsafeShiftL/R for GHC<7.6 (which actually are shiftL/R respectively)
import Control.Monad.Search.Combinatorial
import MagicHaskeller.PriorSubsts
import Data.List(partition, sortBy, sort, nub, (\\))
import Data.Ix(inRange)

import MagicHaskeller.ClassifyDM

import MagicHaskeller.Instantiate

import MagicHaskeller.ProgramGenerator
import MagicHaskeller.ClassLib(mkCL, ClassLib(..), mguPrograms)
import MagicHaskeller.Options(Opt(..))

import MagicHaskeller.Expression

import Data.Monoid


import MagicHaskeller.T10(mergesortWithBy, diffSortedBy)

import qualified Data.Map as M

import MagicHaskeller.DebMT

import Data.Function(fix)
import System.IO(fixIO)
import System.IO.Unsafe(unsafeInterleaveIO)

import Data.Bits -- used for absence analysis
import Data.Word

import Data.Array

#if __GLASGOW_HASKELL__ >= 710
import Prelude hiding ((<$>))
#endif

import Debug.Trace
-- trace str = id

reorganize_ f av = f $ mergesortWithBy const compare av
--reorganize_' = id

--reorganizer' = reorganize'
reorganizer' = id

reorganizerId' :: (Functor m, Expression e) => ([Type] -> m e) -> [Type] -> m e
reorganizerId' = reorganizeId'
--reorganizerId' = id

classify = True
traceExpTy _ = id
-- traceExpTy fty = trace ("lookupexp "++ show fty)
traceTy _    = id
-- traceTy fty = trace ("lookup "++ show fty)

-- Memoization table, created from primitive components
--type ProgGenSF = PGSF AnnExpr
type ProgGenSF = PGSF CoreExpr -- temporarily, until reorganize for ProgGenSF is implemented.
data PGSF e = PGSF (MemoDeb e) TypeTrie (ExpTrie e) -- internal data representation.
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

type ExpTip   e = Matrix e

type ExpTrie  e = MapType (ExpTip e)
type TypeTrie   = MapType (Matrix (Type, Subst, TyVar))

lmt :: Expression e => ExpTrie e -> Type -> Matrix e
lmt mt fty = traceExpTy fty $
                                     lookupMT mt fty -- こっちだとlookup
--                                   filtBF cmn fty $ matchFunctions (maxBound', memoDeb) fty --  こっちだとrecompute

filtBF :: Expression e => Common -> Type -> Recomp e -> Matrix e
--          filtBF ty = fmap fromAnnExpr . filterBF tcl rtrie ty . fmap (toAnnExprWind (execute opt) ty) . tabulate
--filtBF cmn ty = dbToCumulativeMx . fmap fromAnnExpr . fDM cmn ty . fmap (toAnnExprWind (execute (opt cmn) (vl cmn)) ty)  .  mapDepthDB uniqSorter -- . mondepth
filtBF cmn ty | classify  = dbToCumulativeMx . fmap fromAnnExpr . fDM cmn ty . fmap (toAnnExprWind (execute (opt cmn) (vl cmn)) ty) . fromRc . mapDepth uniqSort
              | otherwise = toMx . mapDepth uniqSort
fDM = filterDM -- こっちが従来
-- fDM = filterDMlite -- depth bound(つまり，Int->[(a,Int)]における引数のInt)の代わりに，depth boundからの距離(つまり，Int->[(a,Int)]におけるInt->[(a,ここのInt)])を使ってnrndsの何番目かを決めるもの．
                      -- filterDMと違って，同じdepth boundでも違う乱数を使うので，filterList同様depthを跨いだfiltrationができず，結果はいまいち．
                      -- ただし，dynamicな関数自体をメモ化すれば，格段にメモにヒットしやすくなるはず．

filtBFIO :: Expression e => Common -> Type -> Recomp e -> IO (Matrix e)
filtBFIO cmn ty rc | classify  = dbtToCumulativeMx $ fmap fromAnnExpr $ filterDMIO cmn ty $ fmap (toAnnExprWind (execute (opt cmn) (vl cmn)) ty) $ fromRc $ mapDepth uniqSort rc
                   | otherwise = return $ toMx $ mapDepth uniqSort rc

lmtty mt fty = traceTy fty $
               lookupMT mt fty

--memocond i = 3<i
-- memocond i = i<10
memocond i = True

-- memocond ty = size ty < 10 -- popArgs avail tしてからやるのはちょっと無駄．と思ったけど，実際は関係ないみたい．
-- memocond av ty = size ty + sum (map size av) < 10


instance (Expression e) => ProgramGenerator (PGSF e) where
    mkTrieOpt = mkTrieOptSF
    matchingProgramsWOAbsents ty (PGSF (_,_,cmn) _ etrie)    = fromMx $ zipDepthMx (\i es -> if i < getArity ty - 1 then [] else es) $ matchProgs cmn etrie ty    -- absents ga nai baai
    matchingPrograms ty pgsf@(PGSF (_,_,cmn) _ _) = fromRc $ fmap (toAnnExprWindWind (reducer cmn) ty) $ lookupWithAbsents pgsf ty     -- absents mo fukumeru baai
    unifyingPrograms ty pgsf@(PGSF (_,_,cmn) _ _) = catBags $ fromRc $ fmap (\ ((es,_),_,_) -> map (toAnnExpr $ reducer cmn) es) $ unifyingPossibilities ty pgsf
instance Expression e => WithCommon (PGSF e) where
    extractCommon    (PGSF (_,_,cmn) _ _)      = cmn

unifyingPossibilities ty memodeb = unPS (unifyableExprs memodeb [] ty) emptySubst 0

matchProgs :: Expression e => Common -> ExpTrie e -> Type -> Matrix AnnExpr
matchProgs cmn etrie ty = fmap (toAnnExprWindWind (reducer cmn) ty) $ lookupReorganized etrie ty -- こっちだとlookup
{-
matchProgs memodeb ty = fmap toAnnExpr $ wind (fmap (mapCE Lambda)) (lookupFuns memodeb) [] (quantify ty)                 -- こっちだとrecompute というと語弊がある．recomputeしたきゃlmtのところを変えるべし．

-- matchProgsのみの下請け，matchFunsと交換可能
lookupFuns :: (Expression e, Ord e) => MemoDeb e -> [Type] -> Type -> BF e
lookupFuns memodeb@((_,mt),_,tcl,rtrie) avail reqret =
{-
#ifdef CLASSIFY
                                  fmap fromAnnExpr $ toRc $ filterDM tcl rtrie ty $ fromRc $ fmap (toAnnExprWind ty) $
#endif
-}
--                                  mapDepth uniqSort $
                                             matchFuns memodeb avail reqret
    where ty = popArgs avail reqret
-}

specializedPossibleTypes :: Type -> MemoDeb CoreExpr -> TypeTrie -> Recomp Type
specializedPossibleTypes ty memodeb ttrie = runPS (fmap (\(av,t) -> popArgs av t) $ specializedTypes memodeb ttrie [] ty)
-- specializedPossibleTypes ty memodeb@(_,((mt,_),_,_,_)) = fmap (\(_,s,_) -> apply s ty) $ toRc $ lmtty mt ty


type MemoDeb e = (ClassLib e, (([[Prim]],[[Prim]]),([[Prim]],[[Prim]])), Common)

mkTrieOptSF :: Expression e => Common -> [Typed [CoreExpr]] -> [[Typed [CoreExpr]]] -> [[Typed [CoreExpr]]] -> PGSF e
mkTrieOptSF cmn classes txsopt txs
    = fix $ \pgsf -> PGSF memoDeb typeTrie $ mkMTexp (tcl cmn) (\ty -> filtBF cmn ty $ matchFunctions pgsf ty)
    where qtlopt = splitPrimss txsopt
          qtl    = splitPrimss txs
          memoDeb  = (mkCL cmn classes, (qtlopt,qtl), cmn)
          typeTrie = mkMTty (tcl cmn) (\ty -> freezePS ty (specTypes memoDeb typeTrie ty))
dbToCumulativeMx :: (Ord a) => DBound a -> Matrix a
dbToCumulativeMx (DB f) = Mx $ case map (sort . map fst . f) [0..] of
                                 xss -> let result = zipWith (diffSortedBy compare) xss $ scanl (++) [] result in result -- 多分本当は明示的にlookupし直すべき．
{- The following does not accurately give other chances to the expressions once dropped. コードをいじっているうちにいつの間にか最初の設計を忘れてこんなんなってた．
-- dbToCumulativeMx (DB f) = Mx $ map (map fst . f) [0..]
dbToCumulativeMx (DB f) = let foo = map (sort . map fst . f) [0..]
                          in Mx $ zipWith (diffSortedBy compare) foo ([]:foo)
--                          in Mx $ zipWith (\\) foo ([]:foo)
-}
mkTrieOptSFIO :: Expression e => Common -> [Typed [CoreExpr]] -> [[Typed [CoreExpr]]] -> [[Typed [CoreExpr]]] -> IO (PGSF e)
mkTrieOptSFIO cmn classes txsopt txs
    = fixIO $ \pgsf -> fmap (PGSF memoDeb typeTrie) $ mkMTIO (tcl cmn) (\ty -> filtBFIO cmn ty $ matchFunctions pgsf ty)
    where qtlopt = splitPrimss txsopt
          qtl    = splitPrimss txs
          memoDeb  = (mkCL cmn classes, (qtlopt,qtl), cmn)
          typeTrie = mkMTty (tcl cmn) (\ty -> freezePS ty (specTypes memoDeb typeTrie ty))
dbtToCumulativeMx :: (Ord a) => DBoundT IO a -> IO (Matrix a)
dbtToCumulativeMx (DBT f) = do ts <- interleaveActions $ map f [0..]
                               let xss = map (sort . map fst) ts
                               let result = zipWith (diffSortedBy compare) xss $ scanl (++) [] result 
                               return $ Mx result -- 多分本当は明示的にlookupし直すべき．

mkMTty = mkMT
mkMTexp = mkMT

mondepth = zipDepthRc (\d xs -> trace ("depth="++show d++", and the length is "++show (length xs)) xs) -- depthと表示するなら+1するべきであった．(0から始まるので)


type BFT = Recomp
unBFM = unMx


{-
freezePS :: (Search m, Expression e) => Type -> PriorSubsts m (ExpTip e) -> Matrix (ExpTip e,Subst,Int)
freezePS ty ps
    = let mxty = maxVarID ty -- `max` maximum (map maxVarID avail)
      in Mx $ map (tokoro10ap ty) $ scanl1 (++) $ unMx $ toMx $ unPS ps emptySubst (mxty+1)
-}
freezePS :: Type -> PriorSubsts Recomp Type -> Matrix (Type,Subst,TyVar)
freezePS ty ps
    = let mxty = maxVarID ty -- `max` maximum (map maxVarID avail)
--      in zipDepthMx (\d tups -> map (\(Mx xss, s, i)->(xss!!d, s, i)) $ tokoro10ap ty tups) $ toMx $ fmap fst $ Rc $ unDB $ unPS ps emptySubst (mxty+1)
      in mapDepth tokoro10ap $ toMx $ fmap fst $ Rc $ unDB $ fromRc $ unPS ps emptySubst (mxty+1) 
  --  tokoro10 in place of tokoro10ap ty causes an infinite loop.
  --  fps mxty ps can be used in place of unPS ps emptySubst (mxty+1)

-- MemoStingy.tokoro10 is different from T10.tokoro10, in that duplicates will be removed.
-- (Note that the type can be specialized to [(Type,k,i)] -> [(Type,k,i)])
tokoro10 :: (Eq k, Ord k) => [(a,k,i)] -> [(a,k,i)]
tokoro10 = mergesortWithBy const (\ (_,k,_) (_,l,_) -> k `compare` l)

-- tokoro10fstfst = mergesortWithBy const (\ ((k,_),_,_) ((l,_),_,_) -> k `compare` l)

tokoro10ap :: [(Type,s,i)] -> [(Type,s,i)]
-- tokoro10ap = mergesortWithBy const (\ (t,_,_) (u,_,_) -> compare t u)
tokoro10ap = M.elems . M.fromListWith const . map (\ t@(ty,_,_) -> ( {- normalize -} ty, t))

-- availにしろTypeにしろapplyされている．
-- だからこそ，runAnotherPS的にemptySubstに対して実行した方が効率的なはず？ でも，Substitutionってそんなにでかくならなかったのでは？FiniteMapでもassoc listでも変わらなかった気が．



fps :: Search m => TyVar -> PriorSubsts m e -> m (e,[(TyVar, Type)],TyVar)
fps mxty (PS f) = do (exprs, sub, m) <- f emptySubst (mxty+1)
                     return (exprs, filterSubst sub mxty, m)
    where filterSubst :: Subst -> TyVar -> [(TyVar, Type)]
          filterSubst sub  mx = [ t | t@(i,_) <- sub, inRange (0,mx) i ] -- note that the assoc list is NOT sorted.




specializedTypes :: (Search m, Expression e) => MemoDeb e -> TypeTrie -> [Type] -> Type -> PriorSubsts m ([Type],Type)
specializedTypes memodeb ttrie avail t = do _ <- specializedCases memodeb ttrie avail t
                                            subst <- getSubst
                                            return (map (apply subst) avail, apply subst t)
-- specializedCases is the same as unifyableExprs, except that the latter returns PriorSubsts BF [CoreExpr], and that the latter considers memodepth.
specializedCases, specCases :: (Search m, Expression e) => MemoDeb e -> TypeTrie -> [Type] -> Type -> PriorSubsts m BitSet
specializedCases memodeb ttrie = applyDo (specCases memodeb ttrie)
-- specCases memodeb = wind_ (\avail reqret -> reorganize_ (\newavail -> uniExprs_ memodeb newavail reqret) avail)
specCases memodeb ttrie avail (t0:->t1) = fmap (`unsafeShiftR` 1) $ specCases memodeb ttrie (t0 : avail) t1
specCases memodeb ttrie avail reqret    = reorganize_ (\newavail -> uniExprs_ memodeb ttrie newavail reqret) avail





uniExprs_ :: (Search m, Expression e) => MemoDeb e -> TypeTrie -> [Type] -> Type -> PriorSubsts m BitSet
{-
uniExprs_ memodeb avail t
    = convertPS fromRc $ psListToPSRecomp lfp
    where lfp depth
              | memocond depth     = lookupUniExprs memodeb avail t depth
              | otherwise          = makeUniExprs memodeb avail t depth >> return ()
-}
uniExprs_ memodeb ttrie avail t
    = convertPS fromMx $ lookupNormalizedSharedBits (\ixs _ -> ixs) (lookupTypeTrie memodeb ttrie) avail t

{-
lookupUniExprs :: MemoDeb CoreExpr -> [Type] -> Type -> Int -> PriorSubsts [] ()
lookupUniExprs memodeb@(_,(mt,_),_,_) avail t depth
    = fmap (const ()) $ lookupNormalized (\tn -> unMx (lmtty mt tn) !! depth) avail t

makeUniExprs :: MemoDeb CoreExpr -> [Type] -> Type -> Int -> PriorSubsts [] Type
makeUniExprs memodeb avail t depth
    = convertPS tokoro10fst $
                do psRecompToPSList (reorganize_' (\av -> specCases' memodeb av t) avail) depth
                   sub   <- getSubst
                   return $ quantify (apply sub $ popArgs avail t)
-}

lookupReorganized md typ = let (avs, retty) = splitArgs $ normalize typ
                           in reorganizerId' (\av -> lmt md $ popArgs av retty) avs

-- entry point for memoization
specTypes :: Expression e => MemoDeb e -> TypeTrie -> Type -> PriorSubsts Recomp Type
specTypes memodeb ttrie ty
                           = let (avail,t) = splitArgs ty
                             in convertPS (zipDepthRc (\i es -> if i < length avail - 1 then [] else es)) $ do
                                reorganize_ (\av -> specCases' memodeb ttrie av t) avail
-- quantifyはmemo先で既にやられているので不要
                                applyPS ty

instance Monoid BitSet where
    mappend = (.|.)
    mempty  = 0

funApSub_ :: (Search m, Monoid a) => (Type -> PriorSubsts m ()) -> (Type -> PriorSubsts m a) -> (Type -> PriorSubsts m a) -> Type -> PriorSubsts m a
funApSub_ clbehalf lltbehalf behalf (t:=>ts) = do clbehalf t
                                                  funApSub_ clbehalf lltbehalf behalf ts
funApSub_ clbehalf lltbehalf behalf (t:>ts)  = liftM2 mappend (lltbehalf t) (funApSub_ clbehalf lltbehalf behalf ts)
funApSub_ clbehalf lltbehalf behalf (t:->ts) = liftM2 mappend (behalf t)    (funApSub_ clbehalf lltbehalf behalf ts)
funApSub_ clbehalf lltbehalf behalf _t       = return mempty

funApSub_spec clbehalf behalf = funApSub_ clbehalf behalf behalf

funApSub_forcingNil :: (Type -> PriorSubsts Recomp ()) -> (Type -> PriorSubsts Recomp BitSet) -> (Type -> PriorSubsts Recomp BitSet) -> Type -> BitSet -> PriorSubsts Recomp ()
funApSub_forcingNil clbehalf lltbehalf behalf t bsf 
  = funApSub_forcingNil_cont clbehalf lltbehalf behalf t bsf $ \bs -> guard $ bs == 0
funApSub_forcingNil_spec clbehalf behalf = funApSub_forcingNil clbehalf behalf behalf

funApSub_forcingNil_cont :: (Type -> PriorSubsts Recomp ()) -> (Type -> PriorSubsts Recomp BitSet) -> (Type -> PriorSubsts Recomp BitSet) -> Type -> BitSet -> (BitSet->PriorSubsts Recomp a) -> PriorSubsts Recomp a
funApSub_forcingNil_cont clbehalf lltbehalf behalf (t:=>ts) bsf cont = do clbehalf t
                                                                          funApSub_forcingNil_cont clbehalf lltbehalf behalf ts bsf cont
funApSub_forcingNil_cont clbehalf lltbehalf behalf (t:>ts)  bsf cont = do bse <- lltbehalf t
                                                                          let newRemaining = bsf .&. complement bse
                                                                          forceNil newRemaining $
                                                                            funApSub_forcingNil_cont clbehalf lltbehalf behalf ts newRemaining cont
funApSub_forcingNil_cont clbehalf lltbehalf behalf (t:->ts) bsf cont = do bse <- behalf t
                                                                          let newRemaining = bsf .&. complement bse
                                                                          forceNil newRemaining $
                                                                            funApSub_forcingNil_cont clbehalf lltbehalf behalf ts newRemaining cont
funApSub_forcingNil_cont clbehalf lltbehalf behalf _t       bsf cont = cont bsf

funApSub_forcingNil_cont_spec clbehalf behalf = funApSub_forcingNil_cont clbehalf behalf behalf

mguAssumptionsBits :: (Functor m, MonadPlus m) => Type -> [Type] -> PriorSubsts m BitSet
mguAssumptionsBits  patty assumptions = applyDo mguAssumptionsBits' assumptions patty
mguAssumptionsBits' assumptions patty = msum $ zipWith (\n t -> mguPS patty t >> return (1 `shiftL` n)) [0..] assumptions

specCases' :: Expression e => MemoDeb e -> TypeTrie -> [Type] -> Type -> PriorSubsts Recomp ()
-- specCases' trie prims@(primgen,primmono) avail reqret = msum (map (retMono.fromPrim) primmono) `mplus` msum (map retMono fromAvail ++ map retGen primgen)
specCases' memodeb@(CL classLib, (prims@(primgen,primmono),_),cmn) ttrie avail reqret
 = mapSum retPrimMono primmono `mplus` msum (zipWith retMono (iterate (`unsafeShiftL` 1) 1) avail) `mplus` mapSum retGen primgen
    where fas | constrL $ opt cmn = funApSub_ clbehalf lltbehalf behalf
              | otherwise         = funApSub_spec      clbehalf behalf
          fasf| constrL $ opt cmn = funApSub_forcingNil clbehalf lltbehalf behalf
              | otherwise         = funApSub_forcingNil_spec      clbehalf behalf
          behalf    = specializedCases memodeb ttrie avail
          lltbehalf ty = mguAssumptionsBits ty avail
          clbehalf  ty = mguPrograms classLib ty >> return ()
          lenavails = length avail
          fullBits  | lenavails > 29 = 0
                    | otherwise      = (1 `unsafeShiftL` lenavails) - 1
          -- retPrimMono :: (Int, Type, Int, Typed [CoreExpr]) -> PriorSubsts BFT ()
          retPrimMono (_, arity, retty, numtvs, _xs:::ty)
                                              = napply arity delayPS $
                                                do tvid <- reserveTVars numtvs
                                                   mguPS reqret (mapTV (tvid+) retty)
                                                   fasf (mapTV (tvid+) ty) fullBits
          -- retMono :: BitSet -> Type -> PriorSubsts BFT ()
          retMono ix ty = napply (getArity ty) delayPS $ do
                          mguPS reqret (getRet ty)
                          fasf ty $ fullBits .&. complement ix
          -- retGen :: (Int, Type, Int, Typed [CoreExpr]) -> PriorSubsts BFT ()
          retGen (_, arity, _r, numtvs, _s:::ty) = napply arity delayPS $
                                             do tvid <- reserveTVars numtvs -- この（最初の）IDそのもの（つまり返り値のtvID）はすぐに使われなくなる
                                               -- let typ = apply (unitSubst tvid reqret) (mapTV (tvid+) ty) -- mapTVとapplyはhylo-fusionできるはずだが，勝手にされる？
                                               --                                                              -- unitSubstをinlineにしないと駄目か
                                                mkSubsts (tvndelay $ opt cmn) tvid reqret
                                                funApSub_forcingNil_cont_spec clbehalf behalf (mapTV (tvid+) ty) fullBits $ \i -> do
                                                  gentvar <- applyPS (TV tvid)

                                                  guard (orderedAndUsedArgs gentvar)
                                                  fasf gentvar i

-- absentを含める場合こっちを使う
lookupWithAbsents :: (Search m, Expression e) => PGSF e -> Type -> m e
lookupWithAbsents memodeb ty
  = case splitArgs ty of 
    (a,r) -> wind (fmap (mapCE Lambda)) (lookupNormalizedSharedET (lookupTypeTrieAndExpTrie memodeb)) a r
--unifyableExprs memodeb = applyDo (wind (fmap (map (mapCE Lambda))) (lookupNormalizedShared (\ixs -> map (decodeVarsCE ixs)) (lookupTypeTrieAndExpTrie memodeb)))

lookupNormalizedSharedET :: (Search m, Search n, Expression e) => (Type -> m ([e], Subst, TyVar)) ->  [Type] -> Type -> n e
lookupNormalizedSharedET fun avail t
  = let annAvails = zip [0..] avail
    in fromRc $ Rc $ \d -> [ decodeVars (length avail) ixs e
                           | avs <- combs (d+1) annAvails
                           , let (ixs, newavails) = unzip avs
                                 (tn, _decoder) = encode newt (maxVarID newt + 1)
                                 newt = popArgs newavails t
                           , (exprs, _, _) <- unRc (toRc (fun tn)) d
                           , e <- exprs
                           ]

type Generator m e = PGSF e -> [Type] -> Type -> PriorSubsts m ([e], BitSet)

unifyableExprs ::  Expression e => Generator Recomp e
unifyableExprs memodeb
  = applyDo (wind (fmap (\ (es, bs) -> (map (mapCE Lambda) es, bs `unsafeShiftR` 1)))
                  (\avail -> lookupNormalizedShared (\ixs ixBits e -> (map (decodeVars (length avail) ixs) e, ixBits)) (lookupTypeTrieAndExpTrie memodeb) avail))
--unifyableExprs memodeb = applyDo (wind (fmap (map (mapCE Lambda))) (lookupNormalizedShared (\ixs -> map (decodeVarsCE ixs)) (lookupTypeTrieAndExpTrie memodeb)))


-- memocondexp t d = 1<d && d<7
memocondexp t d = size t < 8 && 0<d && d<7

lookupTypeTrie :: Expression e => MemoDeb e -> TypeTrie -> Type -> Recomp (Type, Subst, TyVar)
lookupTypeTrie memodeb@(_, _, cmn) ttrie t
    = Rc $ \d -> unMx (if memoCondPure (opt cmn) t d
                       then lookupNorm (lmtty ttrie) t
                       else freezePS t $ specTypes memodeb ttrie t  ) !! d -- if d<8 then d else 7
lookupTypeTrieAndExpTrie :: Expression e => PGSF e -> Type -> Recomp ([e], Subst, TyVar)
lookupTypeTrieAndExpTrie (PGSF memodeb@(_, _, cmn) ttrie etrie) t
  = Rc $ \d -> if memoCondPure (opt cmn) t d
                 then [ (unMx (lookupReorganized etrie $ apply s t) !! d, s, i)
                            | (_ty, s, i) <- unMx (lookupNormReorganized (lmtty ttrie) t) !! d {- if d<8 then d else 7 -} ]
                 else -- [ (unMx (filtBF cmn ty $ matchFunctions memodeb ty) !! d, s, i) -- exptrieも同様にmemoCondPureを使う場合．
                     [ (unMx (lookupReorganized etrie $ apply s t) !! d, s, i)  -- exptrieでは全部memoizeする場合．
                            | (ty, s, i) <- unMx (freezePS t $ specTypes memodeb ttrie t) !! d {- if d<8 then d else 7 -} ]

lookupNormReorganized fun typ = let (avs, retty) = splitArgs typ
                               in reorganize_ (\av -> lookupNorm fun (popArgs av retty)) avs
lookupNorm :: MonadPlus m => (Type -> m (e, Subst, TyVar)) -> Type -> m (e, Subst, TyVar)
lookupNorm = id
{-
lookupNorm fun typ
    = do let
             mx  = maxVarID typ + 1
             (tn, decoder) = encode typ mx
         (es, sub, m) <- fun tn
         return (es, retrieve decoder sub, mx+m)
-}


lookupNormalized :: (Functor m, MonadPlus m) => (Type -> m (e, Subst, TyVar)) ->  [Type] -> Type -> PriorSubsts m e
lookupNormalized fun avail t
    = do mx <- getMx
         let typ = popArgs avail t
             (tn, decoder) = encode typ mx
         (es, sub, m) <-  mkPS (fun tn)
         updatePS (retrieve decoder sub)
         updateMx (m+)
         return es
lookupNormalizedShared :: (Search m, Search n) => ([Int8] -> BitSet -> e -> r) -> (Type -> m (e, Subst, TyVar)) ->  [Type] -> Type -> PriorSubsts n r
lookupNormalizedShared ceDecoder fun avail t
    = let annAvails = zip3 [0..] (iterate (`unsafeShiftL` 1) 1) avail
      in PS (\subst mx -> fromRc $ Rc $ \d ->concat 
                                             [ map (\ (exprs, sub, m) -> (ceDecoder ixs ixBits exprs, retrieve decoder sub `plusSubst` subst, mx+m)) $ unRc (toRc (fun tn)) d 
                                             | annAvs <- combs (d+1) annAvails
                                             , let (ixs, ixBitss, newavails) = unzip3 annAvs 
                                                   ixBits = foldl (.|.) 0 ixBitss
                                                   (tn, decoder) = encode (popArgs newavails t) mx
                                             ])

type BitSet = Word32
#if __GLASGOW_HASKELL__ < 706
countBits = countBits32
#else
countBits = popCount
#endif
-- Also, if BitSet = Integer, countBits32 should be used in place of popCount because popCount for Integers is inefficient.

lookupNormalizedSharedBits :: (Search m, Search n) => (BitSet -> e -> r) -> (Type -> m (e, Subst, TyVar)) ->  [Type] -> Type -> PriorSubsts n r
lookupNormalizedSharedBits f = lookupNormalizedShared (const f)


tokoro10fst :: (Eq k, Ord k) => [(k,s,i)] -> [(k,s,i)]
-- tokoro10fst = mergesortWithBy const (\ (k,_,_) (l,_,_) -> k `compare` l)
tokoro10fst = M.elems . M.fromListWith const . map (\ t@(k,_,_) -> (k,t))

-- entry for memoization
matchFunctions :: (Expression e) => PGSF e -> Type -> Recomp e
matchFunctions memodeb ty = -- mapDepth (filter (not . isAbsent (getArity ty))) $       -- KOKO 1
                            case splitArgs (saferQuantify ty) of (avail,t) -> matchFuns memodeb avail t

-- saferQuantify ty = let offset = maxVarID (unquantify ty) + 1 in quantify' $ mapTV (offset+) ty

matchFuns :: Expression e => PGSF e -> [Type] -> Type -> Recomp e
matchFuns memodeb avail reqret = zipDepthRc (\i es -> if i < length avail - 1 then [] else es) $ catBags $ runPS (matchFuns' unifyableExprs memodeb avail reqret)

matchFuns' :: Expression e => Generator Recomp e -> PGSF e -> [Type] -> Type -> PriorSubsts Recomp [e]
-- matchFuns' = generateFuns matchPS filtExprs lookupListrie -- MemoDebの型の違いでこれはうまくいかなんだ．
matchFuns' rec md@(PGSF (CL classLib, (_,(primgen,primmono)),cmn) _ _) avail reqret
    = let clbehalf  = mguPrograms classLib
          behalf    = rec md avail
          lltbehalf = lookupListrie lenavails rec md avail -- heuristic filtration
          lenavails = length avail
          fullBits | lenavails > 29 = 0
                   | otherwise      = (1 `unsafeShiftL` lenavails) - 1
--          fe :: Type -> Type -> [CoreExpr] -> [CoreExpr] -- ^ heuristic filtration
          fe        = filtExprs (guess $ opt cmn)
      in fromAssumptionsBits cmn lenavails fullBits behalf (\a b -> guard $ a==b) reqret avail `mplus`
         convertPS (zipDepthRc (\i es -> if i < lenavails then [] else es))
                   (mapSum (retPrimMonoBits cmn lenavails fullBits clbehalf lltbehalf behalf matchPS reqret) primmono `mplus`
                    mapSum ((    if tv0 $ opt cmn then retGenTV0Bits else
                                 if tv1 $ opt cmn then retGenTV1Bits else retGenOrdBits) cmn lenavails fullBits fe clbehalf lltbehalf behalf reqret) primgen)
--          mapSum (retGenTV1Bits cmn lenavails fe clbehalf lltbehalf behalf reqret) primgen

fromAssumptionsBits :: (Expression e) => Common -> Int -> BitSet -> (Type -> PriorSubsts Recomp ([e],BitSet)) -> (Type -> Type -> PriorSubsts Recomp ()) -> Type -> [Type] -> PriorSubsts Recomp [e]
fromAssumptionsBits cmn lenavails fullBits behalf mps reqret avail = msum $ map (retMonoBits cmn lenavails fullBits behalf (flip mps reqret)) (zip [0..] avail)

retMonoBits :: (Expression e) => Common -> Int -> BitSet -> (Type -> PriorSubsts Recomp ([e],BitSet)) -> (Type -> PriorSubsts Recomp ()) -> (Int, Type) -> PriorSubsts Recomp [e]
retMonoBits cmn lenavails fullBits behalf tok fromBlah
                  = do let (n, ty) = fromBlah
                           (arity,args,retty) = revSplitArgs ty
                       tok retty
{-
                       (es,ixBits) <- convertPS (ndelay arity) $
                                      fapBits behalf args ([ mkHead (reducer cmn) lenavails arity $ X n], 1 `shiftL` n)
                       guard $ ixBits == fullBits    -- KOKO 2
                       return es
-}
                       convertPS (ndelay arity) $
                                      funApSubBits_forcingNil undefined behalf behalf ty ([ mkHead (reducer cmn) lenavails 0 arity $ X $ fromIntegral n], fullBits `clearBit` n)



retPrimMonoBits :: (Expression e) => Common -> Int -> BitSet -> (Type -> PriorSubsts Recomp [e]) -> (Type -> PriorSubsts Recomp ([e],BitSet)) -> (Type -> PriorSubsts Recomp ([e],BitSet)) -> (Type -> Type -> PriorSubsts Recomp ()) -> Type -> Prim -> PriorSubsts Recomp [e]
retPrimMonoBits cmn lenavails fullBits clbehalf lltbehalf behalf mps reqret (numcxts, arity, retty, numtvs, xs:::ty)
                                              = do tvid <- reserveTVars numtvs
                                                   mps (mapTV (tvid+) retty) reqret
                                                   convertPS (ndelay arity) $
                                                             funApSubBits_forcingNil clbehalf lltbehalf behalf (mapTV (tvid+) ty) (map (mkHead (reducer cmn) lenavails numcxts arity) xs, fullBits)

funApSubBits, funApSubBits_resetting :: (Search m, Expression e) => (Type -> PriorSubsts m [e]) -> (Type -> PriorSubsts m ([e],BitSet)) -> (Type -> PriorSubsts m ([e],BitSet)) -> Type -> ([e],BitSet) -> PriorSubsts m ([e],BitSet)
funApSubBits = funApSubOpBits (<$>)
funApSubOpBits op clbehalf lltbehalf behalf = faso
    where faso (t:=>ts) (funs, bsf)
              = do args <- clbehalf t
                   faso ts (liftM2 op funs args, bsf)
          faso (t:> ts) (funs, bsf)
              = do (args, bse) <- lltbehalf t
                   faso ts (liftM2 op funs args, bsf .|. bse)
          -- original. 
          faso (t:->ts) (funs, bsf)
              = do (args, bse) <- behalf t
                   faso ts (liftM2 op funs args, bsf .|. bse)
          faso _        tup = return tup
funApSubBits_resetting = funApSubOpBits_resetting (<$>)
funApSubOpBits_resetting op clbehalf lltbehalf behalf = faso
    where faso (t:=>ts) (funs, bsf)
              = do args <- clbehalf t
                   faso ts (liftM2 op funs args, bsf)
          faso (t:> ts) (funs, bsf)
              = do (args, bse) <- lltbehalf t
                   faso ts (liftM2 op funs args, bsf .&. complement bse)
          -- original. 
          faso (t:->ts) (funs, bsf)
              = do (args, bse) <- behalf t
                   faso ts (liftM2 op funs args, bsf .&. complement bse)
          faso _        tup = return tup
fapBits behalf ts tups = foldM (\ (fs,bsf) t -> do (args, bse) <- behalf t
                                                   return (liftM2 (<$>) fs args, bsf .|. bse))
                               tups
                               ts

forceNil :: BitSet -> PriorSubsts Recomp e -> PriorSubsts Recomp e
forceNil newRemaining = convertPS (zipDepthRc (\i es -> if i < countBits newRemaining - 1 then [] else es))

funApSubBits_forcingNil :: (Expression e) => (Type -> PriorSubsts Recomp [e]) -> (Type -> PriorSubsts Recomp ([e],BitSet)) -> (Type -> PriorSubsts Recomp ([e],BitSet)) -> Type -> ([e],BitSet) -> PriorSubsts Recomp [e]
funApSubBits_forcingNil clbehalf lltbehalf behalf ty = funApSubOpBits_forcingNil  (aeAppErr (" to the request of "++show ty)) clbehalf lltbehalf behalf ty
funApSubBits_forcingNil_cont :: (Expression e) => (Type -> PriorSubsts Recomp [e]) -> (Type -> PriorSubsts Recomp ([e],BitSet)) -> (Type -> PriorSubsts Recomp ([e],BitSet)) -> Type -> ([e],BitSet) -> (([e],BitSet) -> PriorSubsts Recomp [e]) -> PriorSubsts Recomp [e]
funApSubBits_forcingNil_cont clbehalf lltbehalf behalf ty = funApSubOpBits_forcingNil_cont (aeAppErr (" to the request of "++show ty)) clbehalf lltbehalf behalf ty
funApSubOpBits_forcingNil_cont op clbehalf lltbehalf behalf = faso
    where faso (t:=>ts) (funs, bsf) cont 
              = do args <- clbehalf t
                   faso ts (liftM2 op funs args, bsf) cont
          faso (t:> ts) (funs, bsf) cont
              = do (args, bse) <- lltbehalf t
                   let newRemaining = bsf .&. complement bse
                   forceNil newRemaining $
                     faso ts (liftM2 op funs args, newRemaining) cont
          -- original. 
          faso (t:->ts) (funs, bsf) cont
              = do (args, bse) <- behalf t
                   let newRemaining = bsf .&. complement bse
                   forceNil newRemaining $ 
                     faso ts (liftM2 op funs args, newRemaining) cont
          faso _        (funs, bsf) cont = cont (funs, bsf)
funApSubOpBits_forcingNil op clbehalf lltbehalf behalf t tup
  = funApSubOpBits_forcingNil_cont op clbehalf lltbehalf behalf t tup $ \(funs, bsf) ->
                                      do guard $ bsf == 0
                                         return funs
-- Data.Bits.popCount does the job. However, instance Bits Integer uses popCountDefault, which uses the naive algorithm.
countBits32 bin 
  = let quad = bin - ((bin `unsafeShiftR` 1) .&. 0x55555555) -- quadary coded
        hex  = (quad .&. 0x33333333) + ((quad `unsafeShiftR` 2) .&. 0x33333333) -- hexadecimalary coded
    in fromIntegral $ ((((hex + (hex `unsafeShiftR` 4)) .&. 0x0F0F0F0F) * 0x01010101) `unsafeShiftR` 24) .&. 0xFF -- The last (.&. 0xFF) should not be necessary when using Word32.

retGenOrdBits cmn lenavails fullBits fe clbehalf lltbehalf behalf reqret (numcxts, arity, _retty, numtvs, xs:::ty)
  = convertPS (ndelay arity) $              do tvid <- reserveTVars numtvs -- この（最初の）IDそのもの（つまり返り値のtvID）はすぐに使われなくなる
                                               -- let typ = apply (unitSubst tvid reqret) (mapTV (tvid+) ty) -- mapTVとapplyはhylo-fusionできるはずだが，勝手にされる？
                                               --                                                              -- unitSubstをinlineにしないと駄目か
                                               a <- mkSubsts (tvndelay $ opt cmn) tvid reqret
                                               (exprs, bs1) <- funApSubBits_resetting clbehalf lltbehalf behalf (mapTV (tvid+) ty) (map (mkHead (reducer cmn) lenavails numcxts (arity+a)) xs, fullBits)
                                               gentvar <- applyPS (TV tvid)
                                               guard (orderedAndUsedArgs gentvar) -- この辺のcheckをTVnに入る前の早い段階にやるのは1つの考え方だが，TVn中にreplaceされたりはしないのか?
                                               (es, bs2) <- funApSub'' False gentvar (fe gentvar ty exprs, bs1)
                                               guard $ bs2 == 0
                                               return es
    where
--                    funApSub'' filtexp (TV _ :-> _)     funs = mzero -- mkSubstsで導入されたtyvarsが使われていないケース．replaceされた結果TVってケースはとりあえず無視....
                    funApSub'' filtexp (t:->ts@(u:->_)) (funs, bs)
--                        | t > u     = mzero
                        | otherwise = do (args, ixs) <- behalf t
                                         funApSub'' (t==u) ts (if filtexp then [ f <$> e | f <- funs, e <- args, let _:$d = toCE f, d <= toCE e ]
                                                                         else liftM2 (<$>) funs args,  
                                                               bs .&. complement ixs)
-- てゆーかtとuが同じならばもっといろんなことができそう．
                    funApSub'' filtexp (t:->ts) (funs, bs)
                                    = do (args, ixs) <- behalf t
                                         return (if filtexp then [ f <$> e | f <- funs, e <- args, let _:$d = toCE f, d <= toCE e]
                                                            else liftM2 (<$>) funs args,  
                                                 bs .&. complement ixs)
                    funApSub'' _fe _t tups = return tups

retGenTV1Bits cmn lenavails fullBits fe clbehalf lltbehalf behalf reqret (numcxts, arity, _retty, numtvs, xs:::ty)
  = convertPS (ndelay arity) $              do tvid <- reserveTVars numtvs -- この（最初の）IDそのもの（つまり返り値のtvID）はすぐに使われなくなる
                                               -- let typ = apply (unitSubst tvid reqret) (mapTV (tvid+) ty) -- mapTVとapplyはhylo-fusionできるはずだが，勝手にされる？
                                               --                                                              -- unitSubstをinlineにしないと駄目か
                                               a <- mkSubst (tvndelay $ opt cmn) tvid reqret
{-                                               
                                               (exprs, bs1) <- funApSubBits_resetting clbehalf lltbehalf behalf (mapTV (tvid+) ty) (map (mkHead (reducer cmn) lenavails (getLongerArity ty+a)) xs, fullBits)
                                               gentvar <- applyPS (TV tvid)
                                               guard (usedArg (tvid+1) gentvar)
                                               funApSubBits_forcingNil clbehalf lltbehalf behalf gentvar (fe gentvar ty exprs, bs1)
-}
                                               funApSubBits_forcingNil_cont clbehalf lltbehalf behalf (mapTV (tvid+) ty) (map (mkHead (reducer cmn) lenavails numcxts (arity+a)) xs, fullBits) $ \(exprs, bs1) -> do
                                                 gentvar <- applyPS (TV tvid)
                                                 guard (usedArg (tvid+1) gentvar)
                                                 funApSubBits_forcingNil clbehalf lltbehalf behalf gentvar (fe gentvar ty exprs, bs1)

retGenTV0Bits cmn lenavails fullBits fe clbehalf lltbehalf behalf reqret (numcxts, arity, _retty, numtvs, xs:::ty)
  = convertPS (ndelay arity) $              do tvid <- reserveTVars numtvs -- この（最初の）IDそのもの（つまり返り値のtvID）はすぐに使われなくなる
                                               -- let typ = apply (unitSubst tvid reqret) (mapTV (tvid+) ty) -- mapTVとapplyはhylo-fusionできるはずだが，勝手にされる？
                                               --                                                              -- unitSubstをinlineにしないと駄目か
                                               updatePS (unitSubst tvid reqret)
                                               exprs <- funApSubBits_forcingNil clbehalf lltbehalf behalf (mapTV (tvid+) ty) (map (mkHead (reducer cmn) lenavails numcxts arity) xs, fullBits)
                                               gentvar <- applyPS (TV tvid)
                                               return $ fe gentvar ty exprs




matchAssumptionsBits :: (Functor m, MonadPlus m, Expression e) => Common -> Int -> Type -> [Type] -> PriorSubsts m ([e],BitSet)
matchAssumptionsBits cmn lenavails reqty assumptions
    = do s <- getSubst
         let newty = apply s reqty
             (numcxts, arity) = getArities newty
         msum $ zipWith (\n t -> matchPS newty t >> return ([mkHead (reducer cmn) lenavails numcxts arity (X n)], 1 `shiftL` fromIntegral n)) [0..] assumptions
-- match の場合，通常はreqtyの方だけapply substすればよい．

lookupListrie :: (Search m, Expression e) => Int -> Generator m e -> Generator m e
lookupListrie lenavails rec memodeb avail t
                                    | constrL opts = matchAssumptionsBits cmn lenavails t avail
                                    | guess opts = do
                                       (args, ixBits) <- rec memodeb avail t
                                       let args' = filter (not.isClosed.toCE) args
                                       when (null args') mzero
                                       return (args', ixBits)
                                    | otherwise  = do
                                       (args, ixBits) <- rec memodeb avail t
                                       let args' = filter (not.isConstrExpr.toCE) args
                                       when (null args') mzero
                                       return (args', ixBits)
    where opts = opt cmn
          cmn  = extractCommon memodeb
\end{code}
