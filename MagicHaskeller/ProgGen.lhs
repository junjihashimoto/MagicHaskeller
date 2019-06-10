-- 
-- (c) Susumu Katayama
--
\begin{code}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS -cpp #-}
module MagicHaskeller.ProgGen(ProgGen(PG), mkCL, ClassLib(..), mguPrograms) where

import MagicHaskeller.Types
import MagicHaskeller.TyConLib
import Control.Monad
import Data.Monoid
import MagicHaskeller.CoreLang
import Control.Monad.Search.Combinatorial
import MagicHaskeller.PriorSubsts
import Data.List(partition, sortBy, genericLength)
import Data.Ix(inRange)

import MagicHaskeller.ProgramGenerator
import MagicHaskeller.Options(Opt(..))

import MagicHaskeller.Classify
import MagicHaskeller.Instantiate

import MagicHaskeller.Expression

import MagicHaskeller.T10
import qualified Data.Map as Map

import MagicHaskeller.DebMT

import Debug.Trace

import Data.Monoid

import MagicHaskeller.MemoToFiles hiding (freezePS,fps)

traceTy _    = id
-- traceTy fty = trace ("lookup "++ show fty)


type BF = Recomp
-- type BF = DBound

type BFM = Matrix
-- type BFM = DBMemo
fromMemo :: Search m => Matrix a -> m a
fromMemo = fromMx
toMemo :: Search m => m a -> Matrix a
toMemo = toMx


-- Memoization table, created from primitive components

-- | The vanilla program generator corresponding to Version 0.7.*
newtype ProgGen = PG (MemoDeb (ClassLib CoreExpr) CoreExpr) -- ^ internal data representation
newtype ClassLib e = CL (MemoDeb (ClassLib e) e)
-- mapStrTyCon :: Search m => MemoDeb c m CoreExpr -> Map.Map String TyCon
-- mapStrTyCon = fst . extractTCL . PG

type MemoTrie a = MapType (BFM (Possibility a))

lmt mt fty =
       traceTy fty $
       lookupMT mt fty

lookupFunsShared :: (Search m) => Generator m CoreExpr -> Generator m CoreExpr
lookupFunsShared behalf memodeb@(_,mt,_,cmn) avail reqret
    = let annAvails = zip [0..] avail
      in PS (\subst mx -> fromRc $ Rc $ \d ->concat [ let (tn, decoder) = encode (popArgs newavails reqret) mx in map (decodeVarsPos ixs) $ map (\ (exprs, sub, m) -> (exprs, retrieve decoder sub `plusSubst` subst, mx+m)) $ unMx (lmt mt tn) !! d | annAvs <- combs (d+1) annAvails, let (ixs, newavails) = unzip annAvs ] :: [Possibility CoreExpr])

lookupFunsPoly :: (Search m, Expression e) => Generator m e -> Generator m e
lookupFunsPoly behalf memodeb@(_,mt,_,cmn) avail reqret
    = PS (\subst mx ->
              let (tn, decoder) = encode (popArgs avail reqret) mx
              in ifDepth (<= memodepth (opt cmn))
                         (fmap (\ (exprs, sub, m) -> (exprs, retrieve decoder sub `plusSubst` subst, mx+m)) $ fromMemo $ lmt mt tn)
                         (unPS (behalf memodeb avail reqret) subst mx) )

instance WithCommon ProgGen where
    extractCommon     (PG (_,_,_,cmn)) = cmn
instance ProgramGenerator ProgGen where
    mkTrie cmn classes tces = mkTriePG cmn classes tces
    unifyingPrograms   ty (PG x@(_,_,_,cmn)) = fromRc $ fmap (toAnnExpr $ reducer cmn) $ catBags $ fmap (\ (es,_,_) -> es) $ unifyingPossibilities   ty x
instance ProgramGeneratorIO ProgGen where
    mkTrieIO cmn classes tces = return $ mkTriePG cmn classes tces
    unifyingProgramsIO ty (PG x@(_,_,_,cmn)) = fmap (toAnnExpr $ reducer cmn) $ catBags $ fmap (\ (es,_,_) -> es) $ unifyingPossibilitiesIO ty x

unifyingPossibilities :: Search m => Type -> MemoDeb (ClassLib CoreExpr) CoreExpr -> m ([CoreExpr],Subst,TyVar)
unifyingPossibilities ty memodeb = unPS (mguProgs memodeb [] ty) emptySubst 0

unifyingPossibilitiesIO :: Type -> MemoDeb (ClassLib CoreExpr) CoreExpr -> RecompT IO ([CoreExpr],Subst,TyVar)
unifyingPossibilitiesIO ty memodeb = unPS (mguProgsIO memodeb [] ty) emptySubst 0

type MemoDeb c a = (c, MemoTrie a, ([[Prim]],[[Prim]]), Common)


mkTriePG :: Common -> [Typed [CoreExpr]] -> [[Typed [CoreExpr]]] -> ProgGen
mkTriePG cmn classes tces =   let qtl = splitPrimss tces
                                  trie = mkTrieMD (mkCL cmn classes) qtl cmn
                              in PG trie
mkCL :: Common -> [Typed [CoreExpr]] -> ClassLib CoreExpr
mkCL cmn classes = CL $ mkTrieMD undefined ([],[map annotateTCEs classes]) cmn
mkTrieMD :: ClassLib CoreExpr -> ([[Prim]],[[Prim]]) -> Common -> MemoDeb (ClassLib CoreExpr) CoreExpr
mkTrieMD cl qtl cmn
    = let trie = mkMT (tcl cmn) (\ty -> fromRc (let (avail,t) = splitArgs ty in freezePS (length avail) ty (mguFuns memoDeb avail t {- :: PriorSubsts BF [e] -})))
          memoDeb = (cl,trie,qtl,cmn)
      in memoDeb

-- moved from DebMT.lhs to avoid cyclic modules.
freezePS :: Search m => Int -> Type -> PriorSubsts m (Bag CoreExpr) -> m (Possibility CoreExpr)
freezePS arity ty ps
    = let mxty = maxVarID ty -- `max` maximum (map maxVarID avail)
      in mergesortDepthWithBy (\(xs,k,i) (ys,_,_) -> (xs `mappend` ys, k, i)) (\(_,k,_) (_,l,_) -> k `compare` l) $ fps arity mxty ps
fps :: Search m => Int -> TyVar -> PriorSubsts m [CoreExpr] -> m ([CoreExpr],[(TyVar, Type)],TyVar)
fps arity mxty (PS f) = do
                     (exprs, sub, m) <- f emptySubst (mxty+1)
                     let es = filter (not . isAbsent arity) exprs
                     guard $ not $ length es `seq` null es
                     return (es, filterSubst sub mxty, m)
    where filterSubst :: Subst -> TyVar -> [(TyVar, Type)]
          filterSubst sub  mx = [ t | t@(i,_) <- sub, inRange (0,mx) i ] -- note that the assoc list is NOT sorted.


type Generator m e = MemoDeb (ClassLib e) e -> [Type] -> Type -> PriorSubsts m [e]

mguProgramsIO, mguProgsIO :: Generator (RecompT IO) CoreExpr

mguProgramsIO memodeb = applyDo (mguProgsIO memodeb)

mguProgsIO memodeb@(_,mt,_,cmn) = wind (>>= (return . fmap Lambda)) (\avail reqret -> reorganize (\newavail -> (\memodeb avail reqr -> memoPSRTIO (memoCond $ opt cmn) -- (\_ty _dep -> return (Disk "/tmp/memo/mlist")  {- とりあえずこれでテスト -})
                                                                                                                                                mt
                                                                                                                                                (\ty -> let (av,rr) = splitArgs ty in generateFuns mguProgramsIO memodeb av rr)
                                                                                                                                                (popArgs avail reqr)) memodeb newavail reqret) avail)



mguPrograms, mguProgs :: (Search m) => Generator m CoreExpr
mguFuns :: (Search m) => Generator m CoreExpr

mguPrograms memodeb = applyDo (mguProgs memodeb)


mguProgs memodeb = wind (>>= (return . fmap (mapCE Lambda))) (lookupFunsShared mguFuns memodeb)
--mguProgs memodeb = wind (>>= (return . fmap Lambda)) (\avail reqret -> reorganize (\newavail -> lookupFunsPoly mguFuns memodeb newavail reqret) avail)
{- どっちがわかりやすいかは不明
mguProgs memodeb avail (t0:->t1) = do result <- mguProgs memodeb (t0 : avail) t1
                                      return (fmap Lambda result)
mguProgs memodeb avail reqret = reorganize (\newavail -> lookupFunsPoly mguFuns memodeb newavail reqret) avail
-}

mguFuns memodeb = generateFuns  mguPrograms memodeb

-- MemoDebの型が違うと使えない．
generateFuns :: (Search m) =>
                Generator m CoreExpr                               -- ^ recursive call
                -> Generator m CoreExpr
generateFuns rec memodeb@(CL classLib, _mt, (primgen,primmono),cmn) avail reqret
    = let clbehalf  = mguPrograms classLib []
          behalf    = rec memodeb avail
          lltbehalf = lookupListrie (opt cmn) rec memodeb avail -- heuristic filtration
          lenavails = genericLength avail
--          fe :: Type -> Type -> [CoreExpr] -> [CoreExpr] -- ^ heuristic filtration
          fe        = filtExprs (guess $ opt cmn)
          rg        =    if tv0 $ opt cmn then retGenTV0 else
                      if tv1 $ opt cmn then retGenTV1 else retGen
      in fromAssumptions cmn lenavails behalf mguPS reqret avail `mplus` mapSum (rg cmn lenavails fe clbehalf lltbehalf behalf reqret) primgen `mplus` mapSum (retPrimMono cmn lenavails clbehalf lltbehalf behalf mguPS reqret) primmono

lookupListrie opt rec memodeb avail t
--                      | constrL opt = mguAssumptions t avail
                      | guess opt = do args <- rec memodeb avail t
                                       let args' = filter (not.isClosed.toCE) args
                                       when (null args') mzero
                                       return args'
                      | otherwise = do args <- rec memodeb avail t
                                       let args' = filter (not.isConstrExpr.toCE) args
                                       when (null args') mzero
                                       return args'

\end{code}
