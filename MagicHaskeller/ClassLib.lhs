-- 
-- (c) Susumu Katayama
--
\begin{code}
module MagicHaskeller.ClassLib(mkCL, ClassLib(..), mguPrograms) where

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

import MagicHaskeller.Classify
import MagicHaskeller.Instantiate

import MagicHaskeller.Expression

import MagicHaskeller.T10

import MagicHaskeller.DebMT

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


newtype ClassLib e = CL (MemoDeb e)

type MemoTrie a = MapType (BFM (Possibility a))

lmt mt fty =
       traceTy fty $
       lookupMT mt fty

lookupFunsPoly :: (Search m, Expression e) => Generator m e -> Generator m e
lookupFunsPoly behalf memodeb@(mt,_,cmn) reqret
    = PS (\subst mx ->
              let (tn, decoder) = encode reqret mx
              in -- ifDepth (<= memodepth (opt cmn))
                         (fmap (\ (exprs, sub, m) -> (exprs, retrieve decoder sub `plusSubst` subst, mx+m)) $ fromMemo $ lmt mt tn)
                 --        (unPS (behalf memodeb reqret) subst mx) 
         )
                         -- 条件によって再計算したいときはuncommentすべし。メモりは食わないはずなので、常にmemoizeで問題ないはず。

type MemoDeb a = (MemoTrie a, [[Prim]], Common)

mkCL :: Expression e => Common -> [Typed [CoreExpr]] -> ClassLib e
mkCL cmn classes = CL $ mkTrieMD [map annotateTCEs classes] cmn
mkTrieMD :: (Expression e) => [[Prim]] -> Common -> MemoDeb e
mkTrieMD qtl cmn
    = let trie = mkMT (tcl cmn) (\ty -> fromRc (freezePS ty (mguFuns memoDeb ty)))
          memoDeb = (trie,qtl,cmn)
      in memoDeb

-- moved from DebMT.lhs to avoid cyclic modules.
freezePS :: (Search m, Expression e) => Type -> PriorSubsts m (Bag e) -> m (Possibility e)
freezePS ty ps
    = let mxty = maxVarID ty -- `max` maximum (map maxVarID avail)
      in mergesortDepthWithBy (\(xs,k,i) (ys,_,_) -> (xs `mappend` ys, k, i)) (\(_,k,_) (_,l,_) -> k `compare` l) $ fps mxty ps
fps :: (Search m, Expression e) => TyVar -> PriorSubsts m [e] -> m ([e],[(TyVar, Type)],TyVar)
fps mxty (PS f) = do
                     (es, sub, m) <- f emptySubst (mxty+1)
                     guard $ not $ length es `seq` null es
                     return (es, filterSubst sub mxty, m)
    where filterSubst :: Subst -> TyVar -> [(TyVar, Type)]
          filterSubst sub  mx = [ t | t@(i,_) <- sub, inRange (0,mx) i ] -- note that the assoc list is NOT sorted.


type Generator m e = MemoDeb e -> Type -> PriorSubsts m [e]


mguPrograms, mguFuns :: (Search m, Expression e) => Generator m e
mguPrograms memodeb ty = do subst <- getSubst
                            lookupFunsPoly mguFuns memodeb (apply subst ty)
mguFuns memodeb = generateFuns  mguPrograms memodeb

-- MemoDebの型が違うと使えない．
generateFuns :: (Search m, Expression e) =>
                Generator m e                            -- ^ recursive call
                -> Generator m e
generateFuns rec memodeb@(_mt, primmono,cmn) reqret
    = let clbehalf  = error "generateFuns: cannot happen."
          behalf    = rec memodeb
          lltbehalf = error "generateFuns: cannot happen."
          lenavails = 0
      in mapSum (retPrimMono cmn lenavails clbehalf lltbehalf behalf mguPS reqret) primmono

\end{code}
