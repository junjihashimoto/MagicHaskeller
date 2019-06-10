further simplified from ~/svn/MagicHaskeller/allifdefs/FMType.lhs

\begin{code}
{-# OPTIONS -cpp #-}
module MagicHaskeller.FMType(FMType(..), updateFMT, unionFMT, unitFMT, lookupFMT, fmtToList, eltsFMT,
              {- listToFMT, -} mapFMT
             ) where
import MagicHaskeller.Types
-- import Monad
import Data.IntMap as IM

-- import CoreLang

import Data.Monoid

data FMType a = EmptyFMT
              | FMT {
                     tvFMT :: IntMap a,
                     tcFMT :: IntMap a,
                     taFMT  :: (FMType (FMType a)),
                     fnFMT  :: (FMType (FMType a)),
                     funFMT :: (FMType (FMType a))
                    }
                deriving (Read, Show)

lookupFMT :: Type -> FMType a -> Maybe a
lookupFMT _ EmptyFMT = Nothing
lookupFMT (TV tv)     fmt = IM.lookup (fromIntegral tv) (tvFMT fmt)
lookupFMT (TC tc)     fmt = IM.lookup (fromIntegral tc) (tcFMT fmt)
lookupFMT (TA t0 t1)  fmt = lookupFMTFMT t0 t1 (taFMT fmt)
#ifdef RIGHTFMT
lookupFMT (t0 :>  t1) fmt = lookupFMTFMT t0 t1 (fnFMT fmt)
lookupFMT (t0 :-> t1) fmt = lookupFMTFMT t0 t1 (funFMT fmt)
#else
lookupFMT (t1 :>  t0) fmt = lookupFMTFMT t0 t1 (fnFMT fmt)
lookupFMT (t1 :-> t0) fmt = lookupFMTFMT t0 t1 (funFMT fmt)
#endif
lookupFMTFMT t0 t1 fmtfmt = lookupFMT t0 fmtfmt >>= lookupFMT t1

mapFMT :: (Type -> a -> b) -> FMType a -> FMType b -- takes the index as an argument, like mapFM, but currently only the structures of the types are considered. 
mapFMT f EmptyFMT = EmptyFMT
mapFMT f (FMT v c a n u) = FMT (mapWithKey (\tv -> f (TV $ fromIntegral tv)) v)
                               (mapWithKey (\tc -> f (TC $ fromIntegral tc)) c)
                               (mapFMT (\t0 -> mapFMT (\t1 -> f (TA t0 t1)))  a)
                               (mapFMT (\t0 -> mapFMT (\t1 -> f (t1 :> t0)))  n)
                               (mapFMT (\t0 -> mapFMT (\t1 -> f (t1 :-> t0))) u)

{- addToFMTとlistToFMTって何でコメントアウトしたんだっけ？ あと，normalizeしない方がよい？
addToFMT :: Typed a -> FMType a -> FMType a
addToFMT (e:::ty) = updateFMT (et:) et nty
    where nty = normalize ty
          et  = e:nty
listToFMT :: [Typed a] -> FMType a
listToFMT = foldr addToFMT EmptyFMT
-}


eltsFMT :: FMType a -> [a]
eltsFMT EmptyFMT = []
eltsFMT (FMT vs cs as fs fus) = elems vs ++ elems cs ++ [ x | fmt <- eltsFMT as, x <- eltsFMT fmt ] ++ [ x | fmt <- eltsFMT fs, x <- eltsFMT fmt ] ++ [ x | fmt <- eltsFMT fus, x <- eltsFMT fmt ]

{-
fmtToList :: FMType a -> [Typed a]
-- fmtToList = eltsFMT . mapFMT (\t a -> a:::t)
fmtToList EmptyFMT = []
fmtToList (FMT vs cs as fs fus) = fmToTypedVars vs ++ fmToTypedCons cs ++ [ x ::: TA t0 t1 | fmt:::t0 <- fmtToList as, x:::t1 <- fmtToList fmt ] ++ [ x ::: (t1 :> t0) | fmt:::t0 <- fmtToList fs, x:::t1 <- fmtToList fmt ] ++ [ x ::: (t1 :-> t0) | fmt:::t0 <- fmtToList fus, x:::t1 <- fmtToList fmt ]
fmToTypedVars fm = map (\ (tv,x) -> x ::: TV tv) (fmToList fm)
fmToTypedCons fm = map (\ (tc,x) -> x ::: TC tc) (fmToList fm)
-}
fmtToList :: FMType a -> [(Type,a)]
-- fmtToList = eltsFMT . mapFMT (\t a -> (t,a))
fmtToList EmptyFMT = []
fmtToList (FMT vs cs as fs fus) = fmToTypedVars vs ++ fmToTypedCons cs ++ [ (TA t0 t1, x) | (t0, fmt) <- fmtToList as, (t1,x) <- fmtToList fmt ] ++ [ (t1 :> t0, x) | (t0,fmt) <- fmtToList fs, (t1,x) <- fmtToList fmt ] ++ [ (t1 :-> t0, x) | (t0,fmt) <- fmtToList fus, (t1,x) <- fmtToList fmt ]
fmToTypedVars fm = Prelude.map (\ (tv,x) -> (TV $ fromIntegral tv, x)) (toList fm)
fmToTypedCons fm = Prelude.map (\ (tc,x) -> (TC $ fromIntegral tc, x)) (toList fm)

updateFMT :: (a->a) -> a -> Type -> (FMType a) -> FMType a
updateFMT f x t fmt = updFMT t fmt
    where updFMT t      EmptyFMT = updFMT t (FMT empty empty EmptyFMT EmptyFMT EmptyFMT)
          updFMT (TV gen)    fmt = fmt{tvFMT = insertWith (\_new old -> f old) (fromIntegral gen) x (tvFMT fmt)}
          updFMT (TC con)    fmt = fmt{tcFMT = insertWith (\_new old -> f old) (fromIntegral con) x (tcFMT fmt)}
          updFMT (TA t0 t1)  fmt = fmt{taFMT  = updateFMT updFMTt1 (updFMTt1 EmptyFMT) t0 (taFMT fmt)}
              where updFMTt1 = updFMT t1
          updFMT (t0 :> t1)  fmt = fmt{fnFMT  = updateFMT updFMTt0 (updFMTt0 EmptyFMT) t1 (fnFMT fmt)}
              where updFMTt0 = updFMT t0
          updFMT (t0 :-> t1) fmt = fmt{funFMT = updateFMT updFMTt0 (updFMTt0 EmptyFMT) t1 (funFMT fmt)}
              where updFMTt0 = updFMT t0

unitFMT x t = updateFMT undefined x t EmptyFMT
-- used by FMSubst.lhs

instance Monoid a => Monoid (FMType a) where
    mappend = unionFMT mappend
    mempty  = EmptyFMT

-- unionFMT is used by TypedTries.
unionFMT :: (a->a->a) -> FMType a -> FMType a -> FMType a
unionFMT f l r = uFMT l r
    where uFMT EmptyFMT fmt = fmt
          uFMT fmt EmptyFMT = fmt
          uFMT (FMT vl cl al nl ul) (FMT vr cr ar nr ur) = FMT (unionWith f vl vr) (unionWith f cl cr) (unionFMT uFMT al ar) (unionFMT uFMT nl nr) (unionFMT uFMT ul ur)
{-
unionFMT :: (forall a. a->a->a) -> FMType b -> FMType b -> FMType b
unionFMT f EmptyFMT fmt = fmt
unionFMT f fmt EmptyFMT = fmt
unionFMT f (FMT vl cl al nl ul) (FMT vr cr ar nr ur) = FMT (plusFM_C f vl vr) (plusFM_C f cl cr) (unionFMT (unionFMT f) al ar) (unionFMT (unionFMT f) nl nr) (unionFMT (unionFMT f) ul ur)
-}


\end{code}
