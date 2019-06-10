-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE CPP, RankNTypes #-}
module Data.Memo where
import Data.Char(ord,chr)
import Data.Bits
import Data.Array

import Data.List(sort) -- just for testing the efficiency

import Language.Haskell.TH

-- This could be a separate module.
#if QUICKCHECK>=2
import Test.QuickCheck.Function
#endif
#ifdef QUICKCHECK
import Test.QuickCheck
#else
infixr 0 ==>
type Property = Bool
(==>) = (<=)
#endif
#if QUICKCHECK>=2
#else
type Function = (->)
getFunction = id
#endif

newtype MapUnit a = MU a -- equivalent to Control.Monad.Identity.Identity
memoUnit :: (() -> a) -> MapUnit a
memoUnit f = MU (f ())
appUnit  :: MapUnit a -> (()->a)
appUnit (MU x) _ = x -- Should I write () instead of _ to make it strict?

data MapBool a = MB a a
memoBool :: (Bool->a) -> MapBool a
memoBool f = MB (f False) (f True)
appBool  :: MapBool a -> (Bool -> a)
appBool  (MB f t) False = f
appBool  (MB f t) True  = t

prop_inverseBool :: Bool -> Function Bool Int -> Bool
prop_inverseBool b f = appBool (memoBool (getFunction f)) b == getFunction f b

data MapOrdering a = MO a a a
memoOrdering :: (Ordering->a) -> MapOrdering a
memoOrdering f = MO (f LT) (f EQ) (f GT)
appOrdering  :: MapOrdering a -> Ordering->a
appOrdering  (MO l e g) LT = l
appOrdering  (MO l e g) EQ = e
appOrdering  (MO l e g) GT = g

data MapMaybe m a = MM a (m a)
memoMaybe :: ((b->a)->m a) -> (Maybe b -> a) -> MapMaybe m a
memoMaybe g f = MM (f Nothing) (g (\b -> f (Just b)))
appMaybe  :: (m a->(b->a)) -> MapMaybe m a -> (Maybe b -> a)
appMaybe  _ (MM n _) Nothing  = n
appMaybe  g (MM _ j) (Just x) = g j x
prop_inverseMaybe :: Maybe Ordering -> (Maybe Ordering -> Integer) -> Bool
prop_inverseMaybe mb f = appMaybe appOrdering (memoMaybe memoOrdering f) mb == f mb

data MapEither m n a = ME (m a) (n a)
memoEither :: ((b->a) -> m a) -> ((d->a) -> n a) -> (Either b d -> a) -> MapEither m n a
memoEither g h f = ME (g (\b -> f (Left b))) (h (\d -> f (Right d)))
appEither  :: (m a -> (b->a)) -> (n a -> (d->a)) -> MapEither m n a -> (Either b d -> a)
appEither  g _ (ME l _) (Left  x) = g l x
appEither  _ h (ME _ r) (Right x) = h r x
prop_inverseEither :: Either Int [Bool] -> (Either Int [Bool] -> Integer) -> Bool
prop_inverseEither e f = appEither appIntegral (appFiniteList appBool) (memoEither memoIntegral (memoFiniteList memoBool) f) e == f e

newtype MapPair m n a = MP (m (n a))
memoPair   :: (forall e. (b->e) -> m e) -> (forall f. (d->f) -> n f) -> ((b,d) -> a) -> MapPair m n a
memoPair   g h f = MP $ g (\b -> h (\d -> f (b,d)))
appPair    :: (forall e. m e -> (b->e)) -> (forall f. n f -> (d->f)) -> MapPair m n a -> ((b,d) -> a)
appPair    g h (MP m) (x,y) = h (g m x) y

type MapTriplet l m n = MapPair (MapPair l m) n
memoTriplet :: (forall e. (b->e) -> l e) ->
               (forall e. (c->e) -> m e) ->
               (forall e. (d->e) -> n e) -> ((b,c,d) -> a) -> MapTriplet l m n a
memoTriplet g h i f = memoPair (memoPair g h) i (\((x,y),z) -> f (x,y,z))
appTriplet  ::  (forall e. l e -> (b->e)) -> (forall e. m e -> (c->e)) -> (forall e. n e -> (d->e)) -> MapTriplet l m n a -> ((b,c,d) -> a)
appTriplet  g h i m (x,y,z) = appPair (appPair g h) i m ((x,y),z)
prop_inverseTriplet :: (Int,[Bool],[Int]) -> ((Int,[Bool],[Int]) -> Integer) -> Bool
prop_inverseTriplet t f = appTriplet appIntegral (appList 5 appBool) (appList 5 appIntegral) (memoTriplet memoIntegral (memoList memoBool) (memoList memoIntegral) f) t == f t

-- | MapList m a is a memoization of |[b]->a|, where m c is the memoization of b->c. Because we cannot memoize functions taking infinite lists (and long lists practically), functions are silently recomputed if the length if its argument list is more than the length limit.
data MapList m b a = ML (MapFiniteList m a) ([b]->a)
data MapFiniteList m a = MFL {
      nilArrow  :: a,
      consArrow :: m (MapFiniteList m a)
    }
memoList   :: (forall c. (b->c) -> m c) -> ([b] -> a) -> MapList m b a
memoList   g f = ML (memoFiniteList g f) f
appList10 = appList 10
appList5  = appList 5
appList3  = appList 3
appList1  = appList 1
appList    :: Int -- ^ length limit
              -> (forall c. m c -> (b->c)) -> MapList m b a -> ([b]->a)
appList    lenlim g (ML m f) xs | xs `isLongerThan` lenlim = f xs
                                | otherwise                = appFiniteList g m xs
memoFiniteList   :: (forall c. (b->c) -> m c) -> ([b] -> a) -> MapFiniteList m a
memoFiniteList   g f = MFL (f []) (g (\b -> memoFiniteList g (\bs -> f (b:bs))))
appFiniteList    :: (forall c. m c -> (b->c)) -> MapFiniteList m a -> ([b]->a)
appFiniteList    _ (MFL n _) []     = n
appFiniteList    g (MFL _ c) (x:xs) = appFiniteList g (g c x) xs

xs     `isLongerThan` n | n<0 = True
[]     `isLongerThan` n = False
(x:xs) `isLongerThan` n = xs `isLongerThan` (n-1)

prop_inverseList :: [Int] -> (Function [Int] Integer) -> Bool
prop_inverseList xs f = appList 5 appIntegral (memoList memoIntegral (getFunction f)) xs == getFunction f xs
prop_inverseListB :: [Bool] -> (Function [Bool] Integer) -> Bool
prop_inverseListB xs f = appList 5 appBool (memoList memoBool (getFunction f)) xs == getFunction f xs

type MapInteger = MapLargeIntegral Integer
memoInteger :: (Integer->a) -> MapInteger a
memoInteger = memoLargeIntegral
appInteger  :: MapInteger a -> Integer->a
appInteger  = appLargeIntegral (fromIntegral (minBound::Int), fromIntegral (maxBound::Int))
data MapLargeIntegral i a = MLI (MapIntegral a) (i->a)
memoLargeIntegral :: (Bits i, Num i) => (i->a) -> MapLargeIntegral i a
memoLargeIntegral f = MLI (memoIntegral f) f
appLargeIntegral  :: (Bits i, Ord i, Num i) => (i,i) -- ^ range
                                   -> MapLargeIntegral i a -> i->a
appLargeIntegral (minb,maxb) (MLI mi f) i | minb <= i && i <= maxb = appIntegral mi i
                                          | otherwise              = f i
type MapInt = MapIntegral
memoInt :: (Int->a) -> MapInt a
memoInt = memoIntegral
appInt  :: MapInt a -> Int->a
appInt  = appIntegral
data MapIntegral a = MI {
      negArrow    :: MapNat a,
      nonnegArrow :: MapNat a
    }
type MapNat = MapFiniteList MapBool
memoIntegral :: (Bits i, Num i) => (i -> a) -> MapIntegral a
memoIntegral f = MI (memoPosNat (\n -> f (-n))) (memoPosNat (\n -> f (n-1)))
memoPosNat f = memoFiniteList memoBool (\bs -> f (bitsToPosNat bs))
bitsToPosNat [] = 1
bitsToPosNat (b:bs) | b         = gbs .|. 1
                    | otherwise = gbs
                    where gbs = bitsToPosNat bs `shiftL` 1
appIntegral :: (Bits i, Num i) => MapIntegral a -> (i->a)
appIntegral (MI n nn) i | signum i == -1 = appPosNat n  (-i)
                        | otherwise      = appPosNat nn (i+1)
appPosNat m i = appFiniteList appBool m (posNatToBits i)
posNatToBits 1 = []
posNatToBits n = (n `testBit` 0) : posNatToBits (n `shiftR` 1)
-- Another option is just to use a list as MapNat, and not to memoize when the argument is huge. This might be better if it is unlikely such large keys are visited again.
-- Patricia tree cannot be used for building an infinite tree.
prop_inverseIntegral :: Integer -> (Function Integer Integer) -> Bool
prop_inverseIntegral i f = appLargeIntegral (-2^28,2^28) (memoLargeIntegral (getFunction f)) i == getFunction f i
prop_inversePosNat :: Int -> Function Int Int -> Property
prop_inversePosNat n f = n>0 ==> appPosNat (memoPosNat (getFunction f)) n == getFunction f n
prop_bitsToFromPosNat :: [Bool]->Bool
prop_bitsToFromPosNat is = posNatToBits (bitsToPosNat is::Integer) == is -- IntegerでなくIntにすると通らない．

memoIx10, memoIx3 :: (Integral i, Ix i) => (i->a) -> MapIx i a
memoIx10 = memoIx (0,10)
memoIx3  = memoIx (0,3)

data MapIx i a = MIx (Array i a) (i->a)
memoIx :: (Ix i) => (i,i) -> (i->a) -> MapIx i a
memoIx bnds f = MIx (listArray bnds (map f (range bnds))) f
appIx  :: (Ix i) => MapIx i a -> i->a
appIx  (MIx ar f) i | bounds ar `inRange` i = ar!i
                    | otherwise             = f i

type MapChar = MapIntegral
memoChar :: (Char->a) -> MapChar a
memoChar f = memoIntegral (\i -> f $ chr i)
appChar :: MapChar a -> (Char->a)
appChar mi c = appIntegral mi (ord c)
prp_inverseChar c f = appChar (memoChar f) c == (f c::Int)

type MapReal = MapPair MapIntegral MapIntegral
memoReal :: RealFloat r => (r -> a) -> MapReal a
memoReal f = memoPair memoIntegral memoIntegral (f . uncurry encodeFloat)
appReal  :: RealFloat r => MapReal a -> r -> a
appReal mt r = appPair appIntegral appIntegral mt (decodeFloat r)

prop_inverseReal :: Double -> (Double->Int) -> Bool
prop_inverseReal r f = appReal (memoReal f) r == f r


-- test code for seeing if memoization really works
heavy, memoizedHeavy :: Integer -> Integer
heavy n = 3^n `div` 3^(n-1)
memoHeavy = memoIntegral heavy
memoizedHeavy = appIntegral memoHeavy

heavy2, memoizedHeavy2 :: Integer -> Integer -> Integer
heavy2 m n = m^n `div` m^(n-1)
memoHeavy2 = memoIntegral ((.) memoIntegral heavy2)
memoizedHeavy2 = (.) appIntegral (appIntegral memoHeavy2)

memoizedHeavy2' :: Integer -> Integer -> Integer
memoHeavy2' = memoPair memoIntegral memoIntegral (uncurry heavy2)
memoizedHeavy2' = curry $ appPair appIntegral appIntegral memoHeavy2'

heavy3, memoizedHeavy3 :: Integer -> Integer -> Integer -> Integer
heavy3 l m n = l^n `div` m^(n-1)
-- memoHeavy3 = memoIntegral ((.) memoIntegral ((.) ((.) memoIntegral) heavy3))
memoHeavy3 = (memoIntegral . (.) (memoIntegral . (.) memoIntegral)) heavy3
-- memoizedHeavy3 = (.) ((.) appIntegral) ((.) appIntegral (appIntegral memoHeavy3))
memoizedHeavy3 = ((.) ((.) appIntegral . appIntegral) . appIntegral) memoHeavy3


heavyList, memoizedHeavyList :: String -> String
heavyList xs = take 10 $ reverse $ sort $ take 1000000 $ cycle xs
memoHeavyList = memoFiniteList memoChar heavyList
memoizedHeavyList = appFiniteList appChar memoHeavyList
