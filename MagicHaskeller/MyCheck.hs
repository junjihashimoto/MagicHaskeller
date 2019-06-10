-- 
-- (c) Susumu Katayama
--
{-
rewrite of QuickCheck.Arbitrary in the form specialized for each type
@inproceedings{QuickCheck,
        AUTHOR = "Koen Claessen and John Hughes",
        TITLE  = "{QuickCheck}: a lightweight tool for random testing of {Haskell} programs",
        BOOKTITLE = "ICFP'00: Proceedings of the 5th ACM SIGPLAN International Conference on Functional Programming",
        PAGES  = "268-279",
        ORGANIZATION = "ACM",
        YEAR = 2000 }
The original source is released under BSD-style license.
I (Susumu) reimplemented this because QuickCheck-1 had (and has?) some bugs and QuickCheck-2 was not released, but 
maybe I could import and reuse definitions of Arbitrary of QuickCheck-2.
(But still I am interested in using different generator than StdGen.)
-}
{-# LANGUAGE CPP #-}
module MagicHaskeller.MyCheck where
#ifdef TFRANDOM
import System.Random.TF.Gen
import System.Random.TF.Instances
#else
import System.Random
#endif
import Control.Monad(liftM, liftM2, liftM3, ap)
import Control.Applicative -- necessary for backward compatibility
import Data.Char(ord,chr)
-- import Data.Ratio
import MagicHaskeller.FastRatio
import Prelude hiding (Rational)

-- for bit hacks. Should such stuff be in a different module?
import qualified Data.ByteString as BS
import Data.Word
import Data.Bits

#ifdef TFRANDOM
newtype Gen a = Gen {unGen :: Int -> TFGen -> a}
#else
newtype Gen a = Gen {unGen :: Int -> StdGen -> a}
#endif
type Coarb a b = a -> Gen b -> Gen b

sized :: (Int -> Gen a) -> Gen a
sized fgen = Gen $ \n g -> unGen (fgen n) n g

instance Functor Gen where
    fmap = liftM
instance Applicative Gen where
    pure a = Gen $ \_ _ -> a
    (<*>)  = ap
instance Monad Gen where
    return      = pure
    Gen m >>= k = Gen $ \n g -> case split g of (g1,g2) -> unGen (k (m n g1)) n g2

arbitraryR :: Random a => (a, a) -> Gen a
arbitraryR bnds = Gen $ \ _ gen -> fst $ randomR bnds gen
-- arbitrary :: (Random a, Bounded a) => Gen a
-- arbitrary = arbitraryR (minBound, maxBound)

arbitraryUnit :: Gen ()
arbitraryUnit = return ()
coarbitraryUnit :: Coarb () b
coarbitraryUnit _ = id

arbitraryBool :: Gen Bool
arbitraryBool = arbitraryR (False,True)
coarbitraryBool :: Coarb Bool b
-- coarbitraryBool b = if b then variant 0 else variant 1
coarbitraryBool b (Gen f) = Gen $ \size stdgen -> f size $ case split stdgen of (g0,g1) -> if b then g0 else g1

arbitraryInt :: Gen Int
arbitraryInt = arbitraryIntegral
coarbitraryInt :: Coarb Int b
coarbitraryInt n = newvariant n

arbitraryInteger :: Gen Integer
arbitraryInteger = arbitraryIntegral
coarbitraryInteger :: Coarb Integer b
coarbitraryInteger n = newvariant n

arbitraryIntegral :: (Random i, Integral i) => Gen i
arbitraryIntegral = sized $ \n -> arbitraryR ( - fromIntegral n,  fromIntegral n )

-- variant of Test.QuickCheck.variant using divide-and-conquer
logvariant, newvariant :: (Bits i, Integral i) => i -> Gen a -> Gen a
logvariant 0 = coarbitraryBool True
#ifdef TFRANDOM
logvariant n | n > 0 = coarbitraryBool False . logvariant (n `shiftR` 32) . coarbitraryBits 32 (n .&. 0xFFFFFFFF)
#else
logvariant n | n > 0 = coarbitraryBool False . logvariant (n `div` 2) . coarbitraryBool (n `mod` 2 == 0)
#endif
             | otherwise = error "logvariant: negative argument"
newvariant n | n >= 0    = coarbitraryBool True  . logvariant n
             | otherwise = coarbitraryBool False . logvariant (-1-n)

#ifdef TFRANDOM
coarbitraryBits b n (Gen f) = Gen $ \size gen -> f size $ splitn gen b $ fromIntegral n
#endif

arbitraryFloat :: Gen Float
arbitraryFloat = arbitraryRealFloat
arbitraryDouble :: Gen Double
arbitraryDouble = arbitraryRealFloat

coarbitraryFloat :: Coarb Float b
coarbitraryFloat = coarbitraryRealFloat
coarbitraryDouble :: Coarb Double b
coarbitraryDouble = coarbitraryRealFloat

fraction a b c = fromInteger a + (fromInteger b / (abs (fromInteger c) + 1))

arbitraryRealFloat :: RealFloat a => Gen a
arbitraryRealFloat     = liftM3 fraction arbitraryInteger arbitraryInteger arbitraryInteger
coarbitraryRealFloat :: RealFloat a => Coarb a b
coarbitraryRealFloat x = let (sig, xpo) = decodeFloat x in newvariant sig . newvariant xpo

arbitraryChar = do r <- arbitraryR (0,11)
                   [arbNum, arbNum, arbASC, return '\n', return '\n', retSpc, retSpc, retSpc, arbLow, arbLow, arbUpp, arbUpp] !! r
retSpc = return ' ' 
arbASC = arbitraryR (' ', chr 126)
arbNum = arbitraryR ('0','9')
arbLow = arbitraryR ('a','z')
arbUpp = arbitraryR ('A','Z')
coarbitraryChar c = logvariant (ord c)

arbitraryOrdering :: Gen Ordering
arbitraryOrdering  = arbitraryR (0,2) >>= return . toEnum
-- Ordering is not an instance of Random!

-- For arbitraryRatio we need a type constraint anyway in order to deal with the div0 case, so we have to do something tricky.
arbitraryRatio :: (Random i, Integral i) => Gen (Ratio i)
arbitraryRatio = liftM2 (%) arbitraryIntegral (fmap (\x->1+abs x) arbitraryIntegral)

arbitraryMaybe    :: Gen a -> Gen (Maybe a)
arbitraryMaybe arb = do b <- arbitraryBool
                        if b then return Nothing else liftM Just arb

arbitraryList     :: Gen a -> Gen [a]
-- arbitraryList  arb = sized $ \n -> arbitraryR (0,n) >>= \n -> sequence $ replicate n arb -- This causes examples bloat rapidly in the case of deeply-nested lists, such as [[[[[[a]]]]]].
#ifdef TFRANDOM
arbitraryList  (Gen f) = sized $ \n -> arbitraryR (0,n) >>= \i -> sequenceSized (lg i + 1) $ replicate i (Gen $ \s g -> f (max 1 (lg s * k)) g)

sequenceSized :: Int -> [Gen a] -> Gen [a]
sequenceSized bits arbs = Gen $ \n g ->  zipWith (\(Gen m) g -> m n g) arbs $ map (splitn g bits) [0..]
#else
arbitraryList  (Gen f) = sized $ \n -> arbitraryR (0,n) >>= \i -> sequence $ replicate i (Gen $ \s g -> f (max 1 (lg s * k)) g)
#endif
k = 1

-- bitvector algorithm for computing log2, translated from http://graphics.stanford.edu/~seander/bithacks.html#IntegerLogDeBruijn.
-- maybe overkill?
lg :: (Integral a, Integral b) => a -> b
lg = fromIntegral . lg' . fromIntegral
lg' :: Word32 -> Word8
lg' v = let v2  = v   .|. (v   `unsafeShiftR` 1)
            v4  = v2  .|. (v2  `unsafeShiftR` 2)
            v8  = v4  .|. (v4  `unsafeShiftR` 4)
            v16 = v8  .|. (v8  `unsafeShiftR` 8)
            v32 = v16 .|. (v16 `unsafeShiftR` 16)
        in multiplyDeBruijnBitPosition `BS.index` fromIntegral ((v32 * 0x07C4ACDD) `unsafeShiftR` 27)
multiplyDeBruijnBitPosition :: BS.ByteString
multiplyDeBruijnBitPosition = BS.pack [ 0, 9, 1, 10, 13, 21, 2, 29, 11, 14, 16, 18, 22, 25, 3, 30, 8, 12, 20, 28, 15, 17, 24, 7, 19, 27, 23, 6, 26, 5, 4, 31 ]


arbitraryPair     :: Gen a -> Gen b -> Gen (a,b)
arbitraryPair      = liftM2 (,)

arbitraryEither   :: Gen a -> Gen b -> Gen (Either a b)
arbitraryEither arb0 arb1 = do b <- arbitraryBool
                               if b then liftM Left arb0 else liftM Right arb1

arbitraryTriplet  :: Gen a -> Gen b -> Gen c -> Gen (a,b,c)
arbitraryTriplet   = liftM3 (,,)

arbitraryFun :: Coarb a b -> Gen b -> Gen (a->b)
arbitraryFun coarb arb = Gen (\n r a -> unGen (coarb a arb) n r)

arbitraryRational :: Gen Rational
arbitraryRational = arbitrary


coarbitraryOrdering :: Coarb Ordering b
#ifdef TFRANDOM
coarbitraryOrdering = coarbitraryBits 2 . fromEnum
#else
coarbitraryOrdering x = case x of LT -> coarbitraryBool True
                                  EQ -> coarbitraryBool False . coarbitraryBool True
                                  GT -> coarbitraryBool False . coarbitraryBool False
#endif
coarbitraryList :: Coarb a b -> Coarb [a] b
coarbitraryList _     []     = coarbitraryBool True
coarbitraryList coarb (x:xs) = coarbitraryBool False . coarb x . coarbitraryList coarb xs

coarbitraryMaybe :: Coarb a b -> Coarb (Maybe a) b
coarbitraryMaybe _     Nothing  = coarbitraryBool True
coarbitraryMaybe coarb (Just x) = coarbitraryBool False . coarb x

coarbitraryEither :: Coarb a c -> Coarb b c -> Coarb (Either a b) c
coarbitraryEither coarb0 _      (Left x)  = coarbitraryBool True . coarb0 x
coarbitraryEither _      coarb1 (Right y) = coarbitraryBool False . coarb1 y

coarbitraryRatio :: (Bits a, Integral a) => Coarb (Ratio a) b
coarbitraryRatio r = newvariant (numerator r) . logvariant (denominator r)

coarbitraryPair :: Coarb a c -> Coarb b c -> Coarb (a,b) c
coarbitraryPair coarb0 coarb1 (a,b) = coarb0 a . coarb1 b

coarbitraryTriplet :: Coarb a d -> Coarb b d -> Coarb c d -> Coarb (a,b,c) d
coarbitraryTriplet coarb0 coarb1 coarb2 (a,b,c) = coarb0 a . coarb1 b . coarb2 c

coarbitraryFun :: Gen a -> Coarb b d -> Coarb (a->b) d
-- This is based on QuickCheck-1, and quite lightweight.
coarbitraryFun arb coarb f gen = arb >>= \x -> coarb (f x) gen

-- This is a definition based on QuickCheck-2:
-- coarbitraryFun arb coarb f gen = arbitraryList arb >>= \xs -> coarbitraryList coarb (map f xs) gen

-- This does even heavier check.
-- coarbitraryFun arb coarb f gen = (sized $ \n -> sequence $ replicate n arb) >>= \xs -> coarbitraryList coarb (map f xs) gen

class Arbitrary a where
    arbitrary   :: Gen a
class Coarbitrary a where
    coarbitrary :: a -> Gen b -> Gen b

instance Arbitrary () where
    arbitrary = arbitraryUnit
instance Coarbitrary () where
    coarbitrary = coarbitraryUnit

instance Arbitrary Bool where
    arbitrary = arbitraryBool
instance Coarbitrary Bool where
    coarbitrary = coarbitraryBool

instance Arbitrary Int where
    arbitrary = arbitraryInt
instance Coarbitrary Int where
    coarbitrary = coarbitraryInt

instance Arbitrary Integer where
    arbitrary = arbitraryInteger
instance Coarbitrary Integer where
    coarbitrary = coarbitraryInteger

instance Arbitrary Float where
    arbitrary = arbitraryFloat
instance Coarbitrary Float where
    coarbitrary = coarbitraryFloat

instance Arbitrary Double where
    arbitrary = arbitraryDouble
instance Coarbitrary Double where
    coarbitrary = coarbitraryDouble

instance Arbitrary Char where
    arbitrary = arbitraryChar
instance Coarbitrary Char where
    coarbitrary = coarbitraryChar

instance Arbitrary Ordering where
    arbitrary = arbitraryOrdering
instance Coarbitrary Ordering where
    coarbitrary = coarbitraryOrdering

instance Arbitrary a => Arbitrary (Maybe a) where
    arbitrary = arbitraryMaybe arbitrary
instance Coarbitrary a => Coarbitrary (Maybe a) where
    coarbitrary = coarbitraryMaybe coarbitrary

instance Arbitrary a => Arbitrary [a] where
    arbitrary = arbitraryList arbitrary
instance Coarbitrary a => Coarbitrary [a] where
    coarbitrary = coarbitraryList coarbitrary

instance (Arbitrary a, Arbitrary b) => Arbitrary (a,b) where
    arbitrary = arbitraryPair arbitrary arbitrary
instance (Coarbitrary a, Coarbitrary b) => Coarbitrary (a,b) where
    coarbitrary = coarbitraryPair coarbitrary coarbitrary

instance (Arbitrary a, Arbitrary b) => Arbitrary (Either a b) where
    arbitrary = arbitraryEither arbitrary arbitrary
instance (Coarbitrary a, Coarbitrary b) => Coarbitrary (Either a b) where
    coarbitrary = coarbitraryEither coarbitrary coarbitrary

instance (Arbitrary a, Arbitrary b, Arbitrary c) => Arbitrary (a,b,c) where
    arbitrary = arbitraryTriplet arbitrary arbitrary arbitrary
instance (Coarbitrary a, Coarbitrary b, Coarbitrary c) => Coarbitrary (a,b,c) where
    coarbitrary = coarbitraryTriplet coarbitrary coarbitrary coarbitrary

instance  (Coarbitrary a, Arbitrary b) => Arbitrary (a->b) where
    arbitrary = arbitraryFun coarbitrary arbitrary
instance  (Arbitrary a, Coarbitrary b) => Coarbitrary (a->b) where
    coarbitrary = coarbitraryFun arbitrary coarbitrary

instance (Integral i, Random i) => Arbitrary (Ratio i) where
    arbitrary  = arbitraryRatio
instance (Integral i, Bits i) => Coarbitrary (Ratio i) where
    coarbitrary = coarbitraryRatio
