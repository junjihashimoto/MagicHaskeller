{-# LANGUAGE DeriveDataTypeable, CPP #-}
module MagicHaskeller.FastRatio where
#if __GLASGOW_HASKELL__ >= 706
import Prelude hiding(Ratio, Rational, (%))
#else
import Prelude hiding(Rational)
#endif
import qualified Data.Ratio
import Data.Typeable
import Data.Bits
-- import Test.QuickCheck hiding (choose)
-- import GHC.Integer.GMP.Internals

-- So, the integral type is totally ignored!
data Ratio a = !Integer :% !Integer deriving Typeable

type Rational = Ratio Integer

(%) :: Integral a => a -> a -> Ratio a
x % y = toInteger x :% toInteger y
numerator, denominator :: Integral a => Ratio a -> a
numerator   (n:%d) = let (n':%_ ) = reduce n d in fromInteger $ n' * signum d
denominator (n:%d) = let (_ :%d') = reduce n d in fromInteger $ abs d'

notANumber = 0:%0

reduce _ 0 = notANumber
reduce x y = (x `quot` d) :% (y `quot` d)
  where d = gcd x y

choose :: Ratio a -> Ratio a
-- choose = id

choose v@(n:%d) = if (abs n .|. abs d) > 0x3FFFFFFFFFFFFFFF then 
                    reduce n d else v

instance Ord (Ratio a)  where
  x:%y <= x':%y' =  case compare 0 $ y * y' of 
                          EQ -> False
                          LT -> x * y' <= x' * y
                          GT -> x * y' >= x' * y
  x:%y <  x':%y' =  case compare 0 $ y * y' of 
                          EQ -> False
                          LT -> x * y' <  x' * y
                          GT -> x * y' >  x' * y
  compare (x:%y) (x':%y') = case compare 0 $ y * y' of 
                              EQ -> EQ -- This conflicts the definition of (==) and (<=).
                                       -- compare is used for the random-testing filters, while (==) is used by the predicate filter.
                                       -- (But actually, compare is also used for the sortBy....)
                              LT -> compare (x * y')  (x' * y)
                              GT -> compare (x' * y)  (x * y')
  
instance Eq (Ratio a)  where
  x:%y == x':%y' = (y * y') /= 0 && x*y' == x'*y
  x:%y /= x':%y' = (y * y') /= 0 && x*y' /= x'*y

instance Integral a => Num (Ratio a)  where
  (x:%y) + (x':%y') = choose $ (x*y' + x'*y) :% (y*y')
  (x:%y) - (x':%y') = choose $ (x*y' - x'*y) :% (y*y')
  (x:%y) * (x':%y') = choose $ (x * x')      :% (y*y')
  negate     (x:%y) = (-x):%y
  abs        (x:%y) = abs x :% abs y
  signum     (x:%0) = notANumber
  signum     (x:%y) = signum (x * y) :% 1
  fromInteger x     =  fromInteger x :% 1

instance Integral a => Fractional (Ratio a)  where
  x:%y / x':%y' = if y' == 0 then notANumber else choose $ (x*y') :% (y*x')
  recip (x:%y) | y == 0    = notANumber
               | otherwise = y:%x
  fromRational r = Data.Ratio.numerator r :% Data.Ratio.denominator r

instance Integral a => RealFrac (Ratio a)  where
  properFraction (x:%y) = (fromInteger q, r :% y)
    where (q,r) = quotRem x y

instance (Show a, Integral a) => Show (Ratio a)  where
    showsPrec p r
      =  showParen (p > 7) $
         showsPrec 8 (numerator r) .
         showString " % " .
         showsPrec 8 (denominator r)
instance Integral a => Real (Ratio a) where
    toRational (x:%y) = x Data.Ratio.% y

instance Integral a => Enum (Ratio a)  where
    succ x              =  x + 1
    pred x              =  x - 1

    toEnum n            =  fromIntegral n :% 1
    fromEnum            =  fromInteger . truncate
{-
    enumFrom            =  numericEnumFrom
    enumFromThen        =  numericEnumFromThen
    enumFromTo          =  numericEnumFromTo
    enumFromThenTo      =  numericEnumFromThenTo
-}

{- properties held. 
prop_LE a b c d = c/=0 && d/=0 ==> let r1 = a%c <= b%d
                                       r2 = a Data.Ratio.% c <= b Data.Ratio.% d
                                   in r1 == r2
prop_LT a b c d = c/=0 && d/=0 ==> let r1 = a%c < b%d
                                       r2 = a Data.Ratio.% c < b Data.Ratio.% d
                                   in r1 == r2
prop_EQ a b c d = c/=0 && d/=0 ==> let r1 = a%c == b%d
                                       r2 = a Data.Ratio.% c == b Data.Ratio.% d
                                   in r1 == r2

prop_plus a b c d = c/=0 && d/=0 ==> let r1 = a%c + b%d
                                         r2 = a Data.Ratio.% c + b Data.Ratio.% d
                                     in toRational r1 == r2
prop_minus a b c d = c/=0 && d/=0 ==> let r1 = a%c - b%d
                                          r2 = a Data.Ratio.% c - b Data.Ratio.% d
                                      in r1 == fromRational r2
prop_times a b c d = c/=0 && d/=0 ==> let r1 = a%c * b%d
                                          r2 = (a Data.Ratio.% c) * (b Data.Ratio.% d)
                                     in numerator r1 == Data.Ratio.numerator r2 && denominator r1 == Data.Ratio.denominator r2
prop_negate a b = b/=0 ==> let r1 = negate $ a%b
                               r2 = negate $ a Data.Ratio.% b
                           in numerator r1 == Data.Ratio.numerator r2 && denominator r1 == Data.Ratio.denominator r2
prop_abs a b = b/=0 ==> let r1 = abs $ a%b
                            r2 = abs $ a Data.Ratio.% b
                        in numerator r1 == Data.Ratio.numerator r2 && denominator r1 == Data.Ratio.denominator r2
prop_signum a b = b/=0 ==> let r1 = signum $ a%b
                               r2 = signum $ a Data.Ratio.% b
                           in numerator r1 == Data.Ratio.numerator r2 && denominator r1 == Data.Ratio.denominator r2
prop_fromInteger a b = let r1 = fromInteger a
                           r2 = fromInteger a
                       in numerator r1 == Data.Ratio.numerator r2 && denominator r1 == Data.Ratio.denominator r2

prop_div a b c d = b/=0 && c/=0 && d/=0 ==> let r1 = a%c / b%d
                                                r2 = (a Data.Ratio.% c) / (b Data.Ratio.% d)
                                            in numerator r1 == Data.Ratio.numerator r2 && denominator r1 == Data.Ratio.denominator r2
prop_recip a b = a/=0 && b/=0 ==> let r1 = recip $ a%b
                                      r2 = recip $ a Data.Ratio.% b
                                  in numerator r1 == Data.Ratio.numerator r2 && denominator r1 == Data.Ratio.denominator r2
prop_properFraction a b = b/=0 ==> let (i1,r1) = properFraction $ a%b
                                       (i2,r2) = properFraction $ a Data.Ratio.% b
                                   in i1 == i2 && numerator r1 == Data.Ratio.numerator r2 && denominator r1 == Data.Ratio.denominator r2
prop_showsPrec p a b = b/=0 ==> let  r1 = showsPrec p $ a%b
                                     r2 = showsPrec p $ a Data.Ratio.% b
                                 in r1 [] == r2 []
-}