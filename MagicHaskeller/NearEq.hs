module MagicHaskeller.NearEq where
import MagicHaskeller.FastRatio

infix 4 ~=   -- same as (==)

-- the nearly-equal operator with pattern-matching-like behavior over NaN and Infinity.
class NearEq a where
  (~=) :: a -> a -> Bool

-- Without check with isInfinite, Infinity ~= something would always be True. Without check with signum, Infinity ~= -Infinity would always be True.
instance NearEq Double where
         a ~= b = na==nb && ia == isInfinite b && signum a == signum b && (na || ia || abs (a-b) <= (scaleFloat (-24) $ abs a))
              where na = isNaN a
                    nb = isNaN b
                    ia = isInfinite a
instance NearEq Float where
         a ~= b = na==nb && ia == isInfinite b && signum a == signum b && (na || ia || abs (a-b) <= (scaleFloat (-12) $ abs a))
              where na = isNaN a
                    nb = isNaN b
                    ia = isInfinite a
instance NearEq () where
  x ~= y = x == y
instance NearEq Bool where
  x ~= y = x == y
instance NearEq Ordering where
  x ~= y = x == y
instance NearEq Char where
  x ~= y = x == y
instance NearEq Int where
  x ~= y = x == y
instance NearEq Integer where
  x ~= y = x == y
instance (NearEq i, Integral i) => NearEq (Ratio i) where
  x ~= y = numerator x ~= numerator y && denominator x ~= denominator y
instance NearEq a => NearEq [a] where
  []   ~= []   = True
  x:xs ~= y:ys = x ~= y && xs ~= ys
  _    ~= _    = False
instance NearEq a => NearEq (Maybe a) where
  Nothing ~= Nothing = True
  Just x  ~= Just y  = x ~= y
  _       ~= _       = False
instance (NearEq a, NearEq b) => NearEq (Either a b) where
  Left  x ~= Left  y = x ~= y
  Right x ~= Right y = x ~= y
  _       ~= _       = False
instance (NearEq a, NearEq b) => NearEq (a,b) where
  (x1,x2) ~= (y1,y2) = x1 ~= y1 && x2 ~= y2
instance (NearEq a, NearEq b, NearEq c) => NearEq (a,b,c) where
  (x1,x2,x3) ~= (y1,y2,y3) = x1 ~= y1 && x2 ~= y2 && x3 ~= y3
