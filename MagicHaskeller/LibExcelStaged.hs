module MagicHaskeller.LibExcelStaged where
import MagicHaskeller
import Data.List
import Data.Char

default (Int, Integer, Double)

-- gcd in the latest library is total, but with older versions gcd 0 0 causes an error. 
totalGCD x y =  gcd' (abs x) (abs y)
  where gcd' a 0  =  a
        gcd' a b  =  gcd' b (a `rem` b)




curry2 = curry
curry3 :: ((a,b,c) -> d) -> a->b->c->d
curry3 f x y z = f(x,y,z)
curry4 :: ((a,b,c,d) -> e) -> a->b->c->d->e
curry4 f w x y z = f(w,x,y,z)
curry5 :: ((a,b,c,d,e) -> f) -> a->b->c->d->e->f
curry5 f v w x y z = f(v,w,x,y,z)
curry6 :: ((a,b,c,d,e,f) -> g) -> a->b->c->d->e->f->g
curry6 f u v w x y z = f(u,v,w,x,y,z)

{-
The Policy:
1. During synthesis, monomorphic types including Int and Double must be used by mkTrie &c.
2. fromIntegral and floor are available when synthesizing, but they are removed by ppExcel.
3. Because of 2., functions must be defined polymorphically here, or the generation of input-output examples by the CGI would cause type mismatch.
-}

iF :: (Bool, a, a) -> a
iF (True,  t, f) = t
iF (False, t, f) = f
upper = map toUpper
lower = map toLower
{- This definition unnecessarily trims the spaces.
proper = unwords . map proper' . words
proper' ""     = ""
proper' (h:ts) = toUpper h : map toLower ts
-}
-- I think the following definition is enough. PROPER capitalizes letters even after a hyphen or an apostrophe.
proper ""     = ""
proper (c:cs) | isAlpha c = toUpper c : case span isAlpha cs of (ts, ds) -> map toLower ts ++ proper ds
              | otherwise = c : proper cs

right, left :: ([b], Int) -> [b]
left1  = take 1
right1 str = right (str, 1)
left  (b, a)    = take a b
right (b, a)    = reverse (take a (reverse b))
dropLeft b a    = right(b, len(b) - a)
mid   (c, a, b) = take b (drop (a - 1) c)
len :: Num a => String -> a
len = fromIntegral . length
concatenate (a, b) = a ++ b
concatenatE (a,b,c) = a++b++c
concatenaTE (a,b,c,d) = a++b++c++d
concatenATE (a,b,c,d,e) = a++b++c++d++e
concateNATE (a,b,c,d,e,f) = a++b++c++d++e++f


{-
max = maximum
min= minimum
average= \a -> Prelude.sum a / fromIntegral (length a)
count= \a -> length (filter (/= 0) a)
sumif ms = Prelude.sum[x|Just x <- ms]
-}
cEILING, fLOOR, mround :: (Double, Double) -> Double
cEILING (_, 0) = 0
cEILING (a, b) = fromIntegral (Prelude.ceiling (a / b))*b
mround  (_, 0) = 0
mround  (a, b) = fromIntegral (Prelude.round   (a / b))*b
-- http://office.microsoft.com/en-us/excel-help/mround-HP005209185.aspx?CTT=5&origin=HP005204211

-- As for FLOOR, FLOOR(0,0) is 0, but FLOOR(x,0) is #DIV/0 for other x's. Also, if the second argument is negative, the result is $NUM.
-- Thus, we should prepare something different, defining  \a b -> IF(b > 0, FLOOR(a,b), 0).
-- The postprocessor expands it to FLOOR(a,b) if b is known to be positive.
fLOOR0 a b | b <= 0    = 0
           | otherwise = fromIntegral (Prelude.floor   (a / b))*b
 
-- We need fLOOR in order to generate I/O examples. This definition is not exact, but it alerts anyway if its second argument is not positive.
fLOOR (0, 0) = 0 
fLOOR (a, b) | b <= 0    = 0/0
             | otherwise = fLOOR0 a b

-- これらの第２引数は切り捨てで整数にされるみたい。なので、**ではなく^^を用いなければならない。
rOUND, roundup, rounddown :: (Double, Int) -> Double
rOUND (a, b) = mround (a, 0.1 ^^ b)
roundup (a, b) | a > 0     = cEILING (a, 0.1 ^^ b)
               | otherwise = fLOOR0 a (0.1 ^^ b)
rounddown (a, b) | a < 0     = cEILING (a, 0.1 ^^ b)
                 | otherwise = fLOOR0 a (0.1 ^^ b)

trim = unwords . words
fIND :: (Num b) => (String, String, Int) -> Maybe b
fIND (pat, xs, pos) = fmap (fromIntegral . fst) $ Data.List.find (isPrefixOf pat . snd) $ zip [1..] $ drop (pos-1) $ tails xs
ifERROR :: (Maybe a, a) -> a
ifERROR (mb, x) = maybe x id mb
aND (a, b) = a && b
oR  (a, b) = a || b
sign :: Num a => a -> a
sign = signum
power (a,b) | isNaN result || isInfinite result = Nothing 
            | otherwise                         = Just result
  where result = a ** b
sQRT x | x < 0     = Nothing
       | otherwise = Just $ sqrt x
lOG(a,b) | a<=0 || b<=0 = Nothing
         | otherwise    = Just $ logBase b a
ln a | a <= 0    = Nothing
     | otherwise = Just $ Prelude.log a
pI () = pi
aTAN2 (x,y) = atan2 y x

fact n | n < 0 = Nothing
       | otherwise = Just $ product [1..n]
combin (n,r) | (signum n + 1) * (signum r + 1) * (signum (r-n) + 1) == 0 = Nothing
             | otherwise = Just $ product [n-r+1 .. n] `div` product [1..r]

mOD    :: (Int, Int) -> Maybe Int
mOD(_,0) = Nothing
mOD(m,n) = Just $ m `mod` n
degrees = ((180/pi)*)
radians = ((pi/180)*)


gCD (m, n) = totalGCD (truncate m) (truncate n)

findIx c xs n = finD(char(7), sUBSTITUTE(concatenate(c,xs), c, char(7), 1+abs(n)))-1
finD(c, xs) = maybe undefined id $ fIND(c, xs, 1)
char = (:"") . chr


sUBsTITUTE :: (String, String, String) -> String
sUBsTITUTE(ts, "", _) = ts -- 実際やってみたらこうだった．
sUBsTITUTE([], _,  _) = []
sUBsTITUTE(text@(t:ts), old, new) = case old `stripPrefix` text of Nothing   -> t   :  sUBsTITUTE(ts,   old, new)
                                                                   Just rest -> new ++ sUBsTITUTE(rest, old, new)

sUBSTITUTE :: (String, String, String, Int) -> String
sUBSTITUTE(text, old, new, num) | num <= 0  = error "#NUM"
                                | otherwise = if null old then text
                                                          else sUB text old new num
sUB ""          _   _   _ = ""
sUB text@(t:ts) old new n = case old `stripPrefix` text of Nothing               -> t : sUB ts old new n
                                                           Just rest | n<=1      -> new ++ rest
                                                                     | otherwise -> old ++ sUB rest old new (n-1)

sUBST4 :: String -> String -> String -> Int -> String
sUBST4 text old new num = sUBSTITUTE(text, old, new, 1+abs(num))

countStr :: Num a => String -> String -> a
countStr x ""  = 0
countStr x str = fromIntegral $ (length(x)-length(sUBsTITUTE(x,str,""))) `div` length (str)
$(mkCurriedDecls "'2" [|curry2|] [|(left,right,concatenate,cEILING,mround,rOUND,roundup,rounddown,ifERROR,aND,oR,power,lOG,aTAN2,combin,mOD,gCD)|])
{- The above should generate:
left'2  = curry2 left
right'2 = curry2 right
...
-}

$(mkCurriedDecls "'3" [|curry3|] [|(iF,mid,fIND,sUBsTITUTE,concatenatE)|])
{- again,
iF'3    = curry3 iF
mid'3   = curry3 mid
...
-}

$(mkCurriedDecls "'4" [|curry4|] [|concatenaTE|])

$(mkCurriedDecls "'5" [|curry5|] [|concatenATE|])

$(mkCurriedDecls "'6" [|curry6|] [|concateNATE|])
