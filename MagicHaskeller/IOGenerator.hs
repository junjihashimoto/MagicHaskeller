-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE FlexibleInstances, UndecidableInstances, OverlappingInstances, IncoherentInstances #-}
-- Used by the Web version.
module MagicHaskeller.IOGenerator(module MagicHaskeller.IOGenerator, NearEq((~=))) where
#ifdef TFRANDOM
import System.Random.TF.Gen
import System.Random.TF.Instances
#else
import System.Random
#endif
import MagicHaskeller.MyCheck
import Data.List(sort, group, sortBy, groupBy, nubBy, intersperse)
import Data.Function(on)
import Data.Char(isAlphaNum)
-- import Data.Ratio
import MagicHaskeller.FastRatio
import MagicHaskeller.LibTH(everythingF, pgfull, postprocess)
import MagicHaskeller.ExpToHtml(pprnn, annotateString, Language(..)) -- annotateFree is replaced with annotateString
import Language.Haskell.TH(pprint, Exp)
import Data.Typeable
import Text.Html(stringToHtmlString)

import MagicHaskeller.NearEq(NearEq((~=)))

#ifdef TFRANDOM
arbitraries :: Arbitrary a => [a]
arbitraries = arbs 4 (seedTFGen (12279932681387497184,218462391894233257,1625759680792809304,12756118543158863164))
arbs :: Arbitrary a => Int -> TFGen -> [a]
arbs n stdgen  =  case map (splitn stdgen 8) [0..255] of
                    g0:gs -> map (f n) gs ++ arbs n g0 -- I think 255 seeds is enough, but just in case.
    where Gen f = arbitrary
#else
arbitraries :: Arbitrary a => [a]
arbitraries = arbs 4 (mkStdGen 1)
arbs :: Arbitrary a => Int -> StdGen -> [a]
arbs n stdgen  =  case split stdgen of
                    (g0,g1) -> f n g0 : arbs n g1
    where Gen f = arbitrary
#endif

--showIOPairs :: IOGenerator a => String -> String -> a -> String
--showIOPairs crlf funname fun = concat $ map ((crlf ++) . (funname++)) $ generate fun
showIOPairsHTML :: String -> [ShownIOPair] -> String
showIOPairsHTML = showIOPairsHTML' (const showIOPairHTML)
showIOPairsWithFormsHTML :: String                     -- ^ CGI.myPath, which is usually "/cgi-bin/MagicHaskeller.cgi"
                         -> String                     -- ^ predicate before escaping single quotes
                         -> String -> [ShownIOPair] -> String
showIOPairsWithFormsHTML mypath predicate
    = let beginForm = "<FORM ACTION='"++mypath++"' METHOD=GET> <INPUT TYPE=HIDDEN NAME='predicate' VALUE='"++concatMap escapeQuote predicate ++"'> <INPUT TYPE=HIDDEN NAME='inputs' VALUE='"
      in showIOPairsHTML' (showIOPairWithFormHTML beginForm)
showIOPairsHTML' :: (Int -> ShownIOPair -> String) -> String -> [ShownIOPair] -> String
showIOPairsHTML' shower funname iopairs
  = concat $ map (("<tr align=left cellspacing=20><td><font size=1 color='#888888'>&amp;&amp;</font>&nbsp;</td><td>"++) . (funname++) . shower boxSize) {- (nubSortedOn iopairToInputs -} iopairs -- Instead, nubOn is applied to showArbitraries.  
  where boxSize  = maximum $ 20 : map length (snd $ unzip iopairs)

nubOn  f = map snd . nubBy ((==) `on` fst) . map (\x -> (f x, x))
nubSortedOn  f = map snd . nubSortedOn' fst . map (\x -> (f x, x))
nubSortedOn' f = map head . groupBy ((==) `on` f) . sortBy (compare `on` f)

type ShownIOPair = ([AnnShowS], String)

iopairToInputs :: ShownIOPair -> [String]
iopairToInputs (funs,_) = map assToString funs
assToString :: AnnShowS -> String
assToString fun = fun id ""

type AnnShowS = (String->String) -- ^ annotater
                -> String -> String
showIOPairHTML :: ShownIOPair -> String
showIOPairHTML (args,ret) = foldr (\arg str -> "&nbsp;</td><td>&nbsp;" ++ arg (annotateString LHaskell) str) ("&nbsp;</td><td>&nbsp; ~= &nbsp;</td><td> &nbsp;"++ret++ " &nbsp;</td></tr>") args

showIOPairWithFormHTML begin boxSize pair@(args,ret) = showIOPairHTML (args, mkForm begin boxSize pair)
mkForm :: String
       -> Int
       -> ShownIOPair
       -> String
-- predicateとinputsとoutputがあればよい．CGI側では，  '(':predicate++") && f "++inputs++" == "++output  をpredicateとして実行
mkForm begin boxSize (args,ret)
    = begin ++ concatMap escapeQuote (showsInputs args "") ++ "'> <INPUT TYPE=TEXT NAME='output' VALUE='"++concatMap escapeQuote ret ++ "' SIZE="++show boxSize ++"> <INPUT TYPE=SUBMIT VALUE='Narrow search'> </FORM>"
showsInputs args = \s -> foldr (\arg str -> ' ' : arg id str) s args
escapeQuote '\'' = "&apos;"
escapeQuote c    = [c]

class IOGenerator a where
--    generate     :: a -> [String]
    generateIOPairs :: a -> [ShownIOPair] -- list of pairs of shown arguments and shown return values
instance (IOGenerator r) => IOGenerator (Int->r) where
  -- generate      f = [ ' ' : showParen (a<0) (shows a) s | a <- uniqSort $ take 5 arbitraries, s <- generate (f a) ]
  generateIOPairs = generateIOPairsLitNum integrals
instance (IOGenerator r) => IOGenerator (Integer->r) where
  -- generate      f = [ ' ' : showParen (a<0) (shows a) s | a <- uniqSort $ take 5 arbitraries, s <- generate (f a) ]
  generateIOPairs = generateIOPairsLitNum integrals
instance (IOGenerator r) => IOGenerator (Float->r) where
  -- generate      f = [ ' ' : showParen (a<0) (shows a) s | a <- uniqSort $ take 5 arbitraries, s <- generate (f a) ]
  generateIOPairs = generateIOPairsLitNum arbitraries
instance (IOGenerator r) => IOGenerator (Double->r) where
  -- generate      f = [ ' ' : showParen (a<0) (shows a) s | a <- uniqSort $ take 5 arbitraries, s <- generate (f a) ]
  generateIOPairs = generateIOPairsLitNum arbitraries

generateIOPairsLitNum :: (Num a, Ord a, Show a, IOGenerator b) =>
                         [a] -> (a -> b) -> [ShownIOPair]
-- Can be used for Integer, Double, and Float, but not for Ratio and Complex.
generateIOPairsLitNum rs f = [ (const (showParen (a<0) (shows a)) : args, ret) | a <- uniqSort $ take 4 rs, (args,ret) <- generateIOPairs (f a) ]

integrals :: Integral i => [i]
integrals = concat $ zipWith (\a b -> [a,b]) [0,-1..] [1..]

instance (IOGenerator r) => IOGenerator (()->r) where
--    generate     f = generateFun False f
    generateIOPairs f = generateIOPairsFun False f
instance (IOGenerator r) => IOGenerator (Bool->r) where
--    generate     f = generateFun False f
    generateIOPairs f = generateIOPairsFun False f
instance (IOGenerator r) => IOGenerator (Ordering->r) where
--    generate     f = generateFun False f
    generateIOPairs f = generateIOPairsFun False f
instance (IOGenerator r) => IOGenerator (Char->r) where
--    generate     f = generateFun False f
    generateIOPairs f = [ (const (stringToHtmlString (show a) ++) : args, ret) | a <- " \nAb."{- ++ take 0 arbitraries -}, (args,ret) <- generateIOPairs (f a) ]

instance (IOGenerator r) => IOGenerator (String->r) where
--    generate     f = generateFun False f
    generateIOPairs f = [ (const (shows a) : args, ret) | a <- sortBy (compare `on` length) $ uniqSort $ "" : "12345" : "Abc\nd Ef" : take 2 arbitraries,
                                                  (args, ret) <- generateIOPairs (f a) ]
{----------------------------------------------------------------------- Do not use these in order to deal with types like [Int->Int]->Int.
    -- ただ、コメントアウトすると、[Int]とかでもeverythingFを使うため簡約されていない形で表示されてしまうので，分かりにくくなってしまう．両方のバージョンを用意してエラーになったらもう一方ってのがよさそう。
instance (Arbitrary a, Show a, Ord a, IOGenerator r) => IOGenerator ([a]->r) where
--    generate     f = generateFun False f
    generateIOPairs f = [ (shows a : args, ret) | a <- sortBy (compare `on` length) $ uniqSort $ [] : take 4 arbitraries,
                                                  (args, ret) <- generateIOPairs (f a) ]

instance (Arbitrary a, Show a, Ord a, IOGenerator r) => IOGenerator (Maybe a -> r) where
--    generate     f = generateFun False f
    generateIOPairs f = generateIOPairsFun True f
instance (Arbitrary a, Show a, Ord a, Integral a, Random a, IOGenerator r) => IOGenerator (Ratio a -> r) where
--    generate     f = generateFun False f
    generateIOPairs f = generateIOPairsFun True f
instance (Arbitrary a, Show a, Ord a, Arbitrary b, Show b, Ord b, IOGenerator r) => IOGenerator ((a,b)->r) where
--    generate     f = generateFun False f
    generateIOPairs f = generateIOPairsFun False f
instance (Arbitrary a, Show a, Ord a, Arbitrary b, Show b, Ord b, Arbitrary c, Show c, Ord c, IOGenerator r) => IOGenerator ((a,b,c)->r) where
--    generate     f = generateFun False f
    generateIOPairs f = generateIOPairsFun False f
instance (Arbitrary a, Show a, Ord a, Arbitrary b, Show b, Ord b, IOGenerator r) => IOGenerator ((Either a b)->r) where
--    generate     f = generateFun False f
    generateIOPairs f = generateIOPairsFun True f
---------------------------------------------------------------------}
instance (ShowArbitrary a, IOGenerator r) => IOGenerator (a->r) where
--    generate     f = generateFun True f
    generateIOPairs = mhGenerateIOPairs

mhGenerateIOPairs :: (ShowArbitrary a, IOGenerator b) =>
                     (a -> b) -> [ShownIOPair]
mhGenerateIOPairs f = [ (astr : args, ret)
                                | (astr, a) <- take 5 $ nubOn (assToString . fst) showArbitraries,
                                  (args, ret) <- generateIOPairs (f a) ]

-- | 'ShowArbitrary' is a variant of 'Arbitrary' for presenting I/O example pairs. It uses everythingF for generating printable functions.
--   Here `good presentation' is more important than `good randomness'.
class ShowArbitrary a where
      showArbitraries :: [(AnnShowS, a)]
sas      :: (Show a) => (a->Bool) -> [a] -> [(AnnShowS, a)]
sas cond xs = [ (const $ showParen (cond x) (shows x), x) | x <- xs ]
sasNum   :: (Show a, Arbitrary a, Num a, Ord a) => [(AnnShowS, a)]
sasNum   = sas (<0) arbitraries
sasFalse :: (Show a) => [a] -> [(AnnShowS, a)]
sasFalse = sas (const False)
sasIntegral :: (Show a, Arbitrary a, Integral a, Ord a) => [(AnnShowS, a)]
sasIntegral = sas (<0) [0,1] ++ -- interleave [2..] [-1,-2..]
              drop 2 sasNum
-- interleave xs ys = concat $ transpose [xs, ys]
instance ShowArbitrary () where
      showArbitraries = repeat (const ("()"++),())
instance ShowArbitrary Bool where
      showArbitraries = sasFalse $ [False, True] ++ arbitraries
instance ShowArbitrary Int where
      showArbitraries = sasIntegral
instance ShowArbitrary Integer where
      showArbitraries = sasIntegral
instance ShowArbitrary Float where
      showArbitraries = sasNum
instance ShowArbitrary Double where
      showArbitraries = sasNum
instance ShowArbitrary Char where
      showArbitraries = sasFalse $ " \nAb."++ drop 5 arbitraries
instance ShowArbitrary Ordering where
      showArbitraries = sasFalse $ [LT,EQ,GT] ++ arbitraries
instance (Integral i, Random i, Show i) => ShowArbitrary (Ratio i) where
      showArbitraries = sas (const True) arbitraries
instance ShowArbitrary a => ShowArbitrary (Maybe a) where
      showArbitraries = (const ("Nothing"++), Nothing) : map (mapSA "Just " Just) showArbitraries
instance (ShowArbitrary a, ShowArbitrary b) => ShowArbitrary (Either a b) where
      showArbitraries = zipWith3 (\b l r -> if b then mapSA "Left " Left l else mapSA "Right " Right r) arbitraries showArbitraries showArbitraries
-- ほんとはもっとランダムにすべきではある．2本Eitherがある場合，同じarbitraries::[Bool]を共有するので，同じ箇所でLeftやRightになる．
mapSA str fun (f,x) =  (\annotater -> showParen True ((str++) . f annotater), fun x)
instance (ShowArbitrary a, ShowArbitrary b) => ShowArbitrary (a, b) where
      showArbitraries = zipWith (\(f1,x1) (f2,x2) -> (\annotater -> ('(':) . f1 annotater . (',':) . f2 annotater . (')':), (x1,x2))) 
                                (skip 1 showArbitraries) 
                                (skip 1 $ drop 1 showArbitraries)
instance (ShowArbitrary a, ShowArbitrary b, ShowArbitrary c) => ShowArbitrary (a, b, c) where
      showArbitraries = zipWith3 (\(f1,x1) (f2,x2) (f3,x3) -> (\annotater -> ('(':) . f1 annotater . (',':) . f2 annotater . (',':) . f3 annotater . (')':), (x1,x2,x3))) 
                                 (skip 2 showArbitraries) 
                                 (skip 2 $ drop 1 showArbitraries) 
                                 (skip 2 $ drop 2 showArbitraries)
-- leap frog
skip n (x:xs) = x : skip n (drop n xs)
instance ShowArbitrary a => ShowArbitrary [a] where
      showArbitraries = map cvt $ chopBy arbitraries showArbitraries
-- ほんとはもっとランダムにすべきではある．2本[a]がある場合，同じarbitraries::[Int]を共有するので，同じ箇所で同じ長さになる．
chopBy :: [Int] -> [a] -> [[a]]
chopBy _      [] = []         -- everythingFを使ってある点で切る限り，有限の可能性も必ず残る．空リストであることもありえるので，cycleしてもダメ．
chopBy is     xs = cb is $ cycle xs
  where cb (i:is) xs | i < 0     = cb is xs
                     | otherwise = case splitAt i xs of (tk,dr) -> tk : cb is dr
cvt :: [(AnnShowS,a)] -> (AnnShowS, [a])
cvt ts = case unzip ts of (fs, xs) -> (showsList fs, xs)

showsList fs@(f:_) | head (f id "") == '\'' -- The String case is dealt with here. I use overlapping instances only conservatively. The drawback is that "" is still printed as []. 
                       = const $ shows (map (\fun -> read $ fun id "") fs :: String)
showsList fs       = \annotater -> ('[':) . foldr (.) (']':) (intersperse (',':) $ map ($ annotater) fs)

instance (Typeable a, Typeable b) => ShowArbitrary (a->b) where
      showArbitraries = map (\(e,a) -> (\annotater -> (annotater (pprnn (postprocess e)) ++) , a)) $ concat $ take 5 $ everythingF pgfull True

generateIOPairsFun :: (Ord a, Show a, Arbitrary a, IOGenerator b) => Bool -> (a->b) -> [ShownIOPair]
-- generateFun     b f = [ ' ' : showParen b (shows a) s | a <- uniqSort $ take 5 arbitraries, s <- generate (f a) ]
generateIOPairsFun b f = [ (const (showParen b (shows a)) : args, ret) 
                         | a <- uniqSort $ take 5 arbitraries
                         , (args, ret) <- generateIOPairs (f a) ]

instance Show a => IOGenerator a where
--    generate     x = [" = "++show x]
    generateIOPairs x = [([], stringToHtmlString $ show x)]

uniqSort :: Ord a => [a] -> [a]
uniqSort = map head . group . sort
