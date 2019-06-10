-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE UndecidableInstances, OverlappingInstances, TemplateHaskell, CPP, FlexibleInstances #-} 
-- x #define TESTEQ

module MagicHaskeller.Classification -- (
                      -- randomTestFilter, -- ::  Filtrable a => (b->a) -> Matrix b -> Matrix b
                      -- )
                      where
import Prelude hiding ((/))
#ifdef TFRANDOM
import System.Random.TF.Gen
#else
import System.Random
#endif
import MagicHaskeller.MyCheck
import Data.Char
import Data.List
import Control.Monad
import Control.Monad.Search.Combinatorial
import Data.Complex

import MagicHaskeller.MHTH
import MagicHaskeller.TimeOut
import MagicHaskeller.T10

import MagicHaskeller.Instantiate(compareRealFloat)

class (Search m) => SStrategy m where
    sfilter :: Relation r =>
               (k->k->r) -> (Int->Int) -> m ([k],e) -> m ([k],e)
    ofilter :: Relation r =>
               (k->k->r) -> m (k,e) -> m (k,e)

instance SStrategy Matrix where
    sfilter = sfilterMx
    ofilter = ofilterMx

instance SStrategy DBound where
    sfilter = sfilterDB
    ofilter = ofilterDB

#ifdef TFRANDOM
arbitraries :: Arbitrary a => [a]
arbitraries = arbs 0 (seedTFGen (12279932681387497184,218462391894233257,1625759680792809304,12756118543158863164))
arbs :: Arbitrary a => Int -> TFGen -> [a]
arbs n stdgen  =  case map (splitn stdgen 8) [0..255] of
                    g0:gs -> zipWith f [n..] gs ++ arbs (n+255) g0 -- I think 255 seeds is enough, but just in case.
    where Gen f = arbitrary
#else
arbitraries :: Arbitrary a => [a]
arbitraries = arbs 0 (mkStdGen 1)
arbs :: Arbitrary a => Int -> StdGen -> [a]
arbs n stdgen  =  case split stdgen of
                    (g0,g1) -> f n g0 : arbs (n+1) g1
    where Gen f = arbitrary
#endif

(/~) :: [a] -> (a->a->Bool) -> [[a]]
[]      /~  eq  =  []
(x:xs)  /~  eq  =  case partition (x `eq`) xs of
                     (same, diff) -> (x:same) : (diff /~ eq)
{-
なお，上記(/)および下記nubの場合，無限リストでもいける．
*T10> let {[]     / eq = []; (x:xs) / eq = case partition (x `eq`) xs of (same, diff) -> (x:same) : (diff / eq)}
*T10> cycle "hogeha" / (==)
["hhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhh
(snip)
hhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhInterrupted.
*T10> map head $ cycle "hogeha" / (==)
"hogeaInterrupted.
*T10> Data.List.nub $ cycle "hogeha"
"hogeaTerminated
(snip)
*T10> Data.List.nub $ repeat 'h'
"hTerminated
-}




-- ToDo: deal with timeout




-- complete set of representatives
nubSortBy :: (a->a->Ordering) -> [a] -> [a]
nubSortBy = mergesortWithBy const
nubSortByBot :: (a->a->Maybe Ordering) -> [a] -> [a]
nubSortByBot = mergesortWithByBot const
-- quotient set
(/<) :: [a] -> (a->a->Ordering) -> [[a]]
xs /< cmp  =  mergesortWithBy (++)
                (\x y -> head x `cmp` head y)
                (map return xs)
(/<?) :: [a] -> (a->a->Maybe Ordering) -> [[a]]
xs /<? cmp  =  mergesortWithByBot (++)
                (\x y -> head x `cmp` head y)
                (map return xs)
class Eq rel => Relation rel where
 -- remove duplicates, and sort if |rel==Ordering|
    fromListBy   :: (k->k->rel) -> [k] -> [k]
    fromListBy cmp = map head . (/cmp)
-- used to pick up the shallowest expression in |DBound|
    fromListByDB :: (k->k->rel) -> [(k,Int)] -> [(k,Int)]
    fromListByDB rel ts =
          map  (minimumBy (\x y -> compare (snd y) (snd x)))
               (ts / (\x y -> rel (fst x) (fst y)))
    -- \NB : |maximumBy| returns the last of the maxima,
    -- while |minimumBy| the first of the minima.
 -- quotient set
    (/)          :: [k] -> (k->k->rel) -> [[k]]
 -- merge two lists, 
    appendWithBy :: (k->k->k) -> -- combiner
                    (k->k->rel) -> [k] -> [k] -> [k]
    diffBy       :: (k -> k -> rel) -> [k] -> [k] -> [k]
 -- counterpart of EQ
    cEQ          :: rel
-- merge two quotient sets
appendQuotientsBy ::
  (Relation rel) =>
  (k -> k -> rel) -> [[k]] -> [[k]] -> [[k]]
appendQuotientsBy rel =
   appendWithBy (++) (\ (x:_) (y:_) -> x `rel` y)
-- merge two complete sets of representatives
appendRepresentativesBy ::
   (Relation rel) =>
   (k -> k -> rel) -> [k] -> [k] -> [k]
appendRepresentativesBy = appendWithBy const

instance Relation Bool where
    fromListBy    = Data.List.nubBy
    (/)           = (/~)
    appendWithBy  = unionWithBy
    diffBy        = Data.List.deleteFirstsBy
    cEQ           = True
unionWithBy combiner eq []      ys = ys
unionWithBy combiner eq (x:xs)  ys =
   case break (eq x) ys of
      (_,   [])    ->  x  :  unionWithBy combiner eq xs ys
      (ts,  h:ds)  ->  (x `combiner` h)
                          :  unionWithBy combiner eq xs (ts++ds)
instance Relation Ordering where
    fromListBy    = nubSortBy
    fromListByDB rel =
        mergesortWithBy
                    (\x y -> if snd x < snd y then y else x)
                    (\x y -> fst x `rel` fst y)
    (/)           = (/<)
    appendWithBy  = mergeWithBy
    diffBy        = diffSortedBy
    cEQ           = EQ
instance Relation (Maybe Ordering) where
    fromListBy    = nubSortByBot
    fromListByDB rel =
        mergesortWithByBot
                    (\x y -> if snd x < snd y then y else x)
                    (\x y -> fst x `rel` fst y)
    (/)           = (/<?)
    appendWithBy  = mergeWithByBot
    diffBy        = diffSortedByBot
    cEQ           = Just EQ

randomTestFilter ::  (SStrategy m, Filtrable a) =>
                     (Int->Int) -> m (e,a) -> m (e,a)
randomTestFilter numRandoms = filt numRandoms . fmap (\ t@(_,a) -> (a,t))

unsafeRandomTestFilter ::  (SStrategy m, Filtrable a) =>
                           Maybe Int -- ^ microsecs until timeout
                               -> (Int->Int) -> m (e,a) -> m (e,a)
unsafeRandomTestFilter mto numRandoms = unsafeFilt mto numRandoms . fmap (\ t@(_,a) -> (a,t))

mapFst f (a,b) = (f a, b)

class Filtrable a where
    filt    :: SStrategy m => (Int->Int) -> m (a,e) -> m e
    filtFun :: (SStrategy m, Arbitrary b) =>
               (Int->Int) -> m (b->a,e) -> m e
    unsafeFilt    :: SStrategy m =>
                     Maybe Int -> (Int->Int) -> m (a,e) -> m e
    unsafeFiltFun :: (SStrategy m, Arbitrary b) =>
                     Maybe Int -> (Int->Int) -> m (b->a,e) -> m e

instance  (Arbitrary a, Filtrable r) => Filtrable (a->r)
  where
    filt      = filtFun
    filtFun f = filt f . fmap (mapFst uncurry)
    unsafeFilt    mto f = unsafeFiltFun mto f
    unsafeFiltFun mto f = unsafeFilt mto f . fmap (mapFst uncurry)

#ifdef TESTEQ
instance Eq a => Filtrable a where
    filt     = filtNullary  (==)
    filtFun  = filtUnary    (==)
#else
instance Ord a => Filtrable a where
    filt     = filtNullary  compare
    filtFun  = filtUnary    compare
    unsafeFilt    mto = filtNullary  (unsafeOpWithPTO mto compare)
    unsafeFiltFun mto = filtUnary    (unsafeOpWithPTO mto compare)
instance Filtrable Double where
    filt     = filtNullary  compareRealFloat
    filtFun  = filtUnary    compareRealFloat
    unsafeFilt    mto = filtNullary  (unsafeOpWithPTO mto compareRealFloat)
    unsafeFiltFun mto = filtUnary    (unsafeOpWithPTO mto compareRealFloat)
#endif
filtNullary ::  (SStrategy m, Relation r) =>
                (k->k->r) -> (Int->Int) -> m (k,e) -> m e
filtNullary  op _ =  fmap snd . ofilter op
filtUnary    op f =  fmap snd . sfilter op f .
                      fmap (mapFst (flip map arbitraries))

instance  (RealFloat a, Ord a) =>
          Filtrable (Complex a) where
    filt     = filtNullary  compareCx
    filtFun  = filtUnary    compareCx
    unsafeFilt    mto = filtNullary  (unsafeOpWithPTO mto compareCx)
    unsafeFiltFun mto = filtUnary    (unsafeOpWithPTO mto compareCx)
compareCx ::  (RealFloat a, Ord a) =>
              Complex a -> Complex a -> Ordering
(a:+b) `compareCx` (c:+d) = case compare a c of
                              EQ -> compare b d
                              o  -> o
ofilterMx ::  Relation r =>
            (k->k->r) -> Matrix (k,e) -> Matrix (k,e)
ofilterMx op (Mx xss)
        = let
            (k,_) `rel` (l,_) = k `op` l
            mapped     = map (fromListBy rel) xss
            cumulative =
                 scanl  (appendRepresentativesBy rel)
                                 [] mapped
          in Mx $ zipWith (diffBy rel) mapped cumulative

ofilterDB :: Relation rel =>
              (k->k->rel) ->
               DBound (k,e) -> DBound (k,e)
ofilterDB cmp (DB f) = DB $
    \n -> fromListByDB  (\(k,_) (l,_) -> cmp k l)
                        (f n)

cumulativeRepresentatives ::
    Relation rel =>
   [a->a->rel] -> Matrix a -> Matrix a
cumulativeRepresentatives relations mx =
    fmap head (cumulativeQuotients relations mx)

representatives ::
    Relation rel =>
   [a->a->rel] -> Matrix a -> Matrix a
representatives relations mx = 
   unscanlByList relations $
        cumulativeRepresentatives relations mx
unscanlByList ::  Relation r =>
                  [k->k->r] -> Matrix k -> Matrix k
unscanlByList (_:rels) (Mx (yss@(xs:xss))) =
    Mx $ xs : zipWith3 diffBy rels xss yss

sfilterMx ::  Relation r =>
              (k->k->r) -> 
              (Int->Int) ->
              Matrix ([k],e) -> Matrix ([k],e)
sfilterMx rel numRands = representatives (map (liftRelation rel . numRands) [0..])
liftRelation ::  Relation r =>
                 (k->k->r) -> 
                    Int -> ([k],e) -> ([k],e) -> r
liftRelation rel len (xs,_) (ys,_) = liftRel rel len xs ys
liftRel _   0   _      _      = cEQ
liftRel _   _   []     []     = cEQ
liftRel rel len (x:xs) (y:ys) =
    case rel x y of
           c  | c == cEQ   -> liftRel rel (len-1) xs ys
              | otherwise  -> c

sfilterDB ::  Relation rel =>
               (k->k->rel) ->
              (Int->Int)->
                DBound ([k],e) -> DBound ([k],e)
sfilterDB rel numRands (DB f) = DB $ \n -> fromListByDB  (liftRelation rel (numRands n)) (f n)

cumulativeQuotients relations (Mx xss)
   =  let yss:ysss = zipWith (/) xss relations
      in Mx $ scanl  (\rec (r,z) ->
                       appendQuotientsBy r (rec>>=(/r)) z)
                     yss  (zip (tail relations) ysss)

ns = [6..]
