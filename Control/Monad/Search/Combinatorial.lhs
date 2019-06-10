-- 
-- (c) Susumu Katayama
--
Combinators for Combinatorial Search:
The first part is a slight hack on Spivey 2000.
The second part is my (Susumu's) original which by recomputation refrains producing thunks.
The third part defines DBound, found in Spivey 2006.

\begin{code}
{-# OPTIONS -cpp -XUndecidableInstances -XMultiParamTypeClasses -XTypeSynonymInstances #-}
module Control.Monad.Search.Combinatorial(Matrix(..), (/\), (\/), Recomp(..), RecompT(..), rcToMx, mxToRc, Search(..), diag, Delay(..), msumMx, msumRc, listToRc, consMx, consRc, zipWithBF, printMx, printNMx, {- filterMx, -} mapDepthDB,
                               Bag, Stream, cat, toList, getDepth, scanl1BF, zipDepthMx, zipDepthRc, zipDepth3Mx, zipDepth3Rc, scanlRc,
                               DBound(..), DBoundT(..), zipDepthDB, DBMemo(..), Memoable(..), shrink, DB, dbtToRcT) where
import Control.Monad -- hiding (join) -- ... but still collided when using Hat.
import Control.Applicative -- necessary for backward compatibility
#ifdef HOOD
import Observe
#endif
import Data.Monoid -- Matrix, and any (MonadPlus a) => a, should be a Monoid.

#ifdef QUICKCHECK
import Test.QuickCheck hiding (shrink)
import Data.List(sort)
#endif
import MagicHaskeller.T10(mergesortWithBy, mergesortWithByBot)
import Control.Monad.State

import Data.Array

-- import AList -- append list used as the Bag

-- instance (MonadPlus m) => Monoid (m a) where
instance Monoid (Matrix a) where
    mempty  = mzero
    mappend = mplus
instance Monoid (Recomp a) where
    mempty  = mzero
    mappend = mplus
instance (Functor m, Monad m) => Monoid (RecompT m a) where
    mempty  = mzero
    mappend = mplus

type Stream a = [a]

{-
type Bag a    = AList a
cat = concatAL
toList = flattenAL
-}
type Bag a = [a]
cat = concat
toList = id

#ifdef QUICKCHECK
newtype Matrix a = Mx {unMx::Stream (Bag a)}
instance Show a => Show (Matrix a) where
    showsPrec _ (Mx xss) = ("Mx {unMx = "++) . shows (take 10 xss) . (" ...}"++)-- because we do not like to show infinite lists
#else
newtype Matrix a = Mx {unMx::Stream (Bag a)} deriving Show
#endif
#ifdef HOOD
instance Observable a => Observable (Matrix a) where
    observer (Mx a) = send "Mx" (return Mx << a)
#endif
instance Applicative Matrix where
    pure x = Mx (return x : nils)
    (<*>)  = ap
instance Monad Matrix where
    return = pure
    Mx x >>= f  = Mx (jOIN (map (fmap (unMx.f)) x))
instance Alternative Matrix where
    empty = mzero
    (<|>) = mplus
instance MonadPlus Matrix where
    mzero = Mx nils
    Mx xm `mplus` Mx ym = Mx (zipWith mappend xm ym)
nils :: Stream (Bag a)
nils = repeat mempty
p /\ q = \x -> (q x >>= p)
p \/ q = \x -> (p x `mplus` q x)
jOIN :: Stream (Bag (Stream (Bag a))) -> Stream (Bag a)
jOIN = map (cat.cat) . diag . map trans

diag :: Stream (Stream a) -> Stream (Bag a)
diag ((x:xs):xss) = return x : zipWith cons xs (diag xss)

cons a b = return a `mappend` b

trans :: Bag (Stream a) -> Stream (Bag a)
trans xss = fmap head xss : trans (fmap tail xss)
-- Actually I am not sure why this definition is better than "trans = foldr (zipWith (:)) (repeat [])"....
-- (but the correction really worked in the profiling result.)

-- not sure if this is really needed.
instance Functor Matrix where
    fmap f (Mx xss) = Mx (map (fmap f) xss)

instance Functor Recomp where
    fmap f (Rc xss) = Rc (\d -> fmap f (xss d))
instance Functor DBound where
    fmap f (DB g) = DB (\d -> fmap (\(x,i)->(f x,i)) (g d))
instance Functor f => Functor (RecompT f) where
    fmap f (RcT g) = RcT $ \dep -> fmap (map f) (g dep)
instance Functor f => Functor (DBoundT f) where
    fmap f (DBT g) = DBT (\d -> fmap (map (\(x,i)->(f x,i))) (g d))

-- should be slightly more efficient than msum
msumMx xs = Mx (xs : nils)
-- msumRc xs = Rc (const xs) 間違い
msumRc = listToRc
listToRc l = Rc f where f 0 = l
                        f _ = mempty

{-
-- m is usually IO or ST s
accumulate :: Monad m => Matrix (m a) -> m (Matrix a)
accumulate (Mx xss) = fmap Mx (sequence (sequence xss))
-}
\end{code}

\begin{code}
type    DepthFst = [] -- ghc6.8 does not like "type DepthFst = Stream"
newtype Recomp a = Rc {unRc::Int->Bag a}
newtype RecompT m a = RcT {unRcT::Int -> m (Bag a)}
instance Applicative Recomp where
    pure x = Rc f where f 0 = return x
                        f _ = mempty
    (<*>)  = ap
instance Monad Recomp where
    return = pure
    Rc f >>= g = Rc ( \n  ->  mconcat $  map  (\i -> cat $ fmap (\a -> unRc (g a) (n-i)) (f i))  [0..n] )
--    Rc f >>= g = Rc (\n -> [ y | i <- [0..n], x <- f i, y <- unRc (g x) (n-i) ]) -- Bag a = [a]の場合．
--    Rc f >>= g = Rc (\n -> concat $ map (\i -> concat $ map (\a -> unRc (g a) (n-i)) (f i)) [0..n]) -- STRecompに相当する書き方．とくに遅くはならない....

instance (Functor m, Monad m) => Applicative (RecompT m) where
    pure x = RcT f where f 0 = return [x]
                         f _ = return []
    (<*>)  = ap
instance (Functor m, Monad m) => Monad (RecompT m) where
    return = pure
    RcT f >>= g = RcT ( \n  -> let
                                 hoge i = do xs <- f i
                                             xss <- mapM (\x -> unRcT (g x) (n-i)) xs
                                             return (concat xss)
                               in do xss <- mapM hoge [0..n]
                                     return $ concat xss)

instance Alternative Recomp where
    empty = mzero
    (<|>) = mplus
instance MonadPlus Recomp where
    mzero = Rc (const mempty)
    Rc f `mplus` Rc g = Rc (\i -> f i `mappend` g i)
instance (Functor m, Monad m) => Alternative (RecompT m) where
    empty = mzero
    (<|>) = mplus
instance (Functor m, Monad m) => MonadPlus (RecompT m) where
    mzero = RcT (const $ return [])
    RcT f `mplus` RcT g = RcT (\i -> do xs <- f i        -- f i と g iの両方を実行することになるけど，IOで使う上で間違ってはいない．
                                        ys <- g i
                                        return (xs++ys))

rcToMx :: Recomp a -> Matrix a
rcToMx (Rc f) = Mx (map f [0..])
{-
rcToMx (Rc f) = Mx (go 0)
    where go n = f n : go (n+1)
-}

mxToRc :: Matrix a -> Recomp a
mxToRc (Mx s) = Rc (s!!)

consMx :: Bag a -> Matrix a -> Matrix a
consMx xs (Mx xss) = Mx (xs : xss)

consRc :: Bag a -> Recomp a -> Recomp a
consRc xs (Rc f) = Rc g where g 0 = xs
                              g n = f (n-1)

{-
-- mapDepthがあれば，定義する必要はない．
-- filterMx f (Mx xss) = Mx (map (filter f) xss)
filterMx f = mapDepth (filter f)
-}

class Search m => DB m where
    mapDepthDB :: (Bag (a,Int) -> Bag (b,Int)) -> m a -> m b
    zipDepthDB :: (Int -> Bag (a,Int) -> Bag (b,Int)) -> m a -> m b

instance DB DBound where
    mapDepthDB f (DB g) = DB (f.g)
    zipDepthDB f (DB g) = DB (\d -> f d (g d))

instance (Functor m, Monad m) => DB (DBoundT m) where
    mapDepthDB f (DBT g) = DBT $ fmap f . g
    zipDepthDB f (DBT g) = DBT $ \d -> fmap (f d) (g d)

zipDepthMx :: (Int -> Bag a -> Bag b) -> Matrix a -> Matrix b
zipDepthMx f (Mx xss) = Mx (zipWith f [0..] xss)

zipDepthRc :: (Int -> Bag a -> Bag b) -> Recomp a -> Recomp b
zipDepthRc f (Rc g) = Rc (\d -> f d (g d))

zipDepth3Mx :: (Int -> Bag a -> Bag b -> Bag c) -> Matrix a -> Matrix b -> Matrix c
zipDepth3Mx f (Mx xss) (Mx yss) = Mx (zipWith3 f [0..] xss yss)

zipDepth3Rc :: (Int -> Bag a -> Bag b -> Bag c) -> Recomp a -> Recomp b -> Recomp c
zipDepth3Rc f (Rc g) (Rc h) = Rc (\d -> f d (g d) (h d))

printMx (Mx xss) = pmx 0 xss
    where pmx n (xs:xss) = do putStrLn ("\ndepth = " ++ show n)
                              mapM_ print (toList xs)
                              pmx (n+1) xss
          pmx n [] = return ()
printNMx n (Mx xss) = printMx (Mx (take n xss))

-- join (liftM2 mtf mtx)よりもstrict
zipWithBF :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
zipWithBF f xss yss = do x <- xss
                         y <- yss
                         (f $! x) $! y

scanl1BF :: Search m => m x -> m x
scanl1BF bf = bf `mplus` delay (scanl1BF bf)

scanlRc :: (Bag a -> Bag b -> Bag a) -> Bag a -> Recomp b -> Recomp a
scanlRc f xs rc = result where result = xs `consRc` zipDepth3Rc (\_ -> f) result rc

-- making delay apart to implement zipWithConsFMT.
class Delay m where
    delay :: m a -> m a
    delay = ndelay 1
    ndelay  :: Int -> m a -> m a
    ndelay  n x = iterate delay x !! n
    getDepth :: m Int

instance Delay DepthFst where
    delay    = id
    ndelay _ = id
instance Delay Recomp where
    delay (Rc f) = Rc g where g 0 = mempty
                              g n = f (n-1)
    ndelay i (Rc f) = Rc g where g n | n < i     = mempty
                                     | otherwise = f (n-i)
    getDepth = Rc (\d -> [d])

instance Delay Matrix where
    delay (Mx xm) = Mx (mempty:xm)
    ndelay 0 mx = mx
    ndelay i mx = delay $ ndelay (i-1) mx
    getDepth = fromRc getDepth

instance Monad m => Delay (RecompT m) where
    delay (RcT f) = RcT g where g 0 = return mempty
                                g n = f (n-1)
    ndelay i (RcT f) = RcT g where g n | n < i     = return mempty
                                       | otherwise = f (n-i)

instance (Monad m, Delay m) => Delay (StateT s m) where
         delay    = mapStateT delay
         ndelay n = mapStateT (ndelay n)

class (Delay m, MonadPlus m, Functor m) => Search m where
    fromRc :: Recomp a -> m a
    toRc   :: m a -> Recomp a
    fromMx :: Matrix a -> m a
    toMx   :: m a -> Matrix a
    fromDB :: DBound a -> m a
    fromDF :: [a] -> m a   -- NB: this gives everything the top priority.
    toDF   :: m a -> [a]   -- NB: this drops the info of priority.
    -- | 'mapDepth' applies a function to the bag at each depth. 
    mapDepth :: (Bag a -> Bag b) -> m a -> m b
    -- | 'catBags' flattens each bag.
    catBags :: m (Bag a) -> m a
    catBags = mapDepth concat
    -- | 'mergesortDepthWithBy' converts bags to sets, by (possibly sorting each bag and) removing duplicates.
    --   Efficiency on lists with lots of duplicates is required.
    mergesortDepthWithBy :: (k->k->k) -- ^ Combiner, which is used when there are equivalent elements (compared by the comparer specified by the next argument).
                                      --   The return value of this combiner should also be equivalent to the two arguments.
                         -> (k->k->Ordering) -- ^ Comparer
                         -> m k -> m k
    mergesortDepthWithBy combiner comp = mapDepth (mergesortWithBy combiner comp)
    ifDepth :: (Int->Bool) -> m a -> m a -> m a
instance Search DepthFst where
    fromRc = fromMx . toMx
    toRc   = listToRc
    fromMx = concat . unMx
    toMx   = msumMx
    fromDB (DB f) = [x | d <- [0..], (x,_) <- f d ]
    fromDF = id
    toDF   = id
    mapDepth f = concat . map (f . (:[])) -- mapDepth /= id, because DepthFst is not a finite Bag but an infinite Stream.
    catBags = concat
    mergesortDepthWithBy _ _ = id
    ifDepth _ t _ = t
instance Search Recomp where
    fromRc = id
    toRc   = id
    fromMx = mxToRc
    toMx   = rcToMx
    fromDB = toRc
    fromDF = listToRc
    toDF   = fromMx . toMx
    mapDepth f (Rc g) = Rc (f.g)
    ifDepth pred (Rc t) (Rc f) = Rc fun
        where fun depth | pred depth = t depth
                        | otherwise  = f depth

instance (Functor m, Monad m) => Search (RecompT m) where
    fromRc (Rc f) = RcT (return . f)
    toRc   = error "no toRc for RecompT"
    fromMx = fromRc . mxToRc
    toMx   = error "no toMx for RecompT"
    fromDB = fromRc . toRc
    fromDF = fromRc . listToRc
    toDF = error "no toDF for RecompT"
    mapDepth f (RcT g) = RcT (\x -> fmap f (g x))
    ifDepth pred (RcT t) (RcT f) = RcT fun
        where fun depth | pred depth = t depth
                        | otherwise  = f depth

instance Search Matrix where
    fromRc = rcToMx
    toRc   = mxToRc
    fromMx = id
    toMx   = id
    fromDB = toMx
    fromDF = msumMx
    toDF   = concat . unMx
    mapDepth f (Mx xss) = Mx (map f xss)
    ifDepth pred (Mx ts) (Mx fs) = Mx $ zipWith3 chooser [0..] ts fs
        where chooser depth t f | pred depth = t
                                | otherwise  = f

#ifdef QUICKCHECK
instance Arbitrary a => Arbitrary (Matrix a) where
    arbitrary = liftM fromRc arbitrary -- Converting from Recomp makes sure that the outer list is infinite. 
instance Arbitrary a => Arbitrary (Recomp a) where
    arbitrary = liftM Rc arbitrary
instance Arbitrary a => Arbitrary (DBound a) where
--    arbitrary = liftM fromRc arbitrary
    arbitrary = liftM fromRc arbitrary
-- Having only one of the above two is not enough to test the converter (like fromRc) used here!
-- |arbitrary = liftM DB arbitrary| is not enough, because the annotated Int cannot be greater than the argument Int.
#endif

instance Show (Recomp a) where
    showsPrec _ _ = ("<Recomp>"++)
instance Show (DBound a) where
    showsPrec _ _ = ("<DBound>"++)

\end{code}

\begin{code}
-- aはあらかじめannotateしたものを用いる
categorizeDB :: DBound a -> Int -> Array Int [a]
categorizeDB (DB f) b = categorize b $ f b -- この辺は不要
categorize b ts = accumArray (flip (:)) [] (0,b) $ map swap ts
uncategorizeDB :: (Int -> Array Int [a]) -> DBound a
uncategorizeDB f = DB $ \b -> uncategorize (f b) -- これも不要
uncategorize ar = [ (x,i) | (i,xs) <- assocs ar, x <- xs ]

-- | shrinkDB can be used instead of mergesortDepthWithBy when you want to shrink each depth in different ways using different annotations.
shrinkDB :: (k->k->k) -> (k -> k -> Maybe Ordering) -> DBound k -> DBound k
shrinkDB combiner comparer = zipDepthDB $ shrink combiner comparer -- これも不要
shrink   combiner comparer = \b ts -> uncategorize $ fmap (mergesortWithByBot combiner comparer) $ categorize b ts

{-  元々こっちで定義してたけど，zipDepthDBを使った方が良さそうなので．
-- aはあらかじめannotateしたものを用いる
categorizeDB :: DBound a -> Int -> Array Int [a]
categorizeDB (DB f) b = accumArray (flip (:)) [] (0,b) $ map swap $ f b
uncategorizeDB :: (Int -> Array Int [a]) -> DBound a
uncategorizeDB f = DB $ \b -> [ (x,i) | (i,xs) <- assocs (f b), x <- xs ]

-- | shrinkDB can be used instead of mergesortDepthWithBy when you want to shrink each depth in different ways using different annotations.
shrinkDB :: (k->k->k) -> (k -> k -> Maybe Ordering) -> DBound k -> DBound k
-- shrinkDB combiner comparer db = uncategorizeDB (fmap (mergesortWithByBot combiner comparer) . categorizeDB db)
shrinkDB combiner comparer = uncategorizeDB . (.) (fmap (mergesortWithByBot combiner comparer)) . categorizeDB
-- Control.Monad.Instancesにinstance Functor (a->) where fmap = (.) が定義されている．どっちでもいいはずだけど，下の方が綺麗かなと．
-}

swap (b,x) = (x,b)

newtype DBound  a = DB  {unDB :: Int -> Bag (a, Int)}
newtype DBoundT m a = DBT {unDBT :: Int -> m (Bag (a, Int))}
instance Applicative DBound where
    pure x = DB $ \n -> [(x,n)]
    (<*>)  = ap
instance Monad DBound where
    return = pure
    DB p >>= f = DB $ \n -> [ (y,s) | (x,r) <- p n, (y,s) <- unDB (f x) r ]
instance (Functor m, Monad m) => Applicative (DBoundT m) where
    pure x = DBT $ \n -> return [(x,n)]
    (<*>)  = ap
instance (Functor m, Monad m) => Monad (DBoundT m) where
    return      = pure
    DBT p >>= f = DBT $ \n -> do ts <- p n
                                 tss <- mapM (\(x,r) -> unDBT (f x) r) ts
                                 return $ concat tss
instance Alternative DBound where
    empty = mzero
    (<|>) = mplus
instance MonadPlus DBound where
    mzero               = DB $ \_ -> []
    DB p1 `mplus` DB p2 = DB $ \n -> p1 n ++ p2 n
instance (Functor m, Monad m) => Alternative (DBoundT m) where
    empty = mzero
    (<|>) = mplus
instance (Functor m, Monad m) => MonadPlus (DBoundT m) where
    mzero               = DBT $ \_ -> return []
    DBT p1 `mplus` DBT p2 = DBT $ \n -> liftM2 (++) (p1 n) (p2 n)
instance Delay DBound where
    delay (DB p) = DB $ \n -> case n of 0   -> []
                                        n   -> p (n-1)
    ndelay i (DB p) = DB $ \n -> if n<i then [] else p (n-i)
    getDepth = DB $ \n -> [ (d, n-d) | d <- [0..n] ]
instance Monad m => Delay (DBoundT m) where
    delay (DBT p) = DBT $ \n -> case n of 0   -> return []
                                          n   -> p (n-1)
    ndelay i (DBT p) = DBT $ \n -> if n<i then return [] else p (n-i)
instance Search DBound where
    toRc   (DB p) = Rc $ \n -> [ x | (x,0) <- p n ]
    fromRc (Rc p) = DB $ \n -> [ (x,n-m) | m <- [0..n], x <- p m ]

    toMx (DB p) = Mx [ [ x | (x,0) <- p n ] | n <- [0..] ]
    fromMx (Mx xss) = DB $ \n -> concat $ zipWith (\r xs -> map (\x->(x,r)) xs) [n,n-1..0] xss
    fromDB = id
    fromDF xs = DB $ \n -> [ (x,n) | x <- xs ]
    toDF = toDF . toMx
    mapDepth f (DB g) = DB $ \d -> case unzip $ g d of (xs, is) -> zip (f xs) is
    catBags (DB f) = DB (\d -> [ (x,i) | (xs,i) <- f d, x <- xs ])
    mergesortDepthWithBy combiner rel = mapDepthDB (mergesortWithBy (\ (k,i) (l,_) -> (combiner k l, i))
                                                                    (\ (k,i) (l,j) -> case compare j i of EQ -> rel k l -- Cheaper Int comparison is done in advance.
                                                                                                          c  -> c))     -- Shallower elements come earlier.
    ifDepth pred (DB t) (DB f) = DB fun
        where fun depth | pred depth = t depth
                        | otherwise  = f depth

dbtToRcT (DBT p) = RcT $ \n -> do t <- p n
                                  return [ x | (x,0) <- t ]

instance (Functor m, Monad m) => Search (DBoundT m) where
    toRc   = error "No toRc for DBoundT."
    fromRc (Rc p) = DBT $ \n -> return [ (x,n-m) | m <- [0..n], x <- p m ]

    toMx = error "No toMx for DBoundT"
    fromMx (Mx xss) = DBT $ \n -> return $ concat $ zipWith (\r xs -> map (\x->(x,r)) xs) [n,n-1..0] xss
    fromDB (DB p) = DBT $ \n -> return $ p n
    fromDF xs = DBT $ \n -> return [ (x,n) | x <- xs ]
    toDF = error "No toDF for DBoundT"
    mapDepth f (DBT g) = DBT $ \d -> g d >>= \gd -> case unzip $ gd of (xs, is) -> return $ zip (f xs) is
    catBags (DBT f) = DBT (\d -> f d >>= \fd -> return [ (x,i) | (xs,i) <- fd, x <- xs ])
    ifDepth pred (DBT t) (DBT f) = DBT fun
        where fun depth | pred depth = t depth
                        | otherwise  = f depth
#ifdef QUICKCHECK
-- 0からか1からかでややこしいので，一応quickCheckしておくべし．
prop_fromMxToMx, prop_fromRcToRc :: DBound Int -> Int -> Property
prop_fromMxToMx = \db d -> d>=0 ==> sort (unDB (fromMx (toMx db)) d) == sort (unDB db d) -- passed 100 tests
prop_fromRcToRc = \db d -> d>=0 ==> sort (unDB (fromRc (toRc db)) d) == sort (unDB db d) -- passed 100 tests

prop_toMxFromMx = \mx d -> (d>=0 && length (unMx mx) >= d) ==> take d (map sort (unMx (toMx (fromMx mx :: DBound Int)))) == take d (map sort (unMx mx)) -- passed 100 tests
prop_toRcFromRc = \rc d -> d>=0 ==> sort (unRc (toRc (fromRc rc :: DBound Int)) d) == sort (unRc rc d) -- passed 100 tests
#endif

-- Dunno if "Memoable" is a correct English. Or maybe I should use IsMemoOf?
class (Search n) => Memoable m n where -- なんかmをmonadにするのが面倒になってきたっていうか，その必要ないでしょ．
    tabulate  :: n a -> m a
    applyMemo :: m a -> n a
instance Memoable Matrix Recomp where
    tabulate  (Rc f)   = Mx $ map f [0..]
    applyMemo (Mx xss) = Rc (xss!!)
instance Memoable DBMemo DBound where
    tabulate  (DB  f)   = DBM $ map f [0..]
    applyMemo (DBM xss) = DB (xss!!)

newtype DBMemo a = DBM {unDBM :: Stream (Bag (a,Int))}
{-
instance Monad DBMemo where
    return x = tabulate $ return x -- コンパイル通る?
             -- = DBM $ map (\n->[(x,n)]) [0..]
    DBM p >>= f = DBM $ 
-}


\end{code}

\begin{code}
test'' = mconcat (unMx test')
test' = do x <- Mx [return x | x<-[1..]]
           y <- Mx [return y | y<-[1..]]
           guard (x*y==30)
           return (x,y)

main = print test''
\end{code}
