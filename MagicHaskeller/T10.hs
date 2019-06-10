-- 
-- (c) Susumu Katayama
--
module MagicHaskeller.T10 where
import Control.Monad
-- import MagicHaskeller.CoreLang
-- import PriorSubsts
import Data.List(partition, sortBy)
import Data.Monoid
import Data.Functor((<$>))

-- import MagicHaskeller.Types

liftList :: MonadPlus m => [a] -> m a
liftList = msum . map return


-- Was:  scan10 = mapDepth tokoro10 . scanl1 (++)
scan10 (xs:xss) = scanl (\x y -> tokoro10 (x ++ y)) (tokoro10 xs) xss

-- mergesortWithBy const cmp = map head . groupBy (\x y -> cmp x y == EQ) . sortBy cmp, except that mergesortWithBy is quicker when the domain includes lots of duplicates.
-- (If there are no duplicates, implementation with sortBy should be quicker.)
-- Implementation of mergesort by Ian Lynagh which is found in GHC distributions was useful for implementing this.
mergesortWithBy :: (k->k->k) -> (k->k->Ordering) -> [k] -> [k]
mergesortWithBy op cmp = mergesortWithByBot op (\x y -> Just (cmp x y))

mergesortWithByBot :: (k->k->k) -> (k -> k -> Maybe Ordering) -> [k] -> [k]
mergesortWithByBot op cmp = mergesortWithByBot' op cmp . map return

mergesortWithByBotIO :: (k->k->k) -> (k -> k -> IO (Maybe Ordering)) -> [k] -> IO [k]
mergesortWithByBotIO op cmp = mergesortWithByBot'IO op cmp . map (:[])

mergesortWithByBot' :: (k->k->k) -> (k -> k -> Maybe Ordering) -> [[k]] -> [k]
mergesortWithByBot' op cmp [] = []
mergesortWithByBot' op cmp [xs] = xs
mergesortWithByBot' op cmp xss = mergesortWithByBot' op cmp (merge_pairsBot op cmp xss)

mergesortWithByBot'IO :: (k->k->k) -> (k -> k -> IO (Maybe Ordering)) -> [[k]] -> IO [k]
mergesortWithByBot'IO op cmp []   = return []
mergesortWithByBot'IO op cmp [xs] = return xs
mergesortWithByBot'IO op cmp xss  = mergesortWithByBot'IO op cmp =<< (merge_pairsBotIO op cmp xss)

merge_pairsBot :: (k->k->k) -> (k -> k -> Maybe Ordering) -> [[k]] -> [[k]]
merge_pairsBot op cmp []          = []
merge_pairsBot op cmp [xs]        = [xs]
merge_pairsBot op cmp (xs:ys:xss) = mergeWithByBot op cmp xs ys : merge_pairsBot op cmp xss

merge_pairsBotIO :: (k->k->k) -> (k -> k -> IO (Maybe Ordering)) -> [[k]] -> IO [[k]]
merge_pairsBotIO op cmp []          = return []
merge_pairsBotIO op cmp [xs]        = return [xs]
merge_pairsBotIO op cmp (xs:ys:xss) = liftM2 (:) (mergeWithByBotIO op cmp xs ys) $ merge_pairsBotIO op cmp xss

mergeWithBy :: (k->k->k) -> (k->k->Ordering) -> [k] -> [k] -> [k]
mergeWithBy op cmp = mergeWithByBot op (\x y -> Just (cmp x y))

-- cmp returns Nothing when the comparison causes time-out.
mergeWithByBot :: (k->k->k) -> (k -> k -> Maybe Ordering) -> [k] -> [k] -> [k]
mergeWithByBot op cmp xs     []     = xs
mergeWithByBot op cmp []     ys     = ys
mergeWithByBot op cmp (x:xs) (y:ys)
    = case x `cmp` y of
        Just GT ->        y : mergeWithByBot op cmp (x:xs)   ys
        Just EQ -> x `op` y : mergeWithByBot op cmp    xs    ys
        Just LT -> x        : mergeWithByBot op cmp    xs (y:ys)
        Nothing -> mergeWithByBot op cmp xs ys
-- Actually it is questionable if we may remove both of the expressions compared just because comparison between them fails, because only one of them might be responsible.

-- cmp returns Nothing when the comparison causes time-out.
mergeWithByBotIO :: (k->k->k) -> (k -> k -> IO (Maybe Ordering)) -> [k] -> [k] -> IO [k]
mergeWithByBotIO op cmp xs     []     = return xs
mergeWithByBotIO op cmp []     ys     = return ys
mergeWithByBotIO op cmp (x:xs) (y:ys)
    = do mbo <- x `cmp` y 
         case mbo of
           Just GT ->        (y :) <$> mergeWithByBotIO op cmp (x:xs)   ys
           Just EQ -> (x `op` y :) <$> mergeWithByBotIO op cmp    xs    ys
           Just LT -> (x        :) <$> mergeWithByBotIO op cmp    xs (y:ys)
           Nothing -> mergeWithByBotIO op cmp xs ys
-- Actually it is questionable if we may remove both of the expressions compared just because comparison between them fails, because only one of them might be responsible.

diffSortedBy _  [] _  = []
diffSortedBy _  vs [] = vs
diffSortedBy op vs@(c:cs) ws@(d:ds) = case op c d of EQ -> diffSortedBy op cs ds
                                                     LT -> c : diffSortedBy op cs ws
                                                     GT -> diffSortedBy op vs ds
diffSortedByBot _  [] _  = []
diffSortedByBot _  vs [] = vs
diffSortedByBot op vs@(c:cs) ws@(d:ds) = case op c d of
         Just EQ -> diffSortedByBot op cs ds
         Just LT -> c : diffSortedByBot op cs ws
         Just GT -> diffSortedByBot op vs ds
--         Nothing -> c : diffSortedByBot op cs ds -- I just do not know what is the best solution here, but when timeout happens, I temporarily believe @c@, and skip d.
         Nothing -> diffSortedByBot op cs ds -- The above turned out to be not a good solution, because when an error (or a timeout) happens, the expression repeatedly appears at each depth. See newnotes on Dec. 18, 2011


-- filters only emptySubst
tokoro10nil    :: Eq k => [([a],[k],i)] -> [([a],[k],i)]
tokoro10nil xs =  case partition (\ (_,k,_) -> k==[] ) xs of
                                        ([], diff) -> diff
                                        (same@((_,_,i):_), diff) -> (concat (map (\ (a,_,_) -> a) same), [], i) : diff
{-
-- ちゃんと計算してないけど，O(n^2)くらい？ ただ，要素数nは少ないっぽいのでこっちの方が速いかも
tokoro10             :: Eq k => [([a],k,i)] -> [([a],k,i)]
tokoro10 []          =  []
tokoro10 ((es,k,i):xs) =  case partition (\ (_,k',_) -> k==k' ) xs of
                                        (same, diff) -> (es ++ concat (map (\ (a,_,_) -> a) same), k, i) : tokoro10 diff
-}
{- quicksortの変形
tokoro10             :: (Eq k, Ord k) => [([a],k,i)] -> [([a],k,i)]
tokoro10 []             = []
tokoro10 ((t@(x,k,i)):ts) = case partition3 k ts of (ls,es,gs) -> tokoro10 ls ++ (x ++ concat es, k, i) : tokoro10 gs
partition3     :: (Eq k, Ord k) => k -> [(a,k,i)] -> ([(a,k,i)],[a],[(a,k,i)])
-- {-# INLINE partition3 #-}
partition3 k ts = foldr (select3 k) ([],[],[]) ts
select3 k t@(x,k',_) (ls,es,gs) = case k' `compare` k of LT -> (t:ls,   es,   gs)
                                                         EQ -> (  ls, x:es,   gs)
                                                         GT -> (  ls,   es, t:gs)
-}

-- merge sort could be much faster.
tokoro10             :: (Monoid a, Eq k, Ord k) => [(a,k,i)] -> [(a,k,i)]
tokoro10 = mergesortWithBy (\(xs,k,i) (ys,_,_) -> (xs `mappend` ys, k, i)) (\ (_,k,_) (_,l,_) -> k `compare` l)
{- sortはしないけど，実はこっちの方が効率が悪いのでは? 長さに対して2乗のオーダーになりそう．ソートすれば，O(n log n)（後半はO(n)ですみそう）しかも，(\\\)を使うにはソートしてないとだめ．
tokoro10 :: (Eq k, Ord k) => [([a],k,i)] -> [([a],k,i)]
tokoro10 ((t@(xs,k,i)):ts) = case partition (\ (_,k',_) -> k'==k) ts of (es,ns) -> (xs ++ concat (map (\ (a,_,_) -> a) es),  k,  i) : tokoro10 ns
-}

-- Moved from DebMT.lhs
-- ? means Maybe
[]     !? n = Nothing
(x:xs) !? 0 = Just x
(x:xs) !? n = xs !? (n-1)


{-
-- nlambda n e = iterate Lambda e !! nの方が美しい？効率は？
nlambda 0 e = e
nlambda n e = Lambda $ nlambda (n-1) e
-}