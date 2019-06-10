-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE MagicHash, CPP #-}
module MagicHaskeller.Classify(randomTestFilter, filterBF, filterRc, filterDB -- , filterDBPos
               , ofilterDB, opreexecute, CmpBot, cmpBot, cmpBotIO -- used by ClassifyDM.hs
               , FiltrableBF
               ) where
#define CHTO
import Control.Monad.Search.Combinatorial
-- import Types(Subst) -- Substにspecializeする必要はないけど．
import Data.Maybe
import Control.Monad(mplus)

import MagicHaskeller.Instantiate
import GHC.Exts(unsafeCoerce#)
-- import Data.Array((!))
import MagicHaskeller.Execute(unsafeExecute) -- :: CoreExpr -> a
import MagicHaskeller.TyConLib
import MagicHaskeller.Types
import MagicHaskeller.DebMT
import MagicHaskeller.MyDynamic
#ifdef CHTO
import System.IO.Unsafe
import MagicHaskeller.TimeOut
import Control.Concurrent(yield)
import Data.IORef
#endif
import MagicHaskeller.T10(mergesortWithBy, mergeWithBy, mergesortWithByBot, mergeWithByBot, diffSortedBy, diffSortedByBot)

#ifdef DEBUG
import Test.QuickCheck
#endif

import MagicHaskeller.Expression

import MagicHaskeller.ProgramGenerator
import MagicHaskeller.Options

import Language.Haskell.TH.Ppr
-- import ReadLambdaExpr(exprToTHExp)
-- import ToString

import System.IO
-- import Debug.Trace
trace str e = e


-- randomTestFilter :: MemoDeb -> Matrix CoreExpr -> Matrix CoreExpr, but I do not like to import ProgGen.
-- randomTestFilter (_,_,tcl,rtrie) typ = toMx . filterDB' id tcl rtrie typ . fromMx
randomTestFilter md = filterBF (extractTCL md) (extractRTrie md) (opt $ extractCommon md)
filterBF :: FiltrableBF m => TyConLib -> RTrie -> Opt () -> Type -> m AnnExpr -> m AnnExpr
filterBF tcl rtrie pto typ
    = case trace (show typ) $
           typeToRandomsOrd tcl rtrie typ of
                           Nothing        -> id
                           Just ([],  op) -> fmap snd . ofilter (op,pto) . fmap opreexecute
--                           Just (rnds,op) -> unscanl . fmap snd . repEqClsBy_simple op . fmap (spreexecute rnds) -- Feb. 10, 2007のnotesの最後の辺り参照．Matrixの場合．
                           Just (rnds,op) -> fmap snd . sfilter (op,pto) . fmap (spreexecute (uncurryDyn (mkUncurry tcl) typ) rnds)
spreexecute uncurrier rnds e@(AE _ dyn) = let f = uncurrier dyn in (map (dynAppErr "in Classify.spreexecute" f) rnds, e)

opreexecute :: AnnExpr -> (Dynamic, AnnExpr)
opreexecute e@(AE _ dyn) = (dyn, e)

unscanl :: Ord e => Matrix e -> Matrix e
unscanl = unscanlBy compare

type CmpBot k = (k->k->Ordering, Opt ()) -- Comparison that can return a bottom (i.e., either timeout or error).

class Search m => FiltrableBF m where
    sfilter :: CmpBot k -> m ([k],e) -> m ([k],e)
    ofilter :: CmpBot k -> m (k,e) -> m (k,e)
instance FiltrableBF Matrix where
    sfilter = sfilterMx
    ofilter = ofilterMx
instance FiltrableBF Recomp where
    sfilter = sfilterRc
    ofilter = ofilterRc
instance FiltrableBF DBound where
    sfilter = sfilterDB
    ofilter = ofilterDB

-- x この[([k],e)]の部分は，本当のところStreamTrieで実装した方が効率的なはず．

sfilterMx :: CmpBot k -> Matrix ([k],e) -> Matrix ([k],e)
-- sfilter op (Mx xss) = unscanlByList op $ foldr (mergeMxBy op) undefined (map (repEqClsBy op) xss)
-- x これだと，mergeMxByがプログラムサイズのことを知らずに最初の1個のkeyの比較から始めてしまう ... と思ったけど実はそうでもない．mergeMxByが(Mx (_:ys))のように先頭をdropするのがポイントで，たとえば(map repEqClsBy xss) !! nは先頭のn個分が(結果として)dropされることになる．
-- x やっぱダメ．
-- x 多分問題は，eqClsByは深さ２以降も深さ１にdependしていて，そうなるとサイズ２以降のプログラムが...みたいな感じ
sfilterMx op mx = trace "sfilterMx" $
                      unscanlByList op $ repEqClsBy op mx

filterDB :: TyConLib -> RTrie -> Opt () -> Type -> DBound AnnExpr -> DBound AnnExpr
filterDB = filterBF
{-
filterDBPos :: TyConLib -> RTrie -> Type -> DBound (Possibility AnnExpr) -> DBound (Possibility AnnExpr)
filterDBPos tcl rtrie typ
    = case typeToRandomsOrd tcl rtrie typ of
        Nothing        -> id
        Just ([], op)  -> fmap snd . ofilterDBPos op . fmap (\(x,s,i) -> (map opreexecute x, s, i))
        Just (rnds,op) -> fmap snd . sfilterDBPos op . fmap (\(x,s,i) -> (fmap (spreexecuteNTO (uncurryDyn (mkUncurry tcl) typ) rnds) x,  s,  i))
-}
filterRc :: TyConLib -> RTrie -> Opt () -> Type -> Recomp AnnExpr -> Recomp AnnExpr
filterRc = filterBF

-- x この[([k],e)]の部分は，本当のところStreamTrieで実装した方が効率的なはず．

sfilterRc :: CmpBot k -> Recomp ([k],e) -> Recomp ([k],e)
-- sfilter op (Mx xss) = unscanlByList op $ foldr (mergeMxBy op) undefined (map (repEqClsBy op) xss)
-- x これだと，mergeMxByがプログラムサイズのことを知らずに最初の1個のkeyの比較から始めてしまう ... と思ったけど実はそうでもない．mergeMxByが(Mx (_:ys))のように先頭をdropするのがポイントで，たとえば(map repEqClsBy xss) !! nは先頭のn個分が(結果として)dropされることになる．
-- x やっぱダメ．
-- x 多分問題は，eqClsByは深さ２以降も深さ１にdependしていて，そうなるとサイズ２以降のプログラムが...みたいな感じ
sfilterRc op mx = trace "sfilter" $
                     unscanlByListRc op $ repEqClsByRc op mx
{-
mergeReps :: (k->k->Ordering) -> Int -> [Matrix ([k],e)] -> Matrix ([k],e)
mergeReps op n ~(rs:rss) = trace "mergeReps" $
                           mergeMxBy op n rs (mergeReps op (n+1) rss)
-}


unscanlByList :: CmpBot k -> Matrix ([k],e) -> Matrix ([k],e)
unscanlByList op mx = case unMx mx of yss@(xs:xss) -> Mx (xs : zipWith3 (deleteListByList op) (tcnrnds op) xss yss)

unscanlByListMx :: CmpBot k -> Matrix ([k],e) -> Matrix ([k],e)
unscanlByListMx op mx = zipDepth3Mx (\dep -> deleteListByList op (fcnrnd op (1+dep))) mx (delay mx)

unscanlByListRc :: CmpBot k -> Recomp ([k],e) -> Recomp ([k],e)
unscanlByListRc op rc = zipDepth3Rc (\dep -> deleteListByList op (fcnrnd op (1+dep))) rc (delay rc)


deleteListByList cmp len xs ys = dlbBot (liftCompareBot len cmp) xs ys

comparers :: Int -> CmpBot a -> [([a],e) -> ([a],e) -> Maybe Ordering]
comparers m cmp = liftCompareBot m cmp : comparers (m+1) cmp

liftCompare :: Int -> (a->a->Ordering) -> ([a],e) -> ([a],e) -> Ordering
liftCompare m cmp (xs,_) (ys,_) = liftCmp m cmp xs ys
liftCmp :: Int -> (a->a->Ordering) -> [a] -> [a] -> Ordering
-- liftCmp len cmp xs ys = fromMaybe (error "liftCmp") $ liftCmpBot len cmp xs ys
liftCmp 0   cmp xs     ys     = EQ
liftCmp _   _   []     []     = EQ
liftCmp len cmp (x:xs) (y:ys) = trace "liftCmp" $
                                   case cmp x y of
                                                EQ -> trace "just eq" $
                                                           liftCmp (len-1) cmp xs ys
                                                c       -> trace "otherwise" 
                                                           c

liftCompareBot :: Int -> CmpBot a -> ([a],e) -> ([a],e) -> Maybe Ordering
liftCompareBot m cmp (xs,_) (ys,_) = liftCmpBot m cmp xs ys
liftCmpBot :: Int -> CmpBot a -> [a] -> [a] -> Maybe Ordering
#ifdef CHTO
liftCmpBot len (cmp,pto) xs ys = unsafeWithPTOOpt pto $ liftCmp len cmp xs ys
{-
                         | otherwise     =    liftCmpBot' len cmp xs ys
liftCmpBot' 0   _   _      _      = Just EQ
liftCmpBot' _   _   []     _      = Nothing
liftCmpBot' _   _   (_:_)  []     = Nothing
liftCmpBot' len cmp (x:xs) (y:ys) = trace "liftCmpBot" $
                                   case unsafePerformIO $ maybeWithTO pto $ return $ cmp x y of
                                                Just EQ -> trace "just eq" $
                                                           liftCmpBot' (len-1) cmp xs ys
                                                c       -> trace "otherwise" 
                                                           c
-}
cmpBot (cmp,pto) x y = unsafeWithPTOOpt pto $ cmp x y
cmpBotIO (cmp,pto) x y = maybeWithTOOpt pto $ return $! cmp x y
#else
liftCmpBot len (cmp,_pto) xs ys                 = Just $ liftCmp len cmp xs ys
cmpBot (cmp,_pto) x y = Just $ cmp x y
cmpBotIO (cmp,pto) x y = return $ Just $ cmp x y
#endif
-- dlb = deleteListBy

dlbBot cmps xs ys = diffSortedByBot cmps xs ys
dlb cmps xs ys = diffSortedBy cmps xs ys
{-
dlbBot cmps xs ys = diffSortedByBot cmps (mergesortWithByBot undefined cmps xs) (mergesortWithByBot undefined cmps ys)
dlb cmps xs ys = diffSortedBy cmps (mergesortWithBy undefined cmps xs) (mergesortWithBy undefined cmps ys)
-}

{-
repEqClsBy_simple :: (k->k->Ordering) -> Matrix ([k],e) -> Matrix ([k],e)
repEqClsBy_simple cmp (Mx xss) = Mx $ zipWith (\dep ys -> mergesortWithByBot const (liftCompareBot dep cmp) $ filterEligibles dep ys) cnrnds $ scanl1_recompute (++) xss
scanl1_recompute :: (a -> a -> a) -> [a] -> [a]
scanl1_recompute f xs = [ foldl1 f $ take i xs | i <- [1..] ]
-}

repEqClsBy_simple :: CmpBot k -> Matrix ([k],e) -> Matrix ([k],e)
repEqClsBy_simple cmp mx = Mx $ zipWith (\dep ys -> mergesortWithByBot const (liftCompareBot dep cmp) ys) (cnrnds cmp) $ unMx $ scanl1BF mx

repEqClsByMx :: CmpBot k -> Matrix ([k],e) -> Matrix ([k],e)
repEqClsByMx cmp mx = zipDepthMx (\dep ys -> let n = fcnrnd cmp dep in mergesortWithByBot const (liftCompareBot n cmp) ys) $ scanl1BF mx

repEqClsByRc :: CmpBot k -> Recomp ([k],e) -> Recomp ([k],e)
repEqClsByRc cmp mx = zipDepthRc (\dep ys -> let n = fcnrnd cmp dep in mergesortWithByBot const (liftCompareBot n cmp) ys) $ scanl1BF mx

eqClsBy_naive :: CmpBot a -> Matrix ([a],b) -> Matrix [([a],b)]
eqClsBy_naive cmp (Mx xss) = Mx $ zipWith (\dep ys -> ys /// liftCompareBot dep cmp) (cnrnds cmp) $ scanl1 (++) xss

{- 多少効率化しようかとも思ったけど，とりあえずは本当にnaiveにやる
eqClsBy_naive cmp mx =         scanl (mergeBy cmp) (eqClsByFstNs cmp mx)

scanlx cmp [a0,a1,...] = [a0, mergeBy 
-}


{-
ncmp = 5
fcnrnd = (1+ncmp+)
-}
fcnrnd (_,opt) = fcnrand opt
cnrnds  tup = map (fcnrnd tup) [0..]
tcnrnds tup = map (fcnrnd tup) [1..]

-- repEqClsBy cmp = [([k]の最初の1個のみを見たときの同値類分解の代表元たち), ([k]の最初の2個のみを見たときの同値類分解の代表元たち), ([k]の最初の3個のみを見たときの同値類分解の代表元たち), ....]
repEqClsBy :: CmpBot k -> Matrix ([k],e) -> Matrix ([k],e)
repEqClsBy cmp = trace "repEqClsBy" . 
                 fmap head . eqClsBy cmp
-- eqClsByの結果の深さn番目には，[k]の最初のn個をcmpで比較したときの同値関係による同値類分解が入っている．
-- x 深さ1でサイズ1なやつらを同値類分解 : 深さ1での分解結果を2文字目で同値類分解したヤツと，サイズ2のやつらを2文字分見て同値類分解したやつらをマージ : 深さ2での分解結果を3文字目で同値類分解した奴と，....
eqClsBy :: CmpBot a -> Matrix ([a],b) -> Matrix [([a],b)]
eqClsBy cb@(cmp,opt) mx = Mx $
                 scanl (\xs (n,ys) -> mergeBy (liftCompareBot n cb) (eqClsByNth cmp n xs) ys) ecb0 $ zip (tcnrnds cb) ecbs
{- scanlの1行の代わりにこっちを使ってた．
                 let result = ecb0 : zipWith3 (\n xs ys -> mergeBy (liftCompareBot n cmp) (eqClsByNth n xs) ys) (tail cnrnds) result ecbs
                 in result
-}
    where Mx (ecb0:ecbs) = eqClsByFstNs cb mx
-- n-2番目のequivalenceでのquotient setを元に，n-1番目のequivalenceで細分．むしろ，refineという関数を定義した方がよい?
eqClsByNth :: (a->a->Ordering) -> Int -> [[([a],e)]] -> [[([a],e)]]
eqClsByNth cmp n = concatMap ((/// (\ (xs,_) (ys,_) -> Just $ cmp (xs!!(n-1)) (ys!!(n-1)))))

eqClsByFstNs :: CmpBot a -> Matrix ([a],b) -> Matrix [([a],b)]
eqClsByFstNs cmp (Mx tss) = Mx $ zipWith eqClsByFstN (cnrnds cmp) tss
    where eqClsByFstN n = (/// liftCompareBot n cmp)

isLongEnough 0 _      = True
isLongEnough _ []     = False
isLongEnough n (x:xs) = isLongEnough (n-1) xs

-- This used to be used as a preprocessor of sorting, but such use turned out to be no use for efficiency and make timeout-related discussion more complicated. Search filterEligibles in notes.
filterEligibles :: Int -> [([k],e)] -> [([k],e)]
#ifdef CHTO
filterEligibles n = filter (isLongEnough n . fst)
#else
filterEligibles _ = id
#endif

mergeBy :: (k -> k -> Maybe Ordering) -> [[k]] -> [[k]] -> [[k]]
mergeBy cmp = mergeWithByBot (++) (\x y -> head x `cmp` head y)
-- この辺(mergeBy)のネーミングもいまいち

{-
mergeMxBy :: (k->k->Ordering) -> Int -> Matrix ([k],e) -> Matrix ([k],e) -> Matrix ([k],e)
mergeMxBy op len (Mx ~(xs:xss)) (Mx yss) = Mx (xs : zipWith3 (\i xs ys -> mergeBy (\ (ks,_) (ls,_) -> liftCmp i op ks ls) i (filterEligibles i xs) (filterEligibles i ys)) [len..] xss yss)
-- mergeはtrieにおけるunionByみたいな感じ．
mergeBy :: (k->k->Ordering) -> Int -> [k] -> [k] -> [k]
mergeBy op len xs ys = foldl (insertBy (\x y -> op x y == EQ)) xs ys
insertBy :: (k->k->Bool) -> [k] -> k -> [k]
insertBy op xs y = case filter (op y) xs of [] -> y:xs -- 先頭に逆順に加えてOKだったとは思うのだが，一応気を付ける
                                            _  -> xs
-}

sfilterDB :: CmpBot k -> DBound ([k],e) -> DBound ([k],e)
sfilterDB cmp (DB f) = DB $ \n -> mergesortWithByBot (\x@(_,i) y@(_,j) -> if i<j then y else x) (\(k,_) (l,_) -> liftCompareBot (fcnrnd cmp n) cmp k l) (f n)
ofilterDB :: CmpBot k -> DBound (k,e) -> DBound (k,e)
ofilterDB cmp (DB f) = DB $ \n -> mergesortWithByBot const (\((k,_),_) ((l,_),_) -> cmpBot cmp k l)  (f n)

ofilterRc :: CmpBot k -> Recomp (k,e) -> Recomp (k,e)
ofilterRc cmp rc = let sorted = mapDepth (mergesortWithByBot const op) rc
                       cumulative = scanlRc (mergeWithByBot const op) [] sorted
                   in zipDepth3Rc (\_ -> diffSortedByBot op) sorted cumulative
    where op (k,_) (l,_) = cmpBot cmp k l

ofilterMx :: CmpBot k -> Matrix (k,e) -> Matrix (k,e)
ofilterMx cmp (Mx xss) = let sorted = map (mergesortWithByBot const op) xss
                             cumulative = scanl (mergeWithByBot const op) [] sorted
                         in Mx $ zipWith (diffSortedByBot op) sorted cumulative
    where op (k,_) (l,_) = cmpBot cmp k l
{- こっちの定義だと，sortedではなくcumulativeから[]:cumulativeを引くので，ちょっと非効率
ofilterMx cmp (Mx xss) = unscanlBy op $ Mx $ scanl1 (mergeWithBy const op) $ map (mergesortWithBy const op) xss
    where op (k,_) (l,_) = cmp k l
-}
{-
ofilterMx cmp (Mx xss) = unscanlBy op $ Mx $ map (map head . (/// (\x y -> Just (op x y)))) $ scanl1 (++) xss
    where op (k,_) (l,_) = cmp k l
-}
unscanlBy :: (k->k->Ordering) -> Matrix k -> Matrix k
unscanlBy op (Mx yss@(xs:xss)) = Mx (xs : zipWith (diffSortedBy op) xss yss)

-- quotient set
(///) :: [a] -> (a->a->Maybe Ordering) -> [[a]]
ts /// cmp = mergesortWithByBot (++) (\x y -> head x `cmp` head y) $ map return ts


#ifdef DEBUG
-- Properties

-- prop_sfilter = \x y i j hoge -> i /= j  ==>  (head $ unMx $ sfilter compare $ Mx ([([i],x),([j],y)]:hoge)) == sortBy (\k l -> compare (fst k) (fst l)) [([i],x),([j],y)::([Int],Int)]
prop_sfilter_exhaustive = \yss -> all longenough (concat yss) &&  unique (concat yss) && length yss < 6 ==> let xss = map (map (\x -> (x,()))) yss in  length (concat $ take 10 $ unMx $ sfilter (compare,Nothing) $ Mx (xss ++ repeat [])) == length (concat xss :: [([Int],())])

-- example: quickCheck (prop_sfilter 10 :: Propsf Int)
type Propsf a = [[[a]]] -> Property
prop_sfilter :: Ord a => Int -> Propsf a
prop_sfilter m = \yss -> length yss < m && all longenough (concat yss) ==> let xss = map (map (\x -> (x,()))) yss in (concat xss /// liftCompareBot m (compare,Nothing)) == (concat (take m (unMx $ sfilter (compare,Nothing) (Mx (xss ++ repeat [])))) /// liftCompareBot m (compare,Nothing))

unique [] = True
unique (x:xs) = all (/=x) xs && unique xs
longenough ks = length ks > 3+ncmp
#endif
