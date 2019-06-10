-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE CPP #-}
#define CHTO
module MagicHaskeller.ClassifyDM(filterDM, filterList, filterListDB, filterDMIO, spreexecuteDM) where -- , filterDMTI) where

import Control.Monad.Search.Combinatorial
import Data.Maybe

import MagicHaskeller.Instantiate
import MagicHaskeller.Types
import MagicHaskeller.TyConLib
import MagicHaskeller.DebMT
import MagicHaskeller.MyDynamic
#ifdef CHTO
import System.IO.Unsafe
import MagicHaskeller.TimeOut
import Data.IORef
#endif
import MagicHaskeller.T10(mergesortWithBy, mergesortWithByBot, mergesortWithByBotIO)
import MagicHaskeller.PriorSubsts
import MagicHaskeller.Classify(opreexecute, ofilterDB, CmpBot, cmpBot, cmpBotIO) -- ofilterDB はこっちで定義されていてもいいようなもの．

import MagicHaskeller.Expression

import MagicHaskeller.ProgramGenerator(Common(..))
import MagicHaskeller.Options(Opt(..))

-- import Data.MapByBot

-- sortWithByBot f cmp = Data.MapByBot.elems . Data.MapByBot.fromListWith cmp (flip f) . map (\k -> (k,k))
sortWithByBot = mergesortWithByBot

select :: DBound ([[Dynamic]], AnnExpr) -> DBound ([Dynamic], AnnExpr)
-- select (DB f) = DB $ \n -> map (\((xss,ae),i) -> (((xss!!n), ae),i)) $ f n
select = zipDepthDB $ \d -> map (\((xss,ae),i) -> (((xss!!d), ae),i))

spreexecuteDM :: (Dynamic->Dynamic) -> [[Dynamic]] -> AnnExpr -> ([[Dynamic]], AnnExpr)
spreexecuteDM uncurrier rnds e@(AE _ dyn) = let f = uncurrier dyn in (map ({- forceList . -} map (dynAppErr "in ClassifyDM.spreexecuteDM" f)) rnds,  e)

sprDM :: (Dynamic->Dynamic) -> [[Dynamic]] -> AnnExpr -> Int -> ([Dynamic], AnnExpr)
sprDM unc rnds e db = case spreexecuteDM unc rnds e of (xss, ae) -> (xss!!db, ae)

forceList :: [a] -> [a]
forceList []        = []
forceList xs@(y:ys) = y `seq` forceList ys `seq` xs

-- filterList is convenient if inter-depth filtration is unnecessary (e.g. when you want to do complementary filtration).
filterList :: Common -> Type -> Int -> [AnnExpr] -> [AnnExpr]
filterList cmn typ db
    = case typeToRandomsOrdDM (nrands $ opt cmn) (tcl cmn) (rt cmn) typ of
        Nothing         -> id
        Just ([], op)   -> -- fmap snd . ofilterDB op . fmap opreexecute
                           sortWithByBot const (\(AE _ k) (AE _ l) -> cmpBot (op, opt cmn) k l)
        Just (rndss,op) -> -- fmap snd . sfilterDM (nrands $ opt cmn) op . select . fmap (spreexecuteDM (uncurryDyn (mkUncurry $ tcl cmn) typ) rndss)
                           map snd .
                           sortWithByBot const
                                              (nthCompareBot (nrands $ opt cmn) db (op, opt cmn)) .
                           map (\ae -> sprDM (uncurryDyn (mkUncurry $ tcl cmn) typ) rndss ae db)
filterListDB ::  Common -> Type -> [AnnExpr] -> DBound [AnnExpr]
filterListDB cmn typ aes
    = DB $ \db -> [(filterList cmn typ db aes,db)]

filterDM :: DB m => Common -> Type -> m AnnExpr -> m AnnExpr
filterDM cmn typ
    = case typeToRandomsOrdDM (nrands $ opt cmn) (tcl cmn) (rt cmn) typ of
        Nothing         -> id
        Just ([], op)   -> -- fmap snd . ofilterDB op . fmap opreexecute
                           mapDepthDB $ sortWithByBot const (\((AE _ k),_) ((AE _ l),_) -> cmpBot (op, opt cmn) k l)
        Just (rndss,op) -> -- fmap snd . sfilterDM (nrands $ opt cmn) op . select . fmap (spreexecuteDM (uncurryDyn (mkUncurry $ tcl cmn) typ) rndss)
                           zipDepthDB (\d -> map (\((_dyns,ae),i) -> (ae,i)) .
                                             sortWithByBot (\x@(_,i) y@(_,j) -> if i<j then y else x)
                                                                (\(k,_) (l,_) -> nthCompareBot (nrands $ opt cmn) d (op, opt cmn) k l) .
                                             map (\(ae,i) -> (sprDM (uncurryDyn (mkUncurry $ tcl cmn) typ) rndss ae d, i)))

filterDMIO :: Common -> Type -> DBound AnnExpr -> DBoundT IO AnnExpr
filterDMIO cmn typ db
    = case typeToRandomsOrdDM (nrands $ opt cmn) (tcl cmn) (rt cmn) typ of
        Nothing         ->  fromDB db
        Just ([], op)   -> -- fmap snd . ofilterDB op . fmap opreexecute
                           DBT $ \d -> mergesortWithByBotIO const (\((AE _ k),_) ((AE _ l),_) -> cmpBotIO (op, opt cmn) k l) $ unDB db d
        Just (rndss,op) -> -- fmap snd . sfilterDM (nrands $ opt cmn) op . select . fmap (spreexecuteDM (uncurryDyn (mkUncurry $ tcl cmn) typ) rndss)
                           DBT $ \d -> fmap (map (\ ((_dyns,ae),i) -> (ae,i))) $
                                       mergesortWithByBotIO (\x@(_,i) y@(_,j) -> if i<j then y else x)
                                                            (\ (k,_) (l,_) -> nthCompareBotIO (nrands $ opt cmn) d (op, opt cmn) k l)
                                                            (map (\(ae,i) -> (sprDM (uncurryDyn (mkUncurry $ tcl cmn) typ) rndss ae d, i)) $ unDB db d)

-- depth bound(つまり，Int->[(a,Int)]における引数のInt)の代わりに，depth boundからの距離(つまり，Int->[(a,Int)]におけるInt->[(a,ここのInt)])を使ってnrndsの何番目かを決めるもの．
-- filterDMと違って，同じdepth boundでも違う乱数を使うので，filterList同様depthを跨いだfiltrationができず，結果はいまいち．
-- ただし，dynamicな関数自体をメモ化すれば，格段にメモにヒットしやすくなるはず．
filterDMlite :: Common -> Type -> DBound AnnExpr -> DBound AnnExpr
filterDMlite cmn typ
    = case typeToRandomsOrdDM (nrands $ opt cmn) (tcl cmn) (rt cmn) typ of
        Nothing         -> id
        Just ([], op)   -> -- fmap snd . ofilterDB op . fmap opreexecute
                           mapDepthDB $ sortWithByBot const (\((AE _ k),_) ((AE _ l),_) -> cmpBot (op, opt cmn) k l)
        Just (rndss,op) -> -- fmap snd . sfilterDM (nrands $ opt cmn) op . select . fmap (spreexecuteDM (uncurryDyn (mkUncurry $ tcl cmn) typ) rndss)
                           zipDepthDB (\d -> map (\((_dyns,ae),i) -> (ae,i)) .
                                             shrink const (\k l -> nthCompareBot (nrands $ opt cmn) d (op, opt cmn) k l) d .
                                             map (\(ae,i) -> (sprDM (uncurryDyn (mkUncurry $ tcl cmn) typ) rndss ae i {- i, not d-}, i)))

listCmp :: Int -> (a->a->Ordering) -> [a] -> [a] -> Ordering
listCmp 0 cmp _      _      = EQ
listCmp n cmp []     []     = EQ
listCmp n cmp (x:xs) (y:ys) = case cmp x y of EQ -> listCmp (n-1) cmp xs ys
                                              c  -> c

nthCompareBot :: [Int] -> Int -> CmpBot a -> ([a],e) -> ([a],e) -> Maybe Ordering
nthCompareBot nrnds m cmp (xs,_) (ys,_) = listCmpBot (nrnds !! m) cmp xs ys
listCmpBot :: Int -> CmpBot a -> [a] -> [a] -> Maybe Ordering
#ifdef CHTO
listCmpBot len (cmp,pto) xs ys = unsafeWithPTOOpt pto $ listCmp len cmp xs ys
#else
listCmpBot len (cmp,_)   xs ys = Just $ listCmp len cmp xs ys
#endif

nthCompareBotIO :: [Int] -> Int -> CmpBot a -> ([a],e) -> ([a],e) -> IO (Maybe Ordering)
nthCompareBotIO nrnds m cmp (xs,_) (ys,_) = listCmpBotIO (nrnds !! m) cmp xs ys
listCmpBotIO :: Int -> CmpBot a -> [a] -> [a] -> IO (Maybe Ordering)
#ifdef CHTO
listCmpBotIO len (cmp,pto) xs ys = maybeWithTOOpt pto $ return $! listCmp len cmp xs ys
#else
listCmpBotIO len (cmp,_)   xs ys = return $ Just $ listCmp len cmp xs ys
#endif


sfilterDM :: [Int] -> CmpBot k -> DBound ([k],e) -> DBound ([k],e)
-- sfilterDM nrnds cmp (DB f) = DB $ \n -> sortWithByBot (\x@(_,i) y@(_,j) -> if i<j then y else x) (\(k,_) (l,_) -> nthCompareBot nrnds n cmp k l) (f n)
sfilterDM nrnds cmp = zipDepthDB $ \d -> sortWithByBot (\x@(_,i) y@(_,j) -> if i<j then y else x) (\(k,_) (l,_) -> nthCompareBot nrnds d cmp k l)
{-
uniqDM :: (k->k->Ordering) -> DBound ([[k]],e) -> DBound ([[k]],e)
uniqDM cmp (DB f) = DB $ \n -> uniqByBot (\x@(_,i) y@(_,j) -> if i<j then y else x) (\(k,_) (l,_) -> nthCompareBot n cmp k l) (f n)

uniqByBot combiner op = ubb
    where ubb (x:xs@(y:ys)) = case x `op` y of Nothing -> ubb ys
                                               Just EQ -> ubb (combiner x y : ys)
                                               Just LT -> x : ubb xs
                                               Just GT -> y : ubb (x:ys)
          ubb x = x

filterDMTI :: TyConLib -> RTrie -> Type -> DBoundT (PriorSubsts []) AnnExpr -> DBoundT (PriorSubsts []) AnnExpr
filterDMTI tcl rtrie typ
    = case typeToRandomsOrdDM tcl rtrie typ of
        Nothing         -> id
        Just ([],   op) -> fmap snd . ofilterDBTI op . fmap opreexecute
        Just (rndss,op) -> fmap snd . sfilterDMTI op . fmap (spreexecuteDM (uncurryDyn (mkUncurry tcl) typ) rndss)

ofilterDBTI :: Functor f => (k->k->Ordering) -> DBoundT f (k,e) -> DBoundT f (k,e)
ofilterDBTI cmp (DBT f) = DBT $ \n -> fmap (mergesortWithBy (\x@(_,i) y@(_,j) -> if i<j then y else x) (\((k,_),_) ((l,_),_) -> cmp k l))
                                           (f n)
sfilterDMTI :: (k->k->Ordering) -> DBoundT (PriorSubsts []) ([[k]],e) -> DBoundT (PriorSubsts []) ([[k]],e)
sfilterDMTI cmp (DBT f) = DBT $ \n -> fmap (sortWithByBot (\x@(_,i) y@(_,j) -> if i<j then y else x) (\(k,_) (l,_) -> nthCompareBot n cmp k l))
                                           (f n)
-}
