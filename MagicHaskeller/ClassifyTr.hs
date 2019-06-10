-- 
-- (c) Susumu Katayama
--
module MagicHaskeller.ClassifyTr where
import MagicHaskeller.T10
import Control.Monad.Search.Combinatorial
import Control.Monad

import MagicHaskeller.TimeOut

-- Just for filterTr
import MagicHaskeller.MyDynamic
import MagicHaskeller.Instantiate
import MagicHaskeller.Expression
import MagicHaskeller.ProgramGenerator(Common(..))
import MagicHaskeller.Options(Opt(..))
import MagicHaskeller.Types
import MagicHaskeller.ClassifyDM(spreexecuteDM)
import MagicHaskeller.Classify(cmpBot)

import Debug.Trace

filterTr :: Common -> Type -> Matrix AnnExpr -> (Stream (Forest ([Dynamic], AnnExpr)), Stream (Forest ([Dynamic], AnnExpr)), Matrix AnnExpr)
filterTr cmn typ
    = case typeToRandomsOrdDM nrnds (tcl cmn) (rt cmn) typ of
        Nothing         -> \x -> (undefined, undefined, x)
        Just ([], op)   -> \x -> (undefined, undefined, mapDepth (mergesortWithByBot const (\(AE _ k) (AE _ l) -> cmpBot (op, opt cmn) k l)) x)
        Just (rndss,op) -> -- trace ("take 1 rndss = "++show (take 1 rndss)) $ -- nrndssを表示しようとするとbehaviourが変わる．
                           -- trace ("ty = "++show typ++" and take 10 nrands = "++show (take 10 $ nrands $ opt cmn)) $
                           let finrndss = zipWith take nrnds rndss
                               unsafeCmp ks ls = unsafeWithPTOOpt (opt cmn) (bagCmp op ks ls)
                           in mkTip unsafeCmp . fmap (spreexecuteDM (uncurryDyn (mkUncurry $ tcl cmn) typ) finrndss)
      where nrnds = nrands $ opt cmn
bagCmp :: (a->a->Ordering) -> [a] -> [a] -> Ordering
bagCmp _   []     []     = EQ
bagCmp cmp (x:xs) (y:ys) = case cmp x y of EQ -> bagCmp cmp xs ys
                                           c  -> c
-- other cases should not happen

type Forest k = [Tree k]
data Tree k = Tr k (Forest k) deriving Show

prop_mkTip mx = let mxx = fmap (\(f,e) -> (map f [0..], e)) mx
                    (_,_,res) = mkTip (\ks ls -> Just (compare ks ls)) mxx
                in take 10 (unMx res) == take 10 (unMx res)

mkTip :: -- Show expr =>
         (key->key->Maybe Ordering) -> Matrix (Stream key, expr) -> (Stream (Forest (key, expr)), Stream (Forest (key, expr)), Matrix expr)
mkTip cmp mx = let fs  = mkForests cmp mx
                   cmpFst (x,_) (y,_) = cmp x y
                   acc = accumulateForests cmpFst fs
                   filtered = fmap snd $ difference cmpFst fs ([]:acc)
               in (fs, acc, filtered)


mkForests :: (k->k->Maybe Ordering) -> Matrix (Stream k, r) -> Stream (Forest (k,r))
mkForests cmp (Mx xss) = map (mkForest cmp) xss
{-
mkForests :: Show r => (k->k->Ordering) -> Matrix (Stream k, r) -> Stream (Forest (k,r))
mkForests cmp (Mx xss) = map (\xs -> trace ("before filtration"++ show (map snd xs)) $
                                     mkForest cmp xs) xss
-}
mkForest :: (k->k->Maybe Ordering) -> [(Stream k,r)] -> Forest (k,r) -- Stream kなので，[(Stream k,r)]をあらかじめソートできないことに注意．
mkForest cmp = map (\(k,ts@((_,r):_)) -> Tr (k, r) (mkForest cmp ts)) . mergesortWithByBot (\(k,xs) (_,ys) -> (k,xs++ys)) (\(k,_) (l,_) -> cmp k l) . map (\(k:ks, r) -> (k,[(ks,r)]))
-- もう一つの実装方法: どっちが効率的かは? mkForest cmp [(ks,r)]は[mkTree cmp ks r]みたいにspecializeしたものを用意した方がいいかも．
-- mkForest cmp = map (\(Tr k ts@(Tr (_,r) _ : _)) -> Tr (k, r) ts) . mergesortWithBy (\(Tr k xs) (Tr _ ys) -> Tr k (mergeForests xs ys)) (\(Tr (k,_) _) (Tr (l,_) _) -> cmp k l) . map (\(k:ks, r) -> (k, mkForest cmp [(ks,r)]))


accumulateForests :: (k->k->Maybe Ordering) -> Stream (Forest k) -> Stream (Forest k)
accumulateForests cmp forests = cumulatives
   where cumulatives = zipWith (mergeForests cmp) ([]:cumulatives) forests
-- mergeってのはmonoid的にはmappendなワケ
mergeForests :: (k->k->Maybe Ordering) -> Forest k -> Forest k -> Forest k
mergeForests _   [] trs = trs
mergeForests _   tls [] = tls
mergeForests cmp tls@((tl@(Tr kl fl)) : rls)
                 trs@((tr@(Tr kr fr)) : rrs)
                    = case cmp kl kr of Just LT -> tl                   : mergeForests cmp rls trs
                                        Just GT -> tr                   : mergeForests cmp tls rrs
                                        _ -> Tr kl (mergeForests cmp fl fr) : mergeForests cmp rls rrs

difference :: (k->k->Maybe Ordering) -> Stream (Forest k) -> Stream (Forest k) -> Matrix k
-- difference :: Show x => ((k,x)->(k,x)->Ordering) -> Stream (Forest (k,x)) -> Stream (Forest (k,x)) -> Matrix (k,x)
difference cmp mx cumulative
  = -- mapDepth (\xs -> trace ("after filtration" ++ show (map snd xs)) xs)$
    foldr (\x y -> x `mplus` delay y) undefined $ zipWith (diff cmp) mx cumulative
diff :: (k->k->Maybe Ordering) -> Forest k -> Forest k -> Matrix k
diff _   []  _  = mzero
diff _   tls [] = foldr1 mplus $ map flattenTr tls
diff cmp tls@((tl@(Tr kl fl)) : rls)
         trs@(     Tr kr fr   : rrs)
                   = case cmp kl kr of Just LT -> flattenTr tl                                `mplus` diff cmp rls trs
                                       Just EQ -> delay (removeFirstOfFirst (diff cmp fl fr)) `mplus` diff cmp rls rrs
                                       _  ->                                                     diff cmp tls rrs
flattenTr :: Tree k -> Matrix k
flattenTr (Tr k f) = [k] `consMx` removeFirstOfFirst (msum $ map flattenTr f)

removeFirstOfFirst mx@(Mx ([]:xss))  = mx
removeFirstOfFirst (Mx ((_:xs):xss)) = Mx $ xs:xss -- これが長子を取り除く


{-
*MagicHaskeller.ClassifyTr> case mkTip compare (Mx (((repeat 1, 1):(repeat 1, 2):[]) : repeat [])) of (_,_,x) -> x
Mx {unMx = [[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],
-}
