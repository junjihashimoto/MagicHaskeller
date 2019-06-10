-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE CPP #-}
module MagicHaskeller.Expression(module MagicHaskeller.Expression, module MagicHaskeller.ExprStaged, CoreExpr) where
import MagicHaskeller.CoreLang
import MagicHaskeller.MyDynamic
import MagicHaskeller.Execute
-- import Reduce
import MagicHaskeller.Types
import MagicHaskeller.ExprStaged
import MagicHaskeller.Combinators

import MagicHaskeller.T10
import Control.Monad
import Data.Array((!), array)
import MagicHaskeller.ReadDynamic
import MagicHaskeller.TyConLib(defaultTCL, TyConLib)
-- import Debug.Trace

import MagicHaskeller.Instantiate(RTrie, uncurryDyn, uncurryTy, mkUncurry, mkCurry, curryDyn)
import MagicHaskeller.DebMT

import qualified Data.Set as S
import qualified Data.IntMap as IM

import Data.List
import Data.Array

-- AnnExpr remembers each Dynamic corresponding to the CoreExpr.
data AnnExpr = AE CoreExpr Dynamic deriving Show
instance Eq AnnExpr where
    a == b = toCE a == toCE b
instance Ord AnnExpr where
    compare a b = compare (toCE a) (toCE b)

-- MemoExpr further memoizes each dynamic function.
data MemoExpr = ME CoreExpr Dynamic -- memo table
                            Dynamic -- memoized function
aeToME :: TyConLib -> RTrie -> Type -> AnnExpr -> MemoExpr
aeToME tcl (_,_,_,_,mtdd) ty@(_:->_) (AE ce dyn)
    = case lookupMT mtdd argty of (m,a) -> let me@(ME _ memo _) = ME ce (dynApp m udyn) (curryDyn cur ty $ dynApp a memo)
                                           in me  -- make sure to use the memo table in the datatype by using letrec, or the table will be recomputed.
    where argty:->_ = uncurryTy tcl ty
          unc   = mkUncurry tcl
          udyn  = uncurryDyn unc ty dyn
          cur   = mkCurry tcl
aeToME _   _              _          (AE ce dyn) = ME ce undefined dyn -- non-functional case

meToAE :: MemoExpr -> AnnExpr
meToAE (ME ce _ f) = AE ce f

{-# SPECIALIZE mkHead :: (CoreExpr->Dynamic) -> Int -> Int -> CoreExpr -> e #-}
{-# SPECIALIZE mkHead :: (CoreExpr->Dynamic) -> Int8 -> Int8 -> CoreExpr -> e #-}
class (Ord e, Show e) => Expression e where
    mkHead         :: (Integral i, Integral j) => (CoreExpr->Dynamic) -> i -> j -> j -> CoreExpr -> e
    toCE           :: e -> CoreExpr
    fromCE         :: (CoreExpr -> Dynamic) -> CoreExpr -> e
    mapCE          :: (CoreExpr -> CoreExpr) -> e -> e  -- これも変．
    aeAppErr       :: String -> e -> e -> e
    appEnv         :: Int8 -> e -> e -> e
    toAnnExpr      :: (CoreExpr->Dynamic) -> e -> AnnExpr
    toAnnExprWind  :: (CoreExpr->Dynamic) -> Type -> e -> AnnExpr
    toAnnExprWindWind :: (CoreExpr->Dynamic) -> Type -> e -> AnnExpr
    fromAnnExpr    :: AnnExpr -> e
    reorganize     :: Monad m => ([Type] -> m [e]) -> [Type] -> m [e] -- with uniq
    reorganize'    :: Monad m => ([Type] -> m [e]) -> [Type] -> m [e] -- without uniq
    reorganizeId   ::  ([Type] -> [e]) -> [Type] -> [e] -- reorganize for Id monad
    replaceVars' :: Int8 -> e -> [Int8] -> e -- @replaceVars@ without uniq
    reorganizeId' :: (Functor m) => ([Type] -> m e) -> [Type] -> m e
    reorganizeId' fun avail = case cvtAvails' avail of
                                (args, newavail) ->
                                  fmap (\e -> replaceVars' 0 e args) $ fun newavail
    decodeVars :: Int -> [Int8] -> e -> e

instance Expression CoreExpr where
    mkHead _ _ _ _        = id
    toCE                  = id
    fromCE _              = id
    mapCE                 = id
    aeAppErr _msg         = (:$)
    appEnv _              = (:$)
    toAnnExpr reduce e           = AE e (reduce e)
    toAnnExprWind reduce ty e    = AE e (reduce $ windType ty e)
    toAnnExprWindWind reduce ty e = let we = windType ty e in AE we (reduce we)
    fromAnnExpr (AE ce _) = ce
    reorganize = reorganizer
    reorganize' = reorganizeCE'
    reorganizeId = reorganizerId
    replaceVars' = replaceVarsCE'
    decodeVars = const decodeVarsCE
instance Expression AnnExpr where
    mkHead reduce lenavails numcxts arity ce = mkHeadAE reduce (fromIntegral lenavails) (fromIntegral numcxts) (fromIntegral arity) ce
    toCE ae@(AE ce _)                  = ce
    fromCE                          = toAnnExpr
    mapCE f (AE ce d)               = AE (f ce) d
#ifdef REALDYNAMIC
    aeAppErr msg (AE e1 h1) (AE e2 h2) = AE (e1:$e2) (dynAppErr (" while applying "++show e1 ++" to "++show e2 ++ '\n':msg) h1 h2)
#else
    aeAppErr _msg (AE e1 h1) (AE e2 h2) = AE (e1:$e2) (dynApp h1 h2)
#endif
    appEnv lenavails (AE e1 h1) (AE e2 h2) = AE (e1:$e2) (dynApp (dynApp (dynSn lenavails) h1) h2)
    toAnnExpr     _                 = id
    toAnnExprWind _ _               = id
    toAnnExprWindWind _ ty (AE ce d) = AE (windType ty ce) d
    fromAnnExpr                     = id
    reorganize = id
    reorganize' = id
    reorganizeId = id
    reorganizeId' = id -- Well, this is overridden to id because replaceVars' for AnnExpr is not yet implemented.
                    -- てな訳で．実装すべし！！！！！！！！！！！！！！！！！！！！！！！！！
    decodeVars = decodeVarsAE

mapFst3 f (ces, s, i) = (f ces, s, i)
decodeVarsPos vs = mapFst3 (map (decodeVarsCE vs))

decodeVarsCE :: [Int8] -> CoreExpr -> CoreExpr
decodeVarsCE vs = decodeVarsCE' 0 (listArray (0, genericLength vs-1) vs)
decodeVarsCE' :: Int8 -> Array Int8 Int8 -> CoreExpr -> CoreExpr
decodeVarsCE' offset ar e@(X n) = let nn = n - offset
                                  in if inRange (bounds ar) nn then X $ (ar ! nn) + offset else e
decodeVarsCE' offset ar (Lambda e) = Lambda $ decodeVarsCE' (offset + 1) ar e
decodeVarsCE' offset ar (f :$ e)   = decodeVarsCE' offset ar f :$ decodeVarsCE' offset ar e
decodeVarsCE' offset ar e          = e

decodeVarsAE :: Int -> [Int8] -> AnnExpr -> AnnExpr
decodeVarsAE lenav vs (AE ce dyn) = AE (decodeVarsCE vs ce) (decodeVarsDyn lenav vs dyn)

decodeVarsDyn :: Int -> [Int8] -> Dynamic -> Dynamic
decodeVarsDyn lenav vs dyn = insAbsents (fromIntegral lenav) (map (fromIntegral lenav-1-) $ reverse vs) `dynApp` dyn

insAbsents :: Int8 -> [Int8] -> Dynamic
insAbsents lenav ns = -- trace ("insAbsents "++show lenav ++ ' ':show ns) 
                      ia 0 ns where
  ia i []     | i ==lenav = dynI
  ia i (n:ns) | i == n    = dynB  `dynApp` ia (succ i) ns 
  ia i ms                 = dynBK `dynApp` ia (succ i) ms



(<$>) :: Expression e => e -> e -> e
(<$>) = aeAppErr ""

mkHeadAE _      lenavails _       arity ce@(X i) = AE ce (getDyn_LambdaBoundHead i lenavails arity)    -- Note that 'dynss' and 'dynsss' uses
mkHeadAE reduce lenavails numcxts arity ce       = AE ce ((iterate (dynB `dynApp`) (getDyn lenavails arity) !! numcxts) `dynApp` reduce ce) -- 'unsafeExecute' instead of 'reduce'.

windType :: Type -> CoreExpr -> CoreExpr
windType (a:->b) e = Lambda (windType b e)
windType _       e = e

-- Sn = \f g x1 .. xn -> f x1 .. xn (g x1 .. xn)
dynSn lenavails = dynApp (getDyn lenavails 2) dynI

getDyn, mkDyn :: Int8 -> Int8 -> Dynamic
getDyn lenavails arity
--    | arity<=maxArity = case lenavails `divMod` maxLenavails of (d,m) -> napply d (dynApp (dynApp dynB (finiteDynar!(maxLenavails,arity)))) (finiteDynar!(m,arity)) -- なんか違うみたい．
    | lenavails<=maxLenavails && arity<=maxArity = -- trace (show (lenavails,arity)++show (maxLenavails,maxArity)) $
                                                   finiteDynar ! (lenavails,arity)
    | otherwise                                  = dynss `genericIndex` lenavails `genericIndex` arity

dynss :: [[Dynamic]]
dynss = [ [ mkDyn i j | j <- [0..] ] | i <- [0..] ]
mkDyn 0         _ = dynI
{-
mkDyn lenavails 0 = unsafeExecute (B :$ K) `dynApp` mkDyn (lenavails-1) 0 
mkDyn lenavails arity = unsafeExecute $ mkCE lenavails arity 
-}
-- mkDyn lenavails arity = napply lenavails (dynApp (dynB `dynApp` x arity)) dynI
mkDyn lenavails arity = dynApp (dynB `dynApp` x arity) (getDyn (lenavails-1) arity)

-- #ifdef TEMPLATE_HASKELL
-- x n | n<=maxArity = finiteDynar ! (1,n) -- なんか違うみたい．
-- #else
x 0 = dynK
x 1 = dynB
x 2 = dynS'
-- x 3 = unsafeToDyn (readType "(a->b->c->r)->(x->a)->(x->b)->(x->c)->x->r")    x3      ()
-- #endif
x n = napply n (dynApp dynB) dynS `dynApp` x (n-1)

finiteDynar  = array ((0,0),(maxLenavails,maxArity)) [ ((lenavails,arity), finiteDynss `genericIndex` lenavails `genericIndex` arity) | arity<-[0..maxArity], lenavails<-[0..maxLenavails] ]
finiteDynarr = array ((0,0,0),(maxDebindex,maxLenavails,maxArity)) [ ((debindex,lenavails,arity), finiteDynsss `genericIndex` debindex `genericIndex` (lenavails-debindex-1) `genericIndex` arity) | arity<-[0..maxArity], debindex<-[0..maxDebindex], lenavails<-[debindex+1..maxLenavails] ]

finiteDynss = zipWith3 (zipWith3 (unsafeToDyn defaultTCL)) [ [ hdmnty  arity lenavails | arity <- [0..maxArity] ] | lenavails <- [0..maxLenavails] ]
                                              finiteHVss
                                              [ [ hdmnTHE arity lenavails | arity <- [0..maxArity] ] | lenavails <- [0..maxLenavails] ]
finiteDynsss = zipWith3 (zipWith3 (zipWith3 (unsafeToDyn defaultTCL)))
                        [ [ [ aimnty  debindex arity lenavails | arity <- [0..maxArity] ] | lenavails <- [debindex+1..maxLenavails] ] | debindex <- [0..maxDebindex] ]
                        finiteHVsss
                        [ [ [ aimnTHE debindex arity lenavails | arity <- [0..maxArity] ] | lenavails <- [debindex+1..maxLenavails] ] | debindex <- [0..maxDebindex] ]

getDyn_LambdaBoundHead, mkDyn_LambdaBoundHead :: Int8 -> Int8 -> Int8 -> Dynamic
getDyn_LambdaBoundHead debindex lenavails arity
    | debindex<=maxDebindex && lenavails<=maxLenavails && arity<=maxArity = -- trace (show (debindex,lenavails,arity)++show (maxDebindex,maxLenavails,maxArity)) $
                                                                            finiteDynarr ! (debindex,lenavails,arity) -- こっちの方が効率的なんだけど，デバッグ中だけ一時的に．
                                                                            -- finiteDynsss !! debindex !! (lenavails-debindex-1) !! arity
    | otherwise                                  = dynsss `genericIndex` debindex `genericIndex` lenavails `genericIndex` arity

dynsss :: [[[Dynamic]]]
dynsss = [ [ [ mkDyn_LambdaBoundHead i j k | k <- [0..] ] | j <- [0..] ] | i <- [0..] ]

mkDyn_LambdaBoundHead debindex lenavails arity = (getDyn lenavails (arity+1) `dynApp` dynI) `dynApp` select lenavails debindex
    where
      -- select lenavails debindex = unsafeExecute (napply lenavails Lambda $ X debindex)
      select lenavails debindex = napply (lenavails-1-debindex) (dynApp dynK) $ napply debindex (dynApp dynBK) dynI
dynBK = dynApp dynB dynK

-- dynF = dynApp dynC dynK

-- moved from ProgramGenerator.lhs

-- reorganize :: ([Type] -> PriorSubsts BF [CoreExpr]) -> [Type] -> PriorSubsts BF [CoreExpr]
-- として使われるのだが，特にexportされる訳でもないのでいちいちspecializeしない．
reorganizer :: Monad m => ([Type] -> m [CoreExpr]) -> [Type] -> m [CoreExpr]
reorganizer fun avail
    = case cvtAvails avail of
       (newavail, argss) ->
         do agentExprs <- fun newavail
            return [ result | e <- agentExprs, result <- replaceVars 0 e argss ]

reorganizerId :: ([Type] -> [CoreExpr]) -> [Type] -> [CoreExpr]
reorganizerId fun avail
    = case cvtAvails avail of
       (newavail, argss) ->
           [ result | e <- fun newavail, result <- replaceVars 0 e argss ]
replaceVars :: Int8 -> CoreExpr -> [[Int8]] -> [CoreExpr]
replaceVars dep e@(X n)    argss = case argss !? (n - dep) of Nothing -> [e]
                                                              Just xs -> map (\ m -> X (m + dep)) xs
replaceVars dep (Lambda e) argss = map Lambda (replaceVars (dep+1) e argss)
replaceVars dep (f :$ e)   argss = liftM2 (:$) (replaceVars dep f argss) (replaceVars dep e argss)
replaceVars dep e          argss = [e]

cvtAvails = unzip . tkr10 . annotate

tkr10 :: [(Type,a)] -> [(Type,[a])]
tkr10 = mergesortWithBy (\ (k,is) (_,js) -> (k,is++js)) (\ (k,_) (l,_) -> k `compare` l) . map (\(k,i)->(k,[i]))


-- annotateはsplitAvailsの前処理としても使える．
annotate :: [Type] -> [(Type,Int8)]
annotate ts = zipWith (,) ts [0..]
{-
annotate ts = an 0 ts
    where an n []     = []
          an n (t:ts) = (t,n) : an (n+1) ts
prop_annotate = \ts -> annotate ts == zipWith (,) ts [0..]
-}




-- @reorganize@ without uniq
reorganizeCE' :: Monad m => ([Type] -> m [CoreExpr]) -> [Type] -> m [CoreExpr]
reorganizeCE' fun avail
    = case cvtAvails' avail of
       (args, newavail) ->
         do agentExprs <- fun newavail
            return [ replaceVars' 0 e args | e <- agentExprs ]

replaceVarsCE' :: Int8 -> CoreExpr -> [Int8] -> CoreExpr
replaceVarsCE' dep e@(X n)    args = case args !? (n - dep) of Nothing -> e
                                                               Just m  -> X (m + dep)
replaceVarsCE' dep (Lambda e) args = Lambda (replaceVarsCE' (dep+1) e args)
replaceVarsCE' dep (f :$ e)   args = replaceVarsCE' dep f args :$ replaceVarsCE' dep e args
replaceVarsCE' dep e          args = e

cvtAvails' = unzip . sortBy (\(_,k) (_,l) -> compare k l) . zip [0..]





-- Moved from T10
-- uniqSorter :: (Ord e) => [(e,Int)] -> [(e,Int)]
uniqSorter, uniqSortPatAVL :: (Expression e) => [(e,Int)] -> [(e,Int)]
uniqSorter = swapUniqSort -- uniqSortPatAVL -- swapUniqSort -- id -- uniqSort

uniqSort, uniqSortAVL :: Ord a => [a] -> [a]
uniqSort = mergesortWithBy const compare
swapUniqSort :: (Ord a, Ord b) => [(a,b)] -> [(a,b)]
swapUniqSort = mergesortWithBy const (\(a,b) (c,d) -> compare (b,a) (d,c))

uniqSortAVL = S.toList . S.fromList

--  まずは後ろのIntで分けるので，IntMapとの2段構え
-- causes `Stack space overflow' error when used by SimpleServer
uniqSortPatAVL ts = [ (x,j) | (j, set) <- IM.toList $ IM.fromListWith S.union $ map (\(x,i) -> (i, S.singleton x)) ts
                            , x <- S.toList set ]

{- The hashing uniqsorters are really problematic. See newnotes on 2012/11/04
annUniqSort :: Expression e => [(e,Int)] -> [(e,Int)]
annUniqSort = map snd  .  mergesortWithBy const (\a b -> compare (fst a) (fst b))  .  map (\t@(ce,_i) -> (fromEnum $ toCE ce, t))
aUS :: Expression e => [e] -> [e]
aUS = map snd  .  mergesortWithBy const (\a b -> compare (fst a) (fst b))  .  map (\e -> (fromEnum $ toCE e, e))
annUniqSortAVL :: (Expression e) => [(e,Int)] -> [(e,Int)]
annUniqSortAVL = IM.elems . IM.fromList . map (\t@(ce,_i) -> (fromEnum $ toCE ce, t))
-- fromEnum何度もやり直すのも馬鹿馬鹿しい気も．
-}
