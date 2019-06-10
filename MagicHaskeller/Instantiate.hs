-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE TemplateHaskell, RankNTypes, CPP, PatternGuards, ImpredicativeTypes #-}
module MagicHaskeller.Instantiate(mkRandTrie, RTrie, -- arbitraries,
                   uncurryDyn, uncurryTy, mkUncurry, typeToOrd, typeToRandomsOrd, typeToRandomsOrdDM, mkCurry, curryDyn, argTypeToRandoms
                  , typeToArb -- exported just for testing Classification.tex
                    , PackedOrd, typeToCompare, compareRealFloat
                  ) where

import MagicHaskeller.CoreLang
import qualified Data.Map as Map
import MagicHaskeller.MyCheck
#ifdef TFRANDOM
import System.Random.TF.Gen
#else
import System.Random
#endif
import MagicHaskeller.Types
import Control.Monad.Search.Combinatorial
import Data.Array((!))
import MagicHaskeller.TyConLib
import MagicHaskeller.DebMT
import Data.List hiding (insert)
import Control.Monad
import qualified Data.IntMap as IntMap

-- import Data.Ratio
import MagicHaskeller.FastRatio

import MagicHaskeller.MyDynamic hiding (dynApp)
-- import Data.Typeable

import MagicHaskeller.ReadDynamic(dynI)

import Data.Memo

import MagicHaskeller.T10
-- import ReadTypeRep(typeToTR)

import Language.Haskell.TH hiding (Type)

import MagicHaskeller.NearEq(NearEq(..))

-- import Debug.Trace
trace _ e = e

dynApp = dynAppErr "in MagicHaskeller.Instantiate"

type Order = Maybe ([Dynamic], PackedOrd)

type ExpResult = ([Dynamic],CoreExpr)
mkUncurry :: TyConLib -> Dynamic
mkUncurry tcl =
                $(dynamic [|tcl|] [| uncurry :: (a->b->c)->((,) a b)->c |])

uncurryDyn :: Dynamic -> Type -> Dynamic -> Dynamic
uncurryDyn unc (_ :-> b@(_:->_)) f = dynAppErr "while uncurrying." unc (uncurryDyn unc b f)
uncurryDyn _   _                 x = x

mkCurry :: TyConLib -> Dynamic
mkCurry tcl =
                $(dynamic [|tcl|] [| curry :: ((,) a b -> c)-> a->b->c |])

curryDyn :: Dynamic -> Type -> Dynamic -> Dynamic
curryDyn cur (_ :-> b@(_:->_)) f = dynAppErr "while currying." cur (curryDyn cur b f)
curryDyn _   _                 x = x

{-
varsInts (TA t u) = TA (varsInts t) (varsInts u)
varsInts (u:->t)  = varsInts u :-> varsInts t
varsInts (TV 
-}
uniqueVars (TA t u) = TA (uniqueVars t) (uniqueVars u)
uniqueVars (u:->t)  = uniqueVars u :-> uniqueVars t
uniqueVars (TV _)   = TV 0
uniqueVars tc       = tc

-- uniqueVars はmemoizeしない場合はやってもしょうがないし，memoizeする場合はsynergeticとそうでないのと両方でやるべきでは?


-- memoizeしない場合
typeToRandomsOrd :: TyConLib -> RTrie -> Type -> Order
typeToRandomsOrd tcl = ttro (\(cmap,maps,_,_,_) -> argTypeToRandoms tcl cmap maps) tcl
typeToRandomsOrdDM :: [Int] -> TyConLib -> RTrie -> Type -> Maybe ([[Dynamic]], PackedOrd)
typeToRandomsOrdDM nrnds tcl = ttro (\(cmap,maps,_,_,_) -> argTypeToRandomss nrnds tcl cmap maps) tcl

{-
-- memoizeする場合
typeToRandomsOrd :: TyConLib -> RTrie -> Type -> Order
typeToRandomsOrd tcl rtrie = ttro (\(_,_,(mtrands,_)) -> lookupMT mtrands) tcl rtrie . uniqueVars
typeToRandomsOrdDM :: TyConLib -> RTrie -> Type -> Maybe ([[Dynamic]], PackedOrd)
typeToRandomsOrdDM tcl rtrie = ttro (\(_,_,(_,mtrands)) -> lookupMT mtrands) tcl rtrie . uniqueVars
-}

ttro :: (RTrie -> Type -> Maybe [a]) -> TyConLib -> RTrie -> Type -> Maybe ([a], PackedOrd)
ttro attr tcl rtrie@(cmap,_,_,_,_) (a1:->rest)
    = let (a,r) = uncurryTy' tcl a1 rest
      in do cmp  <- typeToCompare tcl cmap r
            rnds <- attr rtrie a
            return (rnds, cmp)
ttro attr tcl (cmap, _, _, _, _) t
    = do cmp <- typeToCompare tcl cmap t
         return ([], cmp)



dynToCompare :: TyConLib -> Dynamic -> (Dynamic -> Dynamic -> Ordering)
dynToCompare tcl dyn d0 d1 = fromDyn tcl (dynAppErr "in dynToCompare (1)" (dynAppErr "in dynToCompare (2)" dyn d0) d1) (error "dynToCompare: type mismatch")
--dynToCompare tcl dyn d0 d1 = aLittleSafeFromDyn (readType' tcl "Ordering") (dynApp (dynApp dyn d0) d1)

-- 引数の型が確定しても返り値の型が確定しない場合：たとえばundefinedやerrorとか．このへんをちゃんとtake careしとかないと，むりやりIntに変換することになる．...まあいっか？
-- procUndef = Just ([], mkHV (\_ _ -> True))

-- | 'uncurryTy' converts  @a->b->c->d->e->r@ into @((((a,b),c),d),e)->r@
--   Note that @Arbitrary (a,b,c,d,e)@ is not defined in @Test.QuickCheck@.
uncurryTy :: TyConLib -> Type -> Type
uncurryTy tcl (a:->b) = case uncurryTy' tcl a b of (c,r) -> c:->r
uncurryTy _   t       = t
uncurryTy' :: TyConLib -> Type -> Type -> (Type,Type)
uncurryTy' tcl a (b:->r) = uncurryTy' tcl (pair tcl a b) r
uncurryTy' tcl a r       = (a,r)

pair tcl a b = (TA (TA (TC (tuple tcl 2)) a) b)
{-
tupleに対応するやつないし，やっぱTH.Typeに一旦変換した方がよい？ あるいは，Types.TypeでTupleを特別視するか．まあ，律速段階ではないので"(,)"みたいな感じでやってもいいけど．
ただ，tclに"(,)"とかが含まれない場合は？ 単にdefaultTyConsに入れておけばいいか．ただ，Arbitraryは(,,,)までしか定義されていない．

$(support [t| forall a b c. ((Int,Integer,Char), ([a], Maybe a), (Either a b, (a,b))) |])
みたいに書くとtypeToOrdやtypeToRandomsが生成されてくれると便利．
まあとりあえずは限られた型だけでやってもいいけど．

てゆーか，Ordな型とArbitraryな型は別なので，supportOrd, supportArbの２つを用意しておくか．


てゆーか，Dynamicはどうよ？ 同じことか
-}

type PackedOrd = Dynamic -> Dynamic -> Ordering
type Cmp a = a->a->Ordering

#ifdef TFRANDOM
type Generator = TFGen
#else
type Generator = StdGen
#endif
type Maps  = (ArbMap, CoarbMap, Generator, Generator) -- used if we do not memoize
type Tries = (MapType (Maybe [Dynamic]), MapType (Maybe [[Dynamic]])) -- used if we memoize

type RTrie = (CmpMap, Maps, MemoMap,
              Tries,  MapType (Dynamic,Dynamic))

mkRandTrie :: [Int] -> TyConLib -> Generator -> RTrie
mkRandTrie nrnds tcl gen
                   = let arbtup   = mkArbMap tcl
                         coarbtup = mkCoarbMap tcl
                         (g0,g1)  = split gen
                         maps     = (arbtup, coarbtup, g0, g1)
                         cmap     = mkCmpMap tcl
                         mmap     = mkMemoMap tcl
                     in (cmap, maps, mmap,
                            (mkMT tcl (argTypeToRandoms tcl cmap maps), mkMT tcl (argTypeToRandomss nrnds tcl cmap maps)),
                            (mkMT tcl (typeToMemo mmap)))
argTypeToRandoms :: TyConLib -> CmpMap -> Maps -> Type -> Maybe [Dynamic]
argTypeToRandoms  tcl cmap (arbtup, coarbtup, gen, _) a
    = do arb  <- typeToArb arbtup coarbtup a
         return $ arbitrariesByDyn tcl arb gen
argTypeToRandomss :: [Int] -> TyConLib -> CmpMap -> Maps -> Type -> Maybe [[Dynamic]]
argTypeToRandomss nrnds tcl cmap (arbtup, coarbtup, _, gen) a
    = do arb  <- typeToArb arbtup coarbtup a
         let arbssDyn = arbitrariessByDyn nrnds tcl arb gen
         case typeToCompare tcl cmap a of Nothing  -> return arbssDyn
                                          Just cmp -> return $ map (nubByCmp cmp . take 20) arbssDyn
nubByCmp cmp = nubBy (\a b -> cmp a b == EQ)
-- nubByCmpは同じ乱数が入らないようにする働きがある．ただし，Boolなどのように本質的に2種類しかないものに対してnubByCmpして乱数を5つ取ろうとすると無限ループに入ってしまうので，それを避けるためにtake 20を入れている．
-- argTypeToRandomsでもそれをしようとすると結構ややこしいことになるので，そっちではnubByCmpしないことにする．2012/5/29のnewnotes参照．
-- てゆーか，argTypeToRandomssだけで全部やればいいんだけど．

type MapTC a = IntMap.IntMap (IntMap.IntMap a)
type CmpMap = (MapTC Dynamic, SpecialMap, Dynamic)


mkMap :: TyConLib -> [[(String,a)]] -> MapTC a
mkMap tcl@(mapNameTyCon,_) mcts = IntMap.fromAscList $ zip [0..] $ map (IntMap.fromList . map (\ (name, dyn) -> (fromIntegral (mapNameTyCon Map.! name),  dyn))) mcts
mkCmpMap :: TyConLib -> CmpMap
mkCmpMap tcl = (mkMap tcl [mct0, mct1, mct2],
                mkSpecialMap tcl [("Ratio", "Int",     $(dynamic [|tcl|] [| compareRatio :: Ratio Int -> Ratio Int -> Ordering |])),
                                  ("Ratio", "Integer", $(dynamic [|tcl|] [| compareRatio :: Ratio Integer -> Ratio Integer -> Ordering |]))],
                cmpChar)
    where
          cmpChar = $(dynamic [|tcl|] [| compare :: Char -> Char -> Ordering |])
          mct0, mct1, mct2 :: [(String,Dynamic)]
          mct0 = [("Int",     $(dynamic [|tcl|] [| compare      :: Int     -> Int     -> Ordering |])),
                  ("Integer", $(dynamic [|tcl|] [| compare      :: Integer -> Integer -> Ordering |])),
                  ("Char",    cmpChar),
                  ("Bool",    $(dynamic [|tcl|] [| compare      :: Bool    -> Bool    -> Ordering |])),
                  ("Double",  $(dynamic [|tcl|] [| compareRealFloat :: Double  -> Double  -> Ordering |])),
                  ("Float",   $(dynamic [|tcl|] [| compareRealFloat :: Float   -> Float   -> Ordering |])),
                  ("()",      $(dynamic [|tcl|] [| compare      :: ()      -> ()      -> Ordering |])),
                  ("Ordering",$(dynamic [|tcl|] [| compare      :: Ordering-> Ordering-> Ordering |]))]
          mct1 = [("Maybe",   $(dynamic [|tcl|] [| compareMaybe :: (a -> a -> Ordering) -> Maybe a -> Maybe a -> Ordering |])),
                  ("[]",      $(dynamic [|tcl|] [| compareList  :: (a -> a -> Ordering) -> [a]     -> [a]     -> Ordering |]))]
          mct2 = [("Either",  $(dynamic [|tcl|] [| compareEither:: (a -> a -> Ordering) ->
                                                                   (b -> b -> Ordering) -> Either a b -> Either a b -> Ordering |])),
                  ("(,)",     $(dynamic [|tcl|] [| comparePair  :: (a -> a -> Ordering) ->
                                                                   (b -> b -> Ordering) -> (a,b)      -> (a,b)      -> Ordering |]))]
--                  ("Array", unsafeToDyn (readType' tcl "Cmp a -> Cmp b -> Cmp (Array a b)") (\cmp0 cmp1 x y -> compareList (comparePair cmp0 cmp1) (assocs x) (assocs y)))]
--          tto (TA (TA (TA (TC tc) t) u) v) = case (ar ! 3) !! tc of ("(,,)",_) -> packCmp (\ (x0,x1,x2) (y0,y1,y2) -> compareTup  (pair tcl (pair tcl t u) v) ((x0,x1),x2) ((y0,y1),y2))
--                                                                    _          -> Nothing
compareMaybe _   Nothing  Nothing  = EQ
compareMaybe _   Nothing  _        = LT
compareMaybe _   _        Nothing  = GT
compareMaybe cmp (Just x) (Just y) = cmp x y
compareRatio :: Integral i => Ratio i -> Ratio i -> Ordering
compareRatio x y = case (denominator x, denominator y) of (0,0) -> EQ -- Because the comparison is just for removing duplicates efficiently,
                                                          (0,_) -> LT -- notANumber should be a normal element here.
                                                          (_,0) -> GT
                                                          _     -> compare (numerator x * denominator y) (numerator y * denominator x)
compareRealFloat  :: (NearEq a, RealFloat a) => a->a->Ordering
compareRealFloat x y = case (isNaN x, isNaN y) of -- Because the comparison is just for removing duplicates efficiently,
                             (True, True)  -> EQ  -- NaN should be a normal element here.
                             (True, False) -> LT
                             (False,True)  -> GT
                             (False,False) -> if x~=y then EQ else compare x y


compareList _   []     []     = EQ
compareList _   []     _      = LT
compareList _   _      []     = GT
compareList cmp (x:xs) (y:ys) = case cmp x y of EQ -> compareList cmp xs ys
                                                c  -> c
compareEither cmp0 cmp1 (Left x)  (Left y)  = cmp0 x y
compareEither cmp0 cmp1 (Left _)  _         = LT
compareEither cmp0 cmp1 _         (Left _)  = GT
compareEither cmp0 cmp1 (Right x) (Right y) = cmp1 x y
comparePair   cmp0 cmp1 (x0,x1)  (y0,y1) = case cmp0 x0 y0 of EQ -> cmp1 x1 y1
                                                              c  -> c

typeToCompare :: TyConLib -> CmpMap -> Type -> Maybe (Dynamic -> Dynamic -> Ordering)
typeToCompare tcl cmap ty = do cmp <- typeToOrd cmap ty
                               return (dynToCompare tcl cmp)
typeToOrd :: CmpMap -> Type -> Maybe Dynamic
typeToOrd (cmpmap,spmap,cmpchar) ty = tto 0 ty
    where tto 0 (TA (TC tc1) (TC tc2)) | Just dyn <- IntMap.lookup (combineTCs tc1 tc2) spmap = return dyn
          tto k (TA t u) = liftM2 dynApp (tto (k+1) t) (tto 0 u) -- Higher-order kinds break everything.
          tto _ (_:->_)  = Nothing -- error "Functions in containers are not allowed." -- note that ty is (part of) the return type, so this means higher-order datatype is returned.
          tto 0 (TV _)   = Just cmpchar -- same as the Char case
          tto _ (TV _)   = Nothing -- これについては一般的なやりかたはなさそう．
          tto k (TC tc)  = do guard (tc >= 0)
                              imap <- IntMap.lookup k cmpmap
                              IntMap.lookup (fromIntegral tc) imap
          tto _ _        = Nothing
type ArbMap   = (MapTC Dynamic, SpecialMap, Dynamic, Dynamic)
type CoarbMap = (MapTC Dynamic, SpecialMap, Dynamic, Dynamic)

mkArbMap :: TyConLib -> ArbMap
mkArbMap tcl@(mapNameTyCon,_) = (mkMap tcl [mct0, mct1, mct2, mct3],
                                 mkSpecialMap tcl [("Ratio", "Int",     $(dynamic [|tcl|] [| arbitraryRatio   :: Gen (Ratio Int) |])),
                                                   ("Ratio", "Integer", $(dynamic [|tcl|] [| arbitraryRatio   :: Gen (Ratio Integer) |]))],
                                arbChar, -- same as the Char case
                                $(dynamic [|tcl|] [| arbitraryFun :: (a -> Gen b -> Gen b) -> Gen b -> Gen (a->b) |])
                                )

    where
          arbChar = $(dynamic [|tcl|] [| arbitraryChar :: Gen Char |])
          mct0, mct1, mct2, mct3 :: [(String,Dynamic)]
          mct0 = [("Int",     $(dynamic [|tcl|] [| arbitraryInt     :: Gen Int |])),
                  ("Char",    arbChar),
                  ("Integer", $(dynamic [|tcl|] [| arbitraryInteger :: Gen Integer |])),
                  ("Bool",    $(dynamic [|tcl|] [| arbitraryBool    :: Gen Bool    |])),
                  ("Double",  $(dynamic [|tcl|] [| arbitraryDouble  :: Gen Double  |])),
                  ("Float",   $(dynamic [|tcl|] [| arbitraryFloat   :: Gen Float   |])),
                  ("()",      $(dynamic [|tcl|] [| arbitraryUnit    :: Gen ()      |])),
                  ("Ordering",$(dynamic [|tcl|] [| arbitraryOrdering:: Gen Ordering|]))]
          mct1 = [("Maybe",   $(dynamic [|tcl|] [| arbitraryMaybe   :: Gen a -> Gen (Maybe a) |])),
                  ("[]",      $(dynamic [|tcl|] [| arbitraryList    :: Gen a -> Gen [a]       |]))]
          mct2 = [("Either",  $(dynamic [|tcl|] [| arbitraryEither  :: Gen a -> Gen b -> Gen (Either a b) |])),
                  ("(,)",     $(dynamic [|tcl|] [| arbitraryPair    :: Gen a -> Gen b -> Gen (a, b)       |]))]
          mct3 = [("(,,)",    $(dynamic [|tcl|] [| arbitraryTriplet :: Gen a -> Gen b -> Gen c -> Gen (a,b,c) |]))]

-- ArbMap specialized for Ratio Int, etc. 
-- This is necessary because we cannot have something like arbitraryRatio :: Gen a -> Gen (Ratio a) (without type constraint),
-- in order to avoid zero-denominator cases.
type SpecialMap = IntMap.IntMap Dynamic
mkSpecialMap :: TyConLib -> [(String,String,Dynamic)] -> IntMap.IntMap Dynamic
mkSpecialMap tcl@(mapNameTyCon,_) = IntMap.fromList . map (\ (name1, name2, dyn) -> (combineTCs (mapNameTyCon Map.! name1) (mapNameTyCon Map.! name2),  dyn)) 

{- こっちにすべき ---------------------------------------
-- This signature silently makes sure that TyCon == Int8. This should cause an error when TyCon /= Int8.
combineTCs :: Int8 -> Int8 -> Int
combineTCs tc1 tc2 = fromIntegral tc1 * 256 + fromIntegral tc2
-}
-- debug目的でこっちにしている。---------------------------------
combineTCs :: TyCon -> TyCon -> Int
combineTCs tc1 tc2 = fromIntegral tc1 * 256 + fromIntegral tc2


typeToArb :: ArbMap -> CoarbMap -> Type -> Maybe Dynamic
typeToArb arbtup@(arbmap, spmap, arbchar, arbfun) coarbtup@(coarbmap, _, coarbchar, coarbfun) ty = tta 0 ty
    where
          tta 0 ty@(t :-> u) = do coarb <- typeToCoarb arbtup coarbtup t
                                  arb   <- tta 0 u
                                  return (-- trace ("t = "++show t++" and u = "++show u ++ " and coarb = "++show coarb) $
                                          dynApp (dynApp arbfun coarb) arb)
          tta 0 (TV _)  = Just arbchar -- same as the Char case
          tta _ (TV _)  = Nothing -- これについては一般的なやりかたはなさそう．
          tta k (TC tc)
              = do guard (tc >= 0)
                   imap <- IntMap.lookup k arbmap
                   IntMap.lookup (fromIntegral tc) imap
          tta 0 (TA (TC tc1) (TC tc2)) | Just dyn <- IntMap.lookup (combineTCs tc1 tc2) spmap = return dyn
          tta k (TA t0 t1) = do arb0 <- tta (k+1) t0
                                arb1 <- tta 0     t1
                                return (-- trace ("t0 = "++show t0++" and t1 = "++show t1) $
                                        dynApp arb0 arb1)
          tta _ _ = Nothing
mkCoarbMap :: TyConLib -> CoarbMap
mkCoarbMap tcl@(mapNameTyCon,_) = (mkMap tcl [mct0, mct1, mct2, mct3],
                                   mkSpecialMap tcl [("Ratio", "Int",     $(dynamic [|tcl|] [| coarbitraryRatio   :: Ratio Int -> Gen x -> Gen x |])),
                                                     ("Ratio", "Integer", $(dynamic [|tcl|] [| coarbitraryRatio   :: Ratio Integer -> Gen x -> Gen x |]))],
                                   coarbChar, -- same as the Char case
                                   $(dynamic [|tcl|] [| coarbitraryFun :: Gen a -> (b -> Gen x -> Gen x) -> (a->b) -> Gen x -> Gen x |])
                                  )
    where coarbChar = $(dynamic [|tcl|] [| coarbitraryChar :: Char -> Gen x -> Gen x |])
          mct0, mct1, mct2, mct3 :: [(String,Dynamic)]
          mct0 = [("Int",      $(dynamic [|tcl|] [| coarbitraryInt     :: Int     -> Gen x -> Gen x |])),
                  ("Char",     coarbChar),
                  ("Integer",  $(dynamic [|tcl|] [| coarbitraryInteger  :: Integer  -> Gen x -> Gen x |])),
                  ("Bool",     $(dynamic [|tcl|] [| coarbitraryBool     :: Bool     -> Gen x -> Gen x |])),
                  ("Double",   $(dynamic [|tcl|] [| coarbitraryDouble   :: Double   -> Gen x -> Gen x |])),
                  ("Float",    $(dynamic [|tcl|] [| coarbitraryFloat    :: Float    -> Gen x -> Gen x |])),
                  ("()",       $(dynamic [|tcl|] [| coarbitraryUnit     :: ()       -> Gen x -> Gen x |])),
                  ("Ordering", $(dynamic [|tcl|] [| coarbitraryOrdering :: Ordering -> Gen x -> Gen x |]))]
          mct1 = [("[]",     $(dynamic [|tcl|] [| coarbitraryList   :: (a -> Gen x -> Gen x) -> [a]     -> Gen x -> Gen x |])),
                  ("Maybe",  $(dynamic [|tcl|] [| coarbitraryMaybe  :: (a -> Gen x -> Gen x) -> Maybe a -> Gen x -> Gen x |]))]
          mct2 = [("Either", $(dynamic [|tcl|] [| coarbitraryEither :: (a -> Gen x -> Gen x) ->
                                                                       (b -> Gen x -> Gen x) -> Either a b -> Gen x -> Gen x |])),
                  ("(,)",    $(dynamic [|tcl|] [| coarbitraryPair   :: (a -> Gen x -> Gen x) ->
                                                                       (b -> Gen x -> Gen x) -> (a, b) -> Gen x -> Gen x |]))]
          mct3 = [("(,,)",   $(dynamic [|tcl|] [| coarbitraryTriplet:: (a -> Gen x -> Gen x) ->
                                                                       (b -> Gen x -> Gen x) ->
                                                                       (c -> Gen x -> Gen x) -> (a,b,c) -> Gen x -> Gen x |]))]
typeToCoarb :: ArbMap -> CoarbMap -> Type -> Maybe Dynamic
typeToCoarb arbtup@(arbmap,_,arbchar,arbfun) coarbtup@(coarbmap,spmap,coarbchar,coarbfun) ty = ttc 0 ty
    where -- ttc :: Type -> Maybe (Coarb Dynamic)
          ttc 0 ty@(t :-> u) = do arb <- typeToArb arbtup coarbtup t
                                  coarb <- ttc 0 u
                                  return (dynApp (dynApp coarbfun arb) coarb)
          ttc 0 (TV _)  = Just coarbchar -- same as the Char case
          ttc _ (TV _)  = Nothing
          ttc k (TC tc)
              = do guard (tc >= 0)
                   imap <- IntMap.lookup k coarbmap
                   IntMap.lookup (fromIntegral tc) imap
          ttc 0 (TA (TC tc1) (TC tc2)) | Just dyn <- IntMap.lookup (combineTCs tc1 tc2) spmap = return dyn
          ttc k (TA t0 t1) = do arb0 <- ttc (k+1) t0
                                arb1 <- ttc 0     t1
                                return (-- trace ("arb0 = "++show arb0++"arb1 = "++show arb1) $
                                        dynApp arb0 arb1)
          ttc _ _ = Nothing -- めんどくさいので取り合えず．



type MemoMap = (IntMap.IntMap (IntMap.IntMap (Dynamic,Dynamic)), (Dynamic,Dynamic))
mkMemoMap :: TyConLib -> MemoMap
mkMemoMap tcl@(mapNameTyCon,_) = (mkMap tcl [mct0, mct1, mct2, mct3],
                                  memoAppChar)
    where memoAppChar = ( $(dynamic [|tcl|] [| memoChar :: (Char->a) -> MapChar a |]), 
                          $(dynamic [|tcl|] [| appChar  :: MapChar a -> (Char->a) |]) )
          mct0, mct1, mct2, mct3 :: [(String,(Dynamic,Dynamic))]
          mct0 = [("Int",     ($(dynamic  [|tcl|] [| memoIx3      :: (Int->a) -> MapIx Int a |]),
                               $(dynamic  [|tcl|] [| appIx       :: MapIx Int a -> (Int->a) |]))),
                  ("Char",    memoAppChar),
                  ("Integer", ($(dynamic  [|tcl|] [| memoInteger  :: (Integer->a) -> MapInteger a |]),
                               $(dynamic  [|tcl|] [| appInteger   :: MapInteger a -> (Integer->a) |]))),
                  ("Bool",    ($(dynamic  [|tcl|] [| memoBool     :: (Bool->a) -> MapBool a |]),
                               $(dynamic  [|tcl|] [| appBool      :: MapBool a -> (Bool->a) |]))),
                  ("Ordering",($(dynamic  [|tcl|] [| memoOrdering :: (Ordering->a) -> MapOrdering a |]),
                               $(dynamic  [|tcl|] [| appOrdering  :: MapOrdering a -> (Ordering->a) |]))),
                  ("()",      ($(dynamic  [|tcl|] [| memoUnit     :: (()->a) -> MapUnit a |]),
                               $(dynamic  [|tcl|] [| appUnit      :: MapUnit a -> (()->a) |]))),
                  ("Double",  ($(dynamic  [|tcl|] [| memoReal     :: (Double->a) -> MapReal a |]),
                               $(dynamic  [|tcl|] [| appReal      :: MapReal a -> (Double->a) |]))),
                  ("Float",   ($(dynamic  [|tcl|] [| memoReal     :: (Float->a) -> MapReal a |]),
                               $(dynamic  [|tcl|] [| appReal      :: MapReal a -> (Float->a) |])))]
          mct1 = [("[]",      ($(dynamicH [|tcl|] 'memoList      [t| forall m b a. (forall c. (b->c) -> m c) -> ([b] -> a) -> MapList m b a |]), -- use an undefined type, because forall is not supported. (But then does this work? I don't think so....) でも，単にforallを取ってinfinite typeを許せばOKって気もする．どうよ？
                               $(dynamicH [|tcl|] 'appList1     [t| forall m b a. (forall c. m c -> (b->c)) -> MapList m b a -> ([b]->a) |]))),
                  ("Maybe",   ($(dynamic  [|tcl|] [| memoMaybe    :: ((b->a)->m a) -> (Maybe b->a) -> MapMaybe m a |]),
                               $(dynamic  [|tcl|] [| appMaybe     :: (m a->(b->a)) -> MapMaybe m a -> (Maybe b -> a) |])))]
          mct2 = [("Either",  ($(dynamic  [|tcl|] [| memoEither   :: ((b->a) -> m a) ->
                                                                     ((d->a) -> n a) ->
                                                                        (Either b d -> a) -> MapEither m n a |]),
                               $(dynamic  [|tcl|] [| appEither    :: (m a -> (b->a)) ->
                                                                     (n a -> (d->a)) ->
                                                                        MapEither m n a -> (Either b d -> a) |]))),
                  ("(,)",     ($(dynamicH [|tcl|] 'memoPair      [t| forall m n b d a.
                                                                     (forall e. (b->e) -> m e) ->
                                                                     (forall f. (d->f) -> n f) ->
                                                                        ((b,d) -> a) -> MapPair m n a |]),
                               $(dynamicH [|tcl|] 'appPair       [t| forall m n b d a.
                                                                     (forall e. m e -> (b->e)) ->
                                                                     (forall f. n f -> (d->f)) ->
                                                                        MapPair m n a -> ((b,d) -> a) |])))]
          mct3 = [("(,,)",    ($(dynamicH [|tcl|] 'memoTriplet   [t| forall l m n b c d a.
                                                                     (forall f. (b->f) -> l f) ->
                                                                     (forall e. (c->e) -> m e) ->
                                                                     (forall e. (d->e) -> n e) ->
                                                                        ((b,c,d) -> a) -> MapTriplet l m n a |]),
                               $(dynamicH [|tcl|] 'appTriplet    [t| forall l m n b c d a.
                                                                     (forall e. l e -> (b->e)) ->
                                                                     (forall e. m e -> (c->e)) ->
                                                                     (forall e. n e -> (d->e)) ->
                                                                        MapTriplet l m n a -> ((b,c,d) -> a) |])))]
memoLength = 10
typeToMemo :: MemoMap -> Type -> (Dynamic,Dynamic)
typeToMemo memotup@(memomap,memochar) ty = case ttc 0 ty of Nothing -> (dynI,dynI) -- メモできない場合．テストするときは取り合えず全部(dynI,dynI)にしてもいいかも．
                                                            Just t  -> t
    where ttc 0 (t:->u) = Nothing
          ttc 0 (TV _)  = Just memochar
          ttc _ (TV _)  = Nothing
          ttc k (TC tc) | tc < 0    = Nothing
                        | otherwise = do imap <- IntMap.lookup k memomap
                                         IntMap.lookup (fromIntegral tc) imap
          ttc k (TA t0 t1) = do (m0,a0) <- ttc (k+1) t0
                                (m1,a1) <- ttc 0     t1
                                return (dynApp m0 m1, dynApp a0 a1)
          ttc _ _          = Nothing
-- Test.QuickCheck.GenはRandom.StdGen限定で，それ以外のRandomGen g => gではダメみたい．
-- Test.QuickCheck.generateの定義がちょっと変だと思う．usableだとは思うけど．

type Arb a = Generator -> [a]

arbitrariesByDyn :: TyConLib -> Dynamic -> Arb Dynamic
arbitrariesByDyn tcl arb = arbsByDyn tcl arb 0
arbsByDyn :: TyConLib -> Dynamic -> Int -> Generator -> [Dynamic]
arbsByDyn tcl arbDyn depth stdgen = zipWith (genAppDyn tcl arbDyn) [depth..] (gens stdgen)

genAppDyn :: TyConLib -> Dynamic -> Int -> Generator -> Dynamic
genAppDyn tcl arbDyn size stdgen = dynApp $(dynamic [|tcl|] [| (\(Gen f) -> f size stdgen) :: Gen a -> a |] ) arbDyn

{- 実際もう使われていないし．間違えてこっちを編集しちゃうので，隠す．
arbitrariesBy :: Gen a -> Arb a
arbitrariesBy arb = arbsBy arb 0
arbsBy :: Gen a -> Int -> StdGen -> [a]
arbsBy (Gen f) n stdgen = case split stdgen of (g0,g1) -> f n g0 : arbsBy arb (n+1) g1

arbitraries :: Arbitrary a => Arb a
arbitraries = arbitrariesBy arbitrary
-}



-- nrndsは実はsizeを決めるためにしか使われていない．得られるのはStream (Bag Dynamic)ではなくStream (Stream Dynamic)
arbitrariessByDyn :: [Int] -> TyConLib -> Dynamic -> Generator -> [[Dynamic]]
arbitrariessByDyn nrnds tcl arb gen = abd nrnds tcl arb 0 gen
-- abd _ _ arb depth gen = zipWith (arbsByDyn arb) [depth..] (gens gen) -- 乱数サイズを小さい値から増やしていく場合
abd nrnds tcl arb depth gen = zipWith (arbsByDyn' nrnds tcl arb) [depth..] (gens gen) -- 乱数サイズを一定にする場合
arbsByDyn' nrnds tcl arbDyn depth stdgen = map (genAppDyn tcl arbDyn size) (gens stdgen)
    where size = max depth (nrnds !! depth)
#ifdef TFRANDOM
gens gen = case map (splitn gen 8) [0..255] of g0:gs -> gs ++ gens g0
#else
gens gen = case split gen of (g0,g1) -> g0 : gens g1
#endif
