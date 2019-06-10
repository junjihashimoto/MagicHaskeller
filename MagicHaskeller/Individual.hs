-- 
-- (c) Susumu Katayama
--
{-# OPTIONS -XTemplateHaskell #-}
module MagicHaskeller.Individual(availableNames, prioritizedNamesToPg) where
import Language.Haskell.TH as TH
import qualified Data.Map as M
import qualified Data.IntMap as I
import Data.Char(isDigit)
import Data.List(findIndex, findIndices, mapAccumL, mapAccumR)
import Data.Generics
import MagicHaskeller.LibTH
import MagicHaskeller.Types(size)
import MagicHaskeller.ProgGenSF(mkTrieOptSFIO)
import Prelude hiding (tail)

-- | 'totals' is the set of available values (except partial functions) that can be included/excluded individually.
totals :: [Primitive]
totals = concat withDoubleRatio
-- You can add functions you like here, e.g. 
-- totals = concat withDoubleRatio ++ $(p [| nat_para :: (->) Int (a -> (Int -> a -> a) -> a) |] )

-- | 'partials' is the set of available partial functions that can be included/excluded individually.
partials :: [(Primitive,Primitive)]
partials = concat tupartialssNormal -- ++ ....

-- | 'aliases' is the set of aliases that can be used instead of the exact names appearing in 'totals' in order to increase readability of primitive library files. Also, aliases can be used to group a set of primitives and enable at once.
aliases :: [(String, [Primitive])]
aliases = [ ("total init", $(p [| reverse . drop 1 . reverse :: [a] -> [a] |])),
            ("total head", $(p [| foldr const :: a -> (->) [a] a |])),
            ("total last", $(p [| last' :: a -> [a] -> a |])),
            ("drop 1",     $(p [| tail :: (->) [a] [a] |] )),
            ("foldl",      $(p [| flip . flip foldl :: a -> (->) [b] ((a -> b -> a) -> a) |])),
            ("foldr",      $(p [| flip . flip foldr :: a -> (->) [b] ((b -> a -> a) -> a) |])),
            ("maybe",      $(p [| flip . maybe :: a -> (->) (Maybe b) ((b -> a) -> a) |])),
            ("map",        $(p [| flip map :: (->) ([a]) ((a -> b) -> [b]) |])),
            ("concatMap",  $(p [| flip concatMap :: (->) ([a]) ((a -> [b]) -> [b]) |])),
            ("any",        $(p [| flip any :: (->) ([a]) ((a -> Bool) -> Bool) |])),
            ("all",        $(p [| flip all :: (->) ([a]) ((a -> Bool) -> Bool) |])),
            ("zipWith",    $(p [| flip . flip zipWith :: (->) ([a]) ((->) ([b]) ((a -> b -> c) -> [c])) |])),
            ("either",     $(p [| flip (flip . either) :: (->) (Either a b) ((a -> c) -> (b -> c) -> c) |])),
            ("uncurry",    $(p [| flip uncurry :: (->) ((a, b)) ((a -> b -> c) -> c) |])),
            ("findIndex",  $(p [| flip findIndex :: (->) ([a]) ((a -> Bool) -> Maybe Int) |])),
            ("findIndices",$(p [| flip findIndices :: (->) ([a]) ((a -> Bool) -> [Int]) |])),
            ("mapAccumL",  $(p [| flip . flip mapAccumL :: acc -> (->) ([x]) ((acc -> x -> (acc, y)) -> (acc, [y])) |])),
            ("mapAccumR",  $(p [| flip . flip mapAccumR :: acc -> (->) ([x]) ((acc -> x -> (acc, y)) -> (acc, [y])) |])),
            ("\\n x f -> iterate f x !! (n::Int)", $(p [| nat_cata :: (->) Int (a -> (a -> a) -> a) |])),
            ("\\n x f -> iterate f x !! (n::Integer)", $(p [| nat_cata :: (->) Integer (a -> (a -> a) -> a) |]))
          ]

-- `normalizeSpaces' removes redundant spaces.
normalizeSpaces = unwords . words

mapAvailables :: M.Map String (Either [Primitive] (Primitive,Primitive))
mapAvailables = M.fromList assocAvailables
-- When dumping the available names, 'assocAvailables' is used instead of mapAvailables because I guess they should not be sorted
assocAvailables = [ (normalizeSpaces s, Left prims) | (s, prims) <- aliases ] ++ [ (pprintPrim prim, Left [prim]) | prim <- totals ] ++ [ (pprintPrim prim, Right tup) | tup@(_,prim) <- partials ]

availableNames :: [String]
availableNames = map fst assocAvailables

-- postprocessを使いたくなるけど，結果同じ表現になっちゃうとまずい．
pprintPrim :: Primitive -> String
pprintPrim (_, e@(VarE name), t) = 
  case nameBase name of 
    ('b':'y':d:'_':name) | isDigit d -> name                            -- Note that the type is omitted, because the class information is lost.
    ('-':'-':'#':name)           -> '(':dropWhile (=='#') name ++")"    -- Note that the type is omitted, because the class information is lost.
    _                                -> normalizeSpaces $ pprint $ TH.SigE (simplify e) t  -- normalizeSpaces is inserted just in case.
pprintPrim (_, e, t) = normalizeSpaces $ pprint $ TH.SigE (simplify e) t  -- normalizeSpaces is inserted just in case.

simplify :: TH.Exp -> TH.Exp
simplify = everywhere (mkT simp)
simp (ConE name) = ConE $ mkName $ nameBase name
simp (VarE name) = VarE $ mkName $ nameBase name
-- We should be careful about removing flips, because that will change the type.
-- simp (AppE (ConE name) e) | nameBase name == "flip" = e
-- simp (AppE (AppE (ConE name1) (ConE name2)) e) | (nameBase name1, nameBase name2) == ("flip",".") = e
simp e = e

namesToPrimitives :: [String] -> ([Primitive], [(Primitive,Primitive)])
namesToPrimitives xss = let ets = map ((mapAvailables !!!) . normalizeSpaces) xss
                        in ([ prim | Left prims <- ets, prim <- prims], [ tup | Right tup <- ets])


-- a !!! b = M.!
a !!! b = case M.lookup b a of Nothing -> error $ "!!! "++b
                               Just x -> x


namessToPrimitives :: [[String]] -> ([[Primitive]], [[(Primitive,Primitive)]])
namessToPrimitives nss = unzip $ map namesToPrimitives nss
prioritizedNamesToNamess :: [(Int,String)] -> [[String]]
prioritizedNamesToNamess ts = let mapPriorName = I.fromListWith (++) [(i,[s]) | (i,s) <- ts]
                              in map (\i -> maybe [] id $ I.lookup i mapPriorName) [fst $ I.findMin mapPriorName .. fst $ I.findMax mapPriorName]

prioritizedNamesToPg :: Maybe Int -> [(Int,String)] -> IO ProgGenSF
prioritizedNamesToPg Nothing   ts = pNTP options ts
prioritizedNamesToPg (Just sz) ts = pNTP options{memoCondPure = \t d -> size t < sz && 0<d {- && d<7 -}} ts

pNTP opt ts = mkPGXOpts mkTrieOptSFIO opt{tv1=True,nrands=repeat 20,timeout=Just 20000} (eqs++ords++doubleCls++ratioCls) clspartialss tot part
  where (tot,part) = namessToPrimitives $ prioritizedNamesToNamess ts
