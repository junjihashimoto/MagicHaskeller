-- 
-- (c) Susumu Katayama
--
{-# OPTIONS -XTemplateHaskell -XNoMonomorphismRestriction -cpp #-}
module MagicHaskeller.LibTH(module MagicHaskeller.LibTH, module MagicHaskeller) where

import MagicHaskeller
import MagicHaskeller.Types(size)
#ifdef TFRANDOM
import System.Random.TF(seedTFGen)
#else
import System.Random(mkStdGen)
#endif
import Control.Monad(liftM2)
import Data.List hiding (tail)
import Data.Char
import Data.Maybe
-- import Data.Ratio
import MagicHaskeller.FastRatio
import qualified Data.Generics as G

import MagicHaskeller.ProgGenSF(mkTrieOptSFIO)

import qualified Data.IntMap as IM
import Data.Hashable

import Prelude hiding (tail, gcd, enumFromThenTo)

-- whether succ is used only for numbers or not
succOnlyForNumbers = False -- This is False, because we now use succ :: Char->Char.

-- total variants of prelude functions
last' = (\x xs -> last (x:xs))
tail = drop 1
-- init xs = zipWith const xs (drop 1 xs)
-- gcd in the latest library is total, but with older versions gcd 0 0 causes an error. 
gcd x y =  gcd' (abs x) (abs y)
  where gcd' a 0  =  a
        gcd' a b  =  gcd' b (a `rem` b)

-- This definition does not work correctly for Fractional numbers.
-- Maybe @[l,m..n]@ could be used for other cases than 'EQ' even if the original enumFromThenTo is hidden. YMMV, though.
enumFromThenTo l m n = map toEnum $
                       case compare lint mint of 
                         EQ -> error "MagicHaskeller.LibTH.enumFromThenTo m m n"
                         LT -> takeWhile (<=nint) $ iterate (+(mint-lint)) lint
                         GT -> takeWhile (>=nint) $ iterate (+(mint-lint)) lint
  where lint = fromEnum l
        mint = fromEnum m
        nint = fromEnum n
initialize, init075, inittv1 :: IO ()
initialize = do setPrimitives [] (list ++ nat ++ natural ++ mb ++ bool ++ $(p [| hd :: (->) [a] (Maybe a) |]) ++ plusInt ++ plusInteger)
                setDepth 10
-- MagicHaskeller version 0.8 ignores the setDepth value and always memoizes.

init075 = do setPG $ mkMemo075 [] (list ++ nat ++ natural ++ mb ++ bool ++ plusInt ++ plusInteger)
             setDepth 10

-- The @tv1@ option prevents type variable @a@ in @forall a. E1(a) -> E2(a) -> ... -> En(a) -> a@ from matching n-ary functions where n>=2.
-- This can safely be used if @(,)@ and @uncurry@ are in the primitive set,
-- because @forall a b c. E1(a->b->c) -> E2(a->b->c) -> ... -> En(a->b->c) -> a -> b -> c@ and @forall a b c. E1((a,b)->c) -> E2((a,b)->c) -> ... -> En((a,b)->c) -> (a,b) -> c@ are isomorphic, and thus the latter can always be used instead of the former.

inittv1 = do setPG $ mkPGOpt (options{primopt = Nothing, tv1 = True})
                             []
                             (list ++ nat ++ natural ++ mb ++ bool ++ tuple ++ $(p [| (hd :: (->) [a] (Maybe a)) |]) ++ plusInt ++ plusInteger )
             setDepth 10

tuple = $(p [| ((,) :: a -> b -> (a,b), uncurry :: (a->b->c) -> (->) (a,b) c) |])
tuple' = $(p [| ((,) :: a -> b -> (a,b), flip uncurry :: (->) (a,b) ((a->b->c) -> c)) |])

-- Specialized memoization tables. Choose one for quicker results.
mall, mlist, mlist', mnat, mlistnat, mnat_nc, mnatural, mlistnatural  :: ProgramGenerator pg => pg
mall  = mkPG (list ++ nat ++ natural ++ mb ++ bool ++ $(p [| hd :: (->) [a] (Maybe a) |]) ++ plusInt ++ plusInteger)
mlist = mkPG list
mlist' = mkPG list'
mnat  = mkPG (nat ++ plusInt)
mnatural  = mkPG (natural ++ plusInteger)
mlistnat = mkPG (list ++ nat ++ plusInt)
mlistnatural = mkPG (list ++ natural ++ plusInteger)

mnat_nc = mkMemo (nat ++ plusInt)

hd :: [a] -> Maybe a
hd []    = Nothing
hd (x:_) = Just x

-- Prefixed (->) means that the parameter can be matched as an assumption when 'constrL' option is True. Also, this info is used when 'guess' option is True. For example of maybe :: a -> (b->a) -> (->) (Maybe b) a, 
--   Gamma |- A   Gamma,B |- A
--  ---------------------------maybe
--   Gamma, Maybe B |- A
-- rather than
--   Gamma |- A   Gamma,B |- A   Gamma |- Maybe B
--  -----------------------------------------------maybe
--   Gamma |- A
-- This is just for the efficiency reason, and one can use the infixed form, i.e., maybe :: a -> (b->a) -> Maybe b -> a, if efficiency does not matter. In fact, this info is ignored if both 'guess' and 'constrL' options are False.

mb, mb', nat, natural, nat', nat'woPred, natural', plusInt, plusInteger, list'', list', list, bool, boolean, intinst, list1, list1', list2, list3, list3', nats, tuple, tuple', rich, rich', debug :: [Primitive]
mb = $(p [| ( Nothing :: Maybe a, Just :: a -> Maybe a, maybe :: a -> (b->a) -> (->) (Maybe b) a ) |] )
mb' = $(p [| ( Nothing :: Maybe a, Just :: a -> Maybe a, flip . maybe :: a -> (->) (Maybe b) ((b->a) -> a) ) |] )

nat = $(p [| (0 :: Int, (1+) :: Int->Int, nat_para :: (->) Int (a -> (Int -> a -> a) -> a)) |] )
natural = $(p [| (0 :: Integer, (1+) :: Integer->Integer, nat_para :: (->) Integer (a -> (Integer -> a -> a) -> a)) |] )
nat' = $(p [| (0 :: Int, (1+) :: Int->Int, nat_cata :: (->) Int (a -> (a -> a) -> a), pred :: Int->Int) |] )
nat'woPred = $(p [| (0 :: Int, (1+) :: Int->Int, nat_cata :: (->) Int (a -> (a -> a) -> a)) |] )
natural' = $(p [| (0 :: Integer, (1+) :: Integer->Integer, nat_cata :: (->) Integer (a -> (a -> a) -> a), pred :: Integer->Integer) |] )
plusInt = $(p [| (+) :: (->) Int ((->) Int Int) |])
plusInteger = $(p [| (+) :: (->) Integer ((->) Integer Integer) |])

-- Nat paramorphism
nat_para :: Integral i => i -> a -> (i -> a -> a) -> a
nat_para i x f = np (abs i) -- Version 0.8 does not deal with partial functions very well.
    where np 0 = x
          np i = let i' = i-1
                 in f i' (np i')

-- Nat paramorphism.  nat_cata i x f == iterate f x `genericIndex` abs i holds, but the following implementation is much more efficient (and thus safer).
nat_cata :: Integral i => i -> a -> (a -> a) -> a
nat_cata i x f = nc (abs i) -- Version 0.8 does not deal with partial functions very well.
    where nc 0 = x
          nc i = f (nc (i-1))

list'' = $(p [| ([] :: [a], (:), flip . flip foldr :: a -> (->) [b] ((b -> a -> a) -> a), tail :: (->) [a] [a]) |] ) -- foldr's argument order makes the synthesis slower:)
list' = $(p [| ([] :: [a], (:), foldr :: (b -> a -> a) -> a -> (->) [b] a, tail :: (->) [a] [a]) |] ) -- foldr's argument order makes the synthesis slower:)
list  = $(p [| ([] :: [a], (:), list_para :: (->) [b] (a -> (b -> [b] -> a -> a) -> a)) |] )

-- List paramorphism
list_para :: [b] -> a -> (b -> [b] -> a -> a) -> a
list_para []     x f = x
list_para (y:ys) x f = f y ys (list_para ys x f)

bool = $(p [| (True, False, iF :: (->) Bool (a -> a -> a)) |] )

iF :: Bool -> a -> a -> a
iF True  t f = t
iF False t f = f

-- | 'postprocess' replaces uncommon functions like catamorphisms with well-known functions.
postprocess :: Exp -> Exp
postprocess (AppE (AppE (AppE (InfixE (Just e1) (VarE name) (Just e2)) e3) e4) e5) | nameBase name == "." = postprocess $ ((e1 `AppE` (e2 `AppE` e3)) `AppE` e4) `AppE` e5   -- ad hoc pattern:S
postprocess (AppE (AppE (AppE (AppE (ConE name) e1) e2) e3) e4) | nameBase name == "(,,,)" = postprocess $ TupE [e1, e2, e3, e4]
postprocess (AppE (AppE (AppE (AppE (VarE name) e1) e2) e3) e4) | nameBase name == "flip"  = postprocess $ ((e1 `AppE` e3) `AppE` e2) `AppE` e4
postprocess (AppE (InfixE (Just e1) (VarE name) (Just e2)) e3) | nameBase name == "." = postprocess $ e1 `AppE` (e2 `AppE` e3)
postprocess (AppE (e@(AppE (AppE (ConE name) p) t)) f) | nameBase name == "(,,)" = postprocess $ TupE [p,t,f]
postprocess (AppE (e@(AppE (AppE (VarE name) p) t)) f)
    = case nameBase name of
        "iF"       -> CondE ppp ppt ppf
        "enumFromThenTo" -> ArithSeqE $ FromThenToR ppp ppt ppf
        "nat_cata" -> InfixE (Just $ (VarE (mkName "iterate") `AppE` ppf) `AppE` ppt)
                             (VarE (mkName "!!"))     -- Should I use genericIndex instead of (!!) also here?
                             (Just $ case ppp of LitE (IntegerL i)  -> LitE $ IntegerL $ abs i
                                                 _                 -> VarE (mkName "abs") `AppE` ppp)
        "flip"     -> postprocess $ (ppp `AppE` ppf) `AppE` ppt
        "."        -> postprocess (p `AppE` (t `AppE` f))
        _          -> postprocess e `AppE` ppf
  where ppp = postprocess p
        ppt = postprocess t
        ppf = postprocess f
postprocess (AppE f@(AppE (ConE name) lj) e) | nameBase name == "(,)" = postprocess $ TupE [lj, e]
postprocess (AppE f@(AppE (VarE name) lj) e)
    = case nameBase name of "drop" -> case pplj of LitE (IntegerL j) | j<=0 -> ppe
                                                                     | j> 0 -> ppdrop j e
                                                   _                 -> (dropE `AppE` pplj) `AppE` ppe
                            "enumFromTo" -> ArithSeqE $ FromToR pplj ppe
                            "last'" -> case ppe of AppE (VarE rev) e' | nameBase rev == "reverse" -> ((VarE (mkName "foldr") `AppE` constE) `AppE` pplj) `AppE` e'   -- last (x : reverse xs) ==> foldr const x xs
                                                   _ -> VarE (mkName "last") `AppE` InfixE (Just pplj) (ConE $ mkName ":") (Just ppe)
                            "filter" -> case ppe of AppE (VarE rev) e' | nameBase rev == "reverse" -> reverseE `AppE` ((VarE (mkName "filter") `AppE` pplj) `AppE` e')   -- filter p (reverse xs) ==> reverse (filter p xs)  This is useful in the case of (reverse . drop 1 . reverse) (filter p ((reverse . drop 1 . reverse) xs)). Also, there can be a case of last' x (filter p ((reverse . drop 1 . reverse) xs))
                                                    _ -> (VarE (mkName "filter") `AppE` pplj) `AppE` ppe
                            _            -> postprocess f `AppE` ppe
  where pplj = postprocess lj 
        ppe  = postprocess e
postprocess (AppE (InfixE m@(Just _) op Nothing)    e) = postprocess (InfixE m        op (Just e))
postprocess (AppE (InfixE Nothing    op m@(Just _)) e) = postprocess (InfixE (Just e) op m)
postprocess (AppE v@(VarE name) e)
    = case nameBase name of
--        'b':'y':'1':'_':nm -> VarE $ mkName$ by1 nm
        "tail"   -> ppdrop 1 e
        "negate" -> case ppe of LitE (IntegerL i)        -> LitE $ IntegerL $ (-i)
                                LitE (RationalL r)       -> LitE $ RationalL $ (-r)
                                _                        -> AppE v ppe
        "abs"    -> case ppe of LitE (IntegerL i)        -> LitE $ IntegerL $ abs i
                                LitE (RationalL r)       -> LitE $ RationalL $ abs r
                                _                        -> AppE (ppv v) ppe
        "floor"  -> case ppe of LitE (IntegerL i)        -> LitE $ IntegerL i
                                LitE (RationalL r)       -> LitE $ IntegerL $ floor r
                                _                        -> AppE v ppe
        "round"  -> case ppe of LitE (IntegerL i)        -> LitE $ IntegerL i
                                LitE (RationalL r)       -> LitE $ IntegerL $ round r
                                _                        -> AppE v ppe
        "ceiling" -> case ppe of LitE (IntegerL i)        -> LitE $ IntegerL i
                                 LitE (RationalL r)       -> LitE $ IntegerL $ ceiling r
                                 _                        -> AppE v ppe
        "fromIntegral" -> case ppe of LitE i      -> LitE i
                                      _           -> AppE v ppe
        "exponent"   -> case ppe of
                      LitE (IntegerL i)        -> LitE $ IntegerL $ toInteger $ exponent $ fromIntegral i
                      LitE (RationalL r)       -> LitE $ IntegerL $ toInteger $ exponent $ fromRational r
                      _                        -> AppE v ppe
        "succ"   -> case ppe of
                      LitE (IntegerL i)        -> LitE $ IntegerL $ succ i
                      LitE (RationalL r)       -> LitE $ RationalL $ succ r
                      LitE (CharL c)           -> LitE $ CharL $ succ c
                      InfixE (Just (LitE (IntegerL n))) (VarE nm) (Just e)
                        | nameBase nm == "+"    -> InfixE (Just $ LitE $ IntegerL $ succ n) plusE (Just e)
                      AppE (VarE nm) e
                        | succOnlyForNumbers &&
                          nameBase nm == "succ" -> InfixE (Just $ LitE $ IntegerL 2) plusE (Just e) -- This is OK, if we use succ only for numbers.
                      _                       -> AppE (ppv v) ppe
        "reverse" -> case ppe of
                       LitE (StringL xs)        -> LitE $ StringL $ reverse xs
                       ListE es                 -> ListE $ reverse $ map postprocess es
                       ArithSeqE (FromToR (LitE (IntegerL f)) (LitE (IntegerL t))) -> ArithSeqE $ FromThenToR (LitE $ IntegerL t) (LitE $ IntegerL $ t-1) (LitE $ IntegerL f)
                       AppE (VarE name) e' | nameBase name == "reverse" -> e'
                       _         -> AppE reverseE ppe
        "length" -> case ppe of
                       LitE (StringL xs)        -> LitE $ IntegerL $ toInteger $ length xs
                       ListE es                -> LitE $ IntegerL $ toInteger $ length es
                       ArithSeqE (FromToR (LitE (IntegerL f)) (LitE (IntegerL t))) -> LitE $ IntegerL $ t - f + 1 -- can be bottom, if t is less than f.
                       AppE (VarE name) e' | nameBase name == "reverse" -> AppE lengthE e' -- length . reverse => length
                       -- There can also be the length . map f => length rule. The length . map f pattern can appear when f includes some absent argument.
                       _         -> AppE lengthE ppe
        "sum"    -> case ppe of
                       AppE (VarE name) e' | nameBase name == "reverse" -> AppE sumE e'
                       _         -> AppE sumE ppe
        "product" -> case ppe of
                       AppE (VarE name) e' | nameBase name == "reverse" -> AppE productE e'
                       _         -> AppE productE ppe
        nb       -> case IM.lookup (hash nb) byMap of Just fun -> fun ppe $ AppE (ppv v) ppe
                                                      Nothing  -> AppE (ppv v) ppe
  where ppe = postprocess e 
-- The following pattern is actually unnecessary if only eta-long normal expressions will be generated.
postprocess e@(VarE _)          = ppv e
postprocess (AppE f x)          = postprocess f `AppE` postprocess x
postprocess (InfixE me1 op me2) 
  = let j1 = fmap postprocess me1
        j2 = fmap postprocess me2
    in case op of 
          VarE opname -> 
            case (j1,j2) of
                       (Just (LitE (IntegerL i1)), Just (LitE (IntegerL i2))) ->
                                        case nameBase opname of "+" -> LitE $ IntegerL $ i1+i2
                                                                "-" -> LitE $ IntegerL $ i1-i2
                                                                "*" -> LitE $ IntegerL $ i1*i2
                                                                _   -> theDefault
                       (Just (LitE (IntegerL i1)), Just (InfixE (Just (LitE (IntegerL i2))) (VarE inopn) me3))
                                    | nameBase opname == "+" && nameBase inopn `elem` ["+","-"] -> InfixE (Just $ LitE $ IntegerL $ i1+i2) (VarE $ ppopn inopn) me3
                       _ -> theDefault
                   where theDefault = InfixE j1 (VarE $ ppopn opname) j2
          ConE opname -> InfixE j1 (ConE $ ppopn opname) j2

postprocess (LamE pats e)       = ppLambda pats (postprocess e)

postprocess (TupE es)           = TupE (map postprocess es)
postprocess (ListE es)          = ListE (map postprocess es)
postprocess (SigE e ty)         = postprocess e `SigE` ty
postprocess e = e

byMap = IM.fromList $ byEqs++byOrds
byEqs  = (hash "deleteFirstsBy", skipEq "\\\\") : [ (hash $ xs++"By", skipEq xs) | xs <- ["nub","delete","union","intersect","group"]]
byOrds = [ (hash $ xs++"By", skipOrd xs) | xs <- ["sort","insert","minimum","maximum"]]

skip op namestr = \eqExp wholeExp -> case eqExp of VarE name | nameBase name == op -> VarE $ mkName namestr
                                                   _         -> wholeExp
skipEq  = skip "=="
skipOrd = skip "compare"

shown `appearsIn` e = G.everything (||) (False `G.mkQ` (\name -> show (name::Name) == shown)) e

{-
by1 "le"   = "<="
by1 "less" = "<"
by1 name   = name
-}

-- この辺はCoreLangでやるべきという気も．少なくとも，そっちで関数を定義すべき．
-- \x -> iF foo bar x の場合も先にη簡約されてしまうとイマイチではある．ので，η簡約はiF, nat_cata, tailなどの処理の後にやる．
-- For readability, we apply eta-reduction only when we can fully eta-reduce at the outermost lambda-abstraction.
ppLambda [VarP n] (AppE e (VarE n')) | shown == show n' && not (shown `appearsIn` e) = e
                                               where shown = show n
ppLambda [VarP n, VarP m, VarP l] (AppE (AppE (AppE e (VarE n')) (VarE m')) (VarE l')) 
  | shown == show n' && showm == show m' && showl == show l' && free = e
  | shown == show m' && showm == show n' && showl == show l' && free = flipE `AppE` e
                                               where shown = show n
                                                     showm = show m
                                                     showl = show l
                                                     free  = not (shown `appearsIn` e) && not (showm `appearsIn` e) && not (showl `appearsIn` e)
ppLambda [VarP n, VarP m] (AppE (AppE e (VarE n')) (VarE m')) 
  | shown == show n' && showm == show m' && free = e
  | shown == show m' && showm == show n' && free = flipE `AppE` e
                                               where shown = show n
                                                     showm = show m
                                                     free  = not (shown `appearsIn` e) && not (showm `appearsIn` e)
-- postprocess (LamE [WildP]         e)         = constE `AppE` e        -- not sure if this is more readable....
ppLambda [VarP n, WildP] (VarE n') | show n == show n' = constE
ppLambda [VarP n]        (VarE n') | show n == show n' = VarE (mkName "id")
ppLambda [VarP n, VarP m] (InfixE (Just (VarE n')) op (Just (VarE m'))) | show n == show n' &&  show m == show m' = op
ppLambda pats@[VarP n, VarP m] e@(InfixE (Just (VarE n')) op@(VarE opna) (Just (VarE m'))) 
  = if show n == show m' &&  show m == show n'
    then case nameBase opna of "<"                                              -> VarE (mkName ">")
                               "<="                                             -> VarE (mkName ">=")
                               "-"                                              -> VarE (mkName "subtract")
                               name | name `elem` ["==","/=","+","*","&&","||"] -> op
                                    | otherwise                                 -> flipE `AppE` op
    else LamE pats e
ppLambda [VarP n]         (InfixE (Just (VarE n')) op (Just e))         
  | shown == show n' && not (shown `appearsIn` e) = case op of VarE name | nameBase name == "-" -> VarE (mkName "subtract") `AppE` e
                                                               _                                -> InfixE Nothing op (Just e)
  where shown = show n
ppLambda [VarP n]         (InfixE (Just e) op (Just (VarE n')))         | shown == show n' && not (shown `appearsIn` e) = InfixE (Just e) op Nothing
                                                                  where shown = show n
ppLambda pats            e         = LamE pats e



ppv e@(VarE name) | nameBase name `elem` ["iF", "nat_cata"] = LamE [ VarP n | n <- names ] (postprocess (AppE (AppE (AppE e p) t) f))
                  | nameBase name == "last'"                = LamE [ VarP n | n <- tail names ] (postprocess (AppE (AppE e t) f))
                  | otherwise                               = VarE $ ppopn name
    where names   = [ mkName [n] | n <- "ptf" ]
          [p,t,f] = map VarE names

ppopn name = case nameModule name of Just mod | --  mod `elem` ["GHC.Base", "GHC.List", "GHC.Char", "GHC.Num"]  -- Rather, optional qualifications such as Data.Map. and Data.Text. should be qualified, and all other qualifications should be removed.
                                                not $ mod `elem` ["Data.Map", "Data.Set", "Data.Text", "Data.ByteString"] -- These are just examples for now.
                                                     -> mkName $ nameBase name
                                     _        -> name


ppdrop m0j e 
  = case postprocess e of
      AppE (AppE (VarE drn) (LitE (IntegerL i))) list | nameBase drn == "drop" -> droppy (m0j + i) list -- NB: m0j and i are both positive.
      ppe                                             -> droppy m0j ppe
  where droppy i e = (dropE `AppE` (LitE $ IntegerL i)) `AppE` e

constE = VarE $ mkName "const"
flipE  = VarE $ mkName "flip"
plusE  = VarE $ mkName "+"
dropE  = VarE $ mkName "drop"
reverseE = VarE $ mkName "reverse"
lengthE  = VarE $ mkName "length"
sumE     = VarE $ mkName "sum"
productE = VarE $ mkName "product"

procSucc n (AppE (VarE name) e) | nameBase name == "succ" = procSucc (n+1) e
procSucc n (LitE (CharL c))     = LitE $ CharL $ iterate succ c `genericIndex` n
procSucc n (LitE (IntegerL i))  = LitE $ IntegerL $ n+i
procSucc n (LitE (RationalL r)) = LitE $ RationalL $ fromInteger n + r
procSucc n e | succOnlyForNumbers = InfixE (Just $ LitE $ IntegerL n) (VarE $ mkName "+") (Just $ postprocess e) -- This is OK, if we use succ only for numbers.
             | otherwise          = iterate (AppE (VarE $ mkName "succ")) (postprocess e) `genericIndex` n

postprocessQ :: Exp -> ExpQ
{- This type of patterns is not available yet.
postprocessQ (AppE (AppE (AppE (VarE 'iF)        p)  t) f) = [| if $(postprocessQ p) then $(postprocessQ t) else $(postprocessQ f) |]
postprocessQ (AppE (AppE (AppE (VarE 'nat_para)  i)  x) f) = [| let {np 0  = $(postprocessQ x); np (n+1)  = $(postprocessQ f) n (np n)}     in np (abs $(postprocessQ i)) |]
postprocessQ (AppE (AppE (AppE (VarE 'list_para) xs) x) f) = [| let {lp [] = $(postprocessQ x); lp (y:ys) = $(postprocessQ f) y ys (lp ys)} in lp $(postprocessQ xs) |]
-}
postprocessQ (AppE (e@(AppE (AppE (VarE name)        p)  t)) f)
    = case nameBase name of
        "iF"        -> [| if $(postprocessQ p) then $(postprocessQ t) else $(postprocessQ f) |]
        "nat_cata"  -> [| iterate $(postprocessQ f) $(postprocessQ t) !! abs $(postprocessQ p) |]
        "nat_para"  -> [| let {np 0  = $(postprocessQ t); np n  = let i=n-1 in $(postprocessQ f) i (np i)}     in np (abs $(postprocessQ p)) |]
        "list_para" -> [| let {lp [] = $(postprocessQ t); lp (y:ys) = $(postprocessQ f) y ys (lp ys)} in lp $(postprocessQ p) |]
        _           -> [| $(postprocessQ e) $(postprocessQ f) |]
postprocessQ (AppE f x) = [| $(postprocessQ f) $(postprocessQ x) |]
-- postprocessQ (VarE 'iF) = [| \p t f -> if p then t else f |] -- This pattern is actually unnecessary because only eta-long normal expressions will be generated.
-- ...
postprocessQ (InfixE me1 op me2) = let fmapM f Nothing  = return Nothing
                                       fmapM f (Just x) = fmap Just (f x)
                                   in liftM2 (\e1 e2 -> InfixE e1 op e2) (fmapM postprocessQ me1) (fmapM postprocessQ me2)
postprocessQ (LamE pats e) = fmap (LamE pats) (postprocessQ e)
postprocessQ (TupE es) = fmap TupE (mapM postprocessQ es)
postprocessQ (ListE es) = fmap ListE (mapM postprocessQ es)
postprocessQ (SigE e ty) = fmap (`SigE` ty) (postprocessQ e)
postprocessQ e = return e


exploit :: (Typeable a, Filtrable a) => 
           Bool -- ^ whether to include functions with unused arguments
           -> (a -> Bool) -> IO ()
exploit withAbsents pred = filterThenF pred (everything (reallyall::ProgGenSF) withAbsents) >>= pprs

boolean = $(p [| ((&&) :: (->) Bool ((->) Bool Bool),
                  (||) :: (->) Bool ((->) Bool Bool),
                  not  :: (->) Bool Bool) |] )
{-
-- Type classes are not supported yet....
-- Without tuning of the probability distribution over Chars and Lists, these are almost useless.
eq = $(p [| ((==) :: Int->Int->Bool,   (/=) :: Int->Int->Bool,
             (==) :: Char->Char->Bool, (/=) :: Char->Char->Bool,
             (==) :: Bool->Bool->Bool, (/=) :: Bool->Bool->Bool,
             (==) :: [Int] ->[Int] ->Bool, (/=) :: [Int] ->[Int]->Bool,
             (==) :: [Char]->[Char]->Bool, (/=) :: [Char]->[Char]->Bool,
             (==) :: [Bool]->[Bool]->Bool, (/=) :: [Bool]->[Bool]->Bool) |] )
-- ...bothered.
{-
eq = $(p [| ((==) :: Int->Int->Bool,   (/=) :: Int->Int->Bool,
             (==) :: Char->Char->Bool, (/=) :: Char->Char->Bool,
             (==) :: Bool->Bool->Bool, (/=) :: Bool->Bool->Bool) |])
-}
-}
newtype Partial a = Part {undef :: a}
undefs = map (\[a,b] -> (a,b)) $
         [-- Bool や Orderingのように、ありがちな値を返してしまうものは、採用すべきでない。$(p [| (Part False :: Partial Bool,     undefined :: Partial Bool) |]), $(p [| (Part EQ    :: Partial Ordering, undefined :: Partial Ordering) |]),
          $(p [| (Part 53        :: Partial Int,      undefined :: Partial Int) |]), 
          $(p [| (Part '\29'     :: Partial Char,     undefined :: Partial Char) |]),
          $(p [| (Part [43]      :: Partial [Int],    undefined :: Partial [Int]) |]), 
          $(p [| (Part "wleajkf" :: Partial [Char],   undefined :: Partial [Char]) |])]
by1_head :: Partial a -> [a] -> a
by1_head (Part u) [] = u
by1_head _     (x:_) = x
(--#!!) :: Partial a -> [a] -> Int -> a
(--#!!) (Part u) []     n = u
(--#!!) (Part u) (x:xs) n 
  = case compare n 0 of 
     LT -> u
     EQ -> x
     GT -> (--#!!) (Part u) xs (n-1) 

prelPartial = $(p [| ( by1_head :: Partial a -> (->) [a] a,
                       (--#!!) :: Partial a -> [a] -> (->) Int a) |] )

newtype Equivalence a = Eq {(--#==) :: a -> a -> Bool}
eq = Eq (==)
by1_eqMaybe :: Equivalence a -> Equivalence (Maybe a)
by1_eqMaybe (Eq op) = Eq $ eqMaybeBy op
eqMaybeBy _ Nothing  Nothing  = True
eqMaybeBy _ Nothing  (Just _) = False
eqMaybeBy _ (Just _) Nothing  = False
eqMaybeBy e (Just x) (Just y) = e x y
by1_eqList :: Equivalence a -> Equivalence [a]
by1_eqList (Eq e) = Eq $ eqListBy e
eqListBy _ [] [] = True
eqListBy _ [] _  = False
eqListBy _ _  [] = False
eqListBy e (x:xs) (y:ys) = e x y && eqListBy e xs ys

by2_eqEither :: Equivalence a -> Equivalence b -> Equivalence (Either a b)
by2_eqEither (Eq e1) (Eq e2) = Eq $ eqEitherBy e1 e2
eqEitherBy e1 _  (Left  x) (Left  y) = e1 x y
eqEitherBy _  _  (Left  _) (Right _) = False
eqEitherBy _  _  (Right _) (Left  _) = False
eqEitherBy _  e2 (Right x) (Right y) = e2 x y
by2_eqPair :: Equivalence a -> Equivalence b -> Equivalence (a,b)
by2_eqPair (Eq e1) (Eq e2) = Eq $ eqPairBy e1 e2
eqPairBy e1 e2 (x,y) (z,w) = e1 x z && e2 y w

eqs = $(p [| (eq :: Equivalence Bool, eq :: Equivalence Ordering, eq :: Equivalence Int,  eq :: Equivalence Char, -- eq :: Equivalence (Ratio Int) is defined in ratioCls
              eq :: Equivalence [Int],  eq :: Equivalence [Char], by1_eqMaybe :: Equivalence a -> Equivalence (Maybe a), by1_eqList :: Equivalence a -> Equivalence [a],
              by2_eqEither :: Equivalence a -> Equivalence b -> Equivalence (Either a b), by2_eqPair :: Equivalence a -> Equivalence b -> Equivalence (a,b)) |])
prelEqRelated = [$(p [| ((--#==) :: Equivalence a -> (->) a (a -> Bool), (--#/=) :: Equivalence a -> (->) a (a -> Bool)) |]), 
                 $(p [|  by1_elem :: Equivalence a -> a -> [a] -> Bool |]), 
                 []]
dataListEqRelated = [[],
                     $(p [| (by1_group :: Equivalence a -> [a] -> [[a]], 
                             by1_nub :: Equivalence a -> [a] -> [a]) |]), 
                     $(p [| (by1_isPrefixOf :: Equivalence a -> [a] -> [a] -> Bool, 
                             by1_isSuffixOf :: Equivalence a -> [a] -> [a] -> Bool, 
                             by1_isInfixOf  :: Equivalence a -> [a] -> [a] -> Bool, 
                             by1_stripPrefix :: Equivalence a -> [a] -> [a] -> Maybe [a],
                             by1_lookup :: Equivalence a -> a -> (->) [(a, b)] (Maybe b)
                            ) |])]
                      
(--#/=) :: Equivalence a -> a -> a -> Bool
(--#/=) (Eq e) x y = not $ e x y
by1_elem :: Equivalence a -> a -> [a] -> Bool
by1_elem (Eq e) k = any (e k)
by1_group :: Equivalence a -> [a] -> [[a]]
by1_group (Eq e) = groupBy e
by1_nub :: Equivalence a -> [a] -> [a]
by1_nub (Eq e) = nubBy e
by1_isPrefixOf :: Equivalence a -> [a] -> [a] -> Bool
by1_isPrefixOf _      []     _      = True
by1_isPrefixOf _      _      []     = False
by1_isPrefixOf e@(Eq op) (x:xs) (y:ys) = op x y && by1_isPrefixOf e xs ys
by1_isSuffixOf :: Equivalence a -> [a] -> [a] -> Bool
by1_isSuffixOf e xs ys = by1_isPrefixOf e (reverse xs) (reverse ys)
by1_isInfixOf :: Equivalence a -> [a] -> [a] -> Bool
by1_isInfixOf  e xs ys = any (by1_isPrefixOf e xs) (tails ys)
by1_stripPrefix :: Equivalence a -> [a] -> [a] -> Maybe [a]
by1_stripPrefix eq         []     ys     = Just ys
by1_stripPrefix eq@(Eq op) (x:xs) (y:ys) | op x y = by1_stripPrefix eq xs ys
by1_stripPrefix _          _      _      = Nothing
by1_lookup :: Equivalence a -> a -> (->) [(a, b)] (Maybe b)
by1_lookup _          _   []          =  Nothing
by1_lookup eq@(Eq op) key ((x,y):xys)
    | op key x          =  Just y
    | otherwise         =  by1_lookup eq key xys

newtype Ordered a = Ord {by1_compare :: a->a->Ordering}
cmp = Ord compare
by1_cmpMaybe :: Ordered a -> Ordered (Maybe a)
by1_cmpMaybe (Ord compare) = Ord $ compareMaybeBy compare
compareMaybeBy _       Nothing  Nothing  = EQ
compareMaybeBy _       Nothing  (Just _) = LT 
compareMaybeBy _       (Just _) Nothing  = GT 
compareMaybeBy compare (Just x) (Just y) = compare x y
by1_cmpList :: Ordered a -> Ordered [a]
by1_cmpList (Ord compare) = Ord $ compareListBy compare
compareListBy _ [] [] = EQ
compareListBy _ [] _  = LT
compareListBy _ _  [] = GT
compareListBy compare (x:xs) (y:ys) = case compare x y of EQ -> compareListBy compare xs ys
                                                          o  -> o
by2_cmpEither :: Ordered a -> Ordered b -> Ordered (Either a b)
by2_cmpEither (Ord compare1) (Ord compare2) = Ord $ compareEitherBy compare1 compare2
compareEitherBy compare1 _        (Left x)  (Left y)  = compare1 x y
compareEitherBy _        _        (Left _)  (Right _) = LT
compareEitherBy _        _        (Right _) (Left _)  = GT
compareEitherBy _        compare2 (Right x) (Right y) = compare2 x y
by2_cmpPair :: Ordered a -> Ordered b -> Ordered (a, b)
by2_cmpPair (Ord compare1) (Ord compare2) = Ord $ comparePairBy compare1 compare2
comparePairBy compare1 compare2 (x,y) (z,w) = case compare1 x z of EQ -> compare2 y w
                                                                   o  -> o
ords = $(p [| (cmp :: Ordered Bool, cmp :: Ordered Ordering, -- なぜかcomment outされていたので復活させてみた。問題あるなら戻すが。
               cmp :: Ordered Int, cmp :: Ordered Char, -- cmp :: Ordered (Ratio Int) is defined in ratioCls
               by1_cmpMaybe :: Ordered a -> Ordered (Maybe a), by1_cmpList :: Ordered a -> Ordered [a],
               by2_cmpEither :: Ordered a -> Ordered b -> Ordered (Either a b), by2_cmpPair :: Ordered a -> Ordered b -> Ordered (a,b)) |])
prelOrdRelated = [$(p [| by1_compare :: Ordered a -> a->a->Ordering |]) ++
                  $(p [| ((--#<=)  :: Ordered a -> a -> a -> Bool, (--#<) :: Ordered a -> a -> a -> Bool,
                          by1_max     :: Ordered a -> (->) a (a->a),    by1_min :: Ordered a -> (->) a (a->a)) |] ), [],
                  []]
                   --  maximum_by :: Ordered a -> [a] -> a,       minimum_by :: Ordered a -> [a] -> a) |]) -- Those are not total.
dataListOrdRelated = [[],[],$(p [| by1_sort :: Ordered a -> [a] -> [a] |] )]

(--#<=) (Ord compare) x y = case compare x y of GT -> False
                                                _  -> True
(--#<)  (Ord compare) x y = case compare x y of LT -> True
                                                _  -> False
by1_max c x y = if (--#<=) c x y then y else x
by1_min c x y = if (--#<=) c x y then x else y
by1_sort (Ord compare) = sortBy compare

intinst = intinst1++intinst2
intinst1 = $(p [| (
                   {- 
                   (<=) :: Int->Int->Bool,
                   (<)  :: Int->Int->Bool,
               --    (>=) :: Int->Int->Bool,
               --    (>)  :: Int->Int->Bool,
                   max  :: Int->Int->Int,
                   min  :: Int->Int->Int,
-}
                   (-)  :: Int->Int->Int,
                   (*)  :: Int->Int->Int -- ,
               --    div  :: Int->Int->Int,
               --    mod  :: Int->Int->Int,
               --    (^)  :: Int->Int->Int
                  ) |])
intpartials = $(p [| (               
                      div  :: Int->Int->Int,
                      mod  :: Int->Int->Int,
                      (^)  :: Int->Int->Int
                     ) |])
intinst2 = $(p [| (
                   gcd  :: Int->Int->Int,
                   lcm  :: Int->Int->Int) |])

list1 = $(p [| (map       :: (a -> b) -> (->) [a] [b],
                (++)      :: (->) [a] ([a] -> [a]),
                filter    :: (a -> Bool) -> [a] -> [a],
                concat    :: (->) [[a]] [a],
                concatMap :: (a -> [b]) -> (->) [a] [b],
                length    :: (->) [a] Int,
                replicate :: Int -> a -> [a],
                take      :: Int -> [a] -> [a],
                drop      :: Int -> [a] -> [a],
                takeWhile :: (a -> Bool) -> [a] -> [a],
                dropWhile :: (a -> Bool) -> [a] -> [a]) |] )
list1' = $(p [| (flip map :: (->) [a] ((a -> b) -> [b]),
                 (++)      :: (->) [a] ([a] -> [a]),
                 filter    :: (a -> Bool) -> [a] -> [a],
                 concat    :: (->) [[a]] [a],
                 flip concatMap :: (->) [a] ((a -> [b]) -> [b]),
                 length    :: (->) [a] Int,
                 replicate :: Int -> a -> [a],
                 take      :: Int -> [a] -> [a],
                 drop      :: Int -> [a] -> [a],
                 takeWhile :: (a -> Bool) -> [a] -> [a],
                 dropWhile :: (a -> Bool) -> [a] -> [a]) |] )
list2 = $(p [| (
                lines            :: [Char] -> [[Char]],
                words            :: [Char] -> [[Char]],
                unlines            :: [[Char]] -> [Char],
                unwords            :: [[Char]] -> [Char] ) |] )

list3 = $(p [| (reverse :: [a] -> [a],
                and         :: (->) [Bool] Bool,
                or          :: (->) [Bool] Bool,
                any         :: (a -> Bool) -> (->) [a] Bool,
                all         :: (a -> Bool) -> (->) [a] Bool,
                zipWith          :: (a->b->c) -> (->) [a] ((->) [b] [c]) ) |] )
list3' = $(p [| (reverse :: [a] -> [a],
                 and         :: (->) [Bool] Bool,
                 or          :: (->) [Bool] Bool,
                 flip any         :: (->) [a] ((a -> Bool) -> Bool),
                 flip all         :: (->) [a] ((a -> Bool) -> Bool),
                 flip . flip zipWith :: (->) [a] ((->) [b] ((a->b->c) -> [c])) ) |] )

nats = $(p [| (1 ::Int, 2 :: Int, 3 :: Int) |])

reallyall :: ProgramGenerator pg => pg
reallyall = mkPG rich

nrnds = repeat 5


-- comment out (mkStdGen 123456) when using 0.8.3*

#ifdef TFRANDOM
generator = seedTFGen (3497676378205993723,16020016691208771845,6545968067796471226,2770936286170065919)
#else
generator = mkStdGen 123456
#endif

-- Currently only the pg==ConstrLSF case makes sense.
mix, poormix :: ProgramGenerator pg => pg
mix = mkPGSF generator
              nrnds
              []
              (list++bool)
              rich

-- I think having both succ and pred is not good, and pred x can be synthesized as x - succ 0.
-- Still, having both cons and tail is OK.
soso =        (list'' ++
                    nat'woPred ++
                        mb' ++ bool ++ plusInt ++ -- x $(p [| (hd :: [a] -> Maybe a, (+) :: Int -> Int -> Int) |]) ++
                    boolean ++ intinst1 ++
                    list1' ++ list3')
rich = soso ++ list2 ++ intinst2 ++ $(p [| init :: [a] -> [a] |])

poormix = mkPGSF generator
              nrnds
              []
              $(p [| ([] :: [a], True) |] )
              rich

-- just for debugging
ra :: ProgramGenerator pg => pg
ra = mkPG rich'
rich' =      (list'++bool++boolean++
                    list1 ++ list3)

mx :: ProgramGenerator pg => pg
mx = mkPGSF generator
             nrnds
             []
             (list++bool)
             rich'

debug = $(p [| (list_para :: (->) [b] (a -> (b -> [b] -> a -> a) -> a), concatMap :: (a -> [b]) -> (->) [a] [b]) |] )

-- | Library used by the program server backend
pgfull :: ProgGenSF
-- pgfull = mkPG ($(MagicHaskeller.LibTH.load "libsrc/PreludeList.hs") ++ mb ++ bool ++ boolean ++ $(p [| ([], (:), (+) :: Int -> Int -> Int, replicate :: Int -> a -> [a]) |]) ++ $(p [| until ::  (a -> Bool) -> (a -> a) -> a -> a |]) ++ nat ++ intinst)  -- rich とあまり変わらない．
pgfull = mkPGXOpt options{tv1=True,nrands=repeat 20,timeout=Just 100000} (eqs++ords) clspartialss full tupartialssNormal
-- A pgfull must be a CAF, so we must have pgfulls and access pgfullSized via pgfulls. Directly calling pgfullSized is heap-inefficient.
pgfulls :: [ProgGenSF]
pgfulls = map pgfullSized [0..]
  where pgfullSized sz = mkPGXOpt options{memoCondPure = \t d -> size t < sz && 0<d {- && d<7 -}, tv1=True,nrands=repeat 20,timeout=Just 100000} (eqs++ords) clspartialss full tupartialssNormal

mkPgFull :: IO ProgGenSF
mkPgFull = mkPGXOpts mkTrieOptSFIO options{tv1=True,nrands=repeat 20,timeout=Just 20000} (eqs++ords) clspartialss full tupartialssNormal
mkPgTotal :: IO ProgGenSF
mkPgTotal = mkPGXOpts mkTrieOptSFIO options{tv1=True,nrands=repeat 20,timeout=Just 20000} (eqs++ords) [] full []

mkDebugPg :: IO ProgGenSF
mkDebugPg = mkPGXOpts mkTrieOptSFIO options{tv1=True,nrands=repeat 20,timeout=Just 20000} [] [] deb []

deb = [ $(p [| (reverse :: [a] -> [a], enumFromTo :: Int -> Int -> [Int], 1::Int, product :: [Int] -> Int, concatMap :: (a -> [b]) -> [a] -> [b]) |]), [],[]]

pgfullIO :: IO ProgGenSFIORef
pgfullIO = mkPGXOptIO options{tv1=True,nrands=repeat 20} (eqs++ords) clspartialss full tupartialssNormal
full = foldr zipAppend literals [fromPrelude, prelEqRelated, dataListEqRelated, prelOrdRelated, dataListOrdRelated, fromDataList, fromDataChar, fromDataMaybe]
clspartialss :: [(Primitive,Primitive)]
clspartialss = undefs
tupartialss, tupartialssNormal :: [[(Primitive,Primitive)]]
tupartialss
  = map (map (\[a,b] -> (a,b))) 
                  [ [], -- [$(p [|(reverse . drop 1 . reverse :: [a] -> [a], init :: [a] -> [a])|])], -- An unnatural value cannot be returned in this case due to the polymorphism, unless the Partial class is used.
                    [$(p [| (chr . (`mod` 65536) . abs, chr . abs) |]),
                     $(p [| (chr . (`mod` 65536) . succ . ord :: Char->Char, succ :: Char -> Char) |])],
                    [$(p [| ((\m n -> if n==0 then 83 else div m n) :: Int->Int->Int,     div :: Int->Int->Int) |]),
                     $(p [| ((\m n -> if n==0 then 46 else mod m n) :: Int->Int->Int,     mod :: Int->Int->Int) |]),
                     $(p [| ((\m n -> if n<0  then 23 else m ^ n)   :: Int->Int->Int,     (^) :: Int->Int->Int) |]),
                     $(p [| ((\l m n -> if l==m then [n,m,m,n,m,n,n]   else [l,m..n]) :: Int->Int->Int->[Int],     enumFromThenTo :: Int->Int->Int->[Int]) |]),
                     $(p [| ((\l m n -> if l==m then [m,n,n,m,n,n,n,m] else [l,m..n]) :: Char->Char->Char->[Char], enumFromThenTo :: Char->Char->Char->[Char]) |]),
                     $(p [| (chr . (`mod` 65536) . pred . ord :: Char->Char, pred :: Char -> Char) |])
                    ] ]
-- tupartialssNormal is a variant of tupartialss, which make total functions from partial functions by making the latter return `natural' values for error cases.
-- Returning natural values is good if MagicHaskeller.fpartial try total versions after failures of partial versions, and currently that is the case.
tupartialssNormal
  = map (map (\[a,b] -> (a,b))) 
                  [ [], -- [$(p [|(reverse . drop 1 . reverse :: [a] -> [a], init :: [a] -> [a])|])], 
                    [$(p [| (chr . (`mod` 65536) . abs, chr . abs) |]),
                     $(p [| (chr . (`mod` 65536) . succ . ord :: Char->Char, succ :: Char -> Char) |])],
                    [$(p [| ((\m n -> if n==0 then 0 else div m n) :: Int->Int->Int,     div :: Int->Int->Int) |]),
                     $(p [| ((\m n -> if n==0 then 0 else mod m n) :: Int->Int->Int,     mod :: Int->Int->Int) |]),
                     $(p [| ((\m n -> if m==0 then 0 else m ^ n)   :: Int->Int->Int,     (^) :: Int->Int->Int) |]),
                     $(p [| ((\l m n -> if l==m then [] else [l,m..n]) :: Int->Int->Int->[Int],     enumFromThenTo :: Int->Int->Int->[Int]) |]),
                     $(p [| ((\l m n -> if l==m then [] else [l,m..n]) :: Char->Char->Char->[Char], enumFromThenTo :: Char->Char->Char->[Char]) |]),
                     $(p [| (chr . (`mod` 65536) . pred . ord :: Char->Char, pred :: Char -> Char) |])
                     ] ]

literals = [$(p [|(1::Int, 2::Int, 3::Int, ' '::Char)|]), [], []]
fromPrelude = [ -- prelPartial ++
               soso ++ $(p [| (null :: (->) [a] Bool, -- Without this, null is synthesized as all (\_ -> False).
                               abs  :: (->) Int Int, -- compare :: Char->Char->Ordering, compare :: Int->Int->Ordering, 
                               flip . flip foldl :: a -> (->) [b] ((a -> b -> a) -> a), 
                               foldr const :: a -> (->) [a] a, 
                               last' :: a -> [a] -> a,
                               reverse . drop 1 . reverse :: [a] -> [a],
                               enumFromTo :: Int->Int->[Int], enumFromTo :: Char->Char->[Char],
                               fmap :: (a -> b) -> (->) (Maybe a) (Maybe b),
                               flip (flip . either) :: (->) (Either a b) ((a -> c) -> (b -> c) -> c)) |])
               ++ intinst2 ++ $(p [| (sum :: (->) [Int] Int, product :: (->) [Int] Int) |]), 
               list2 ++ $(p [| (scanl :: (a -> b -> a) -> a -> [b] -> [a], scanr :: (a -> b -> b) -> b -> [a] -> [b], scanl1 :: (a -> a -> a) -> [a] -> [a], scanr1 :: (a -> a -> a) -> [a] -> [a],
               -- until ::  (a -> Bool) -> (a -> a) -> a -> a) を入れてたが，どうもuntilがあると急に遅くなる．その割に，全く使われない．何じゃらホイ
                show :: Int -> [Char]) |])++ $(p [| ((,) :: a -> b -> (a,b), flip uncurry :: (->) (a,b) ((a->b->c) -> c)) |]),
                $(p [| ((,,) :: a -> b -> c -> (a,b,c), Left :: a -> Either a b, Right :: b -> Either a b,
                                    zip  :: (->) [a] ((->) [b] [(a, b)]),
                                    zip3 :: (->) [a] ((->) [b] ((->) [c] [(a, b, c)])),
                                    unzip  :: (->) [(a, b)]    ([a], [b]),
                                    unzip3 :: (->) [(a, b, c)] ([a], [b], [c]),
                                    odd :: Int -> Bool, even :: Int -> Bool) |])
              ] -- My version of enumFromThenTo is used. The problem of the library version is that enumFromThenTo 1 1 2 is infinite.
fromDataList = [$(p [| (sortBy, nubBy, deleteBy, dropWhileEnd, transpose -- , stripPrefix :: [Char]->[Char]->Maybe [Char],
                       )|]),
                $(p [| (
                       find :: (a -> Bool) -> [a] -> Maybe a, flip findIndex :: (->) [a] ((a -> Bool) -> Maybe Int), flip findIndices :: (->) [a] ((a -> Bool) -> [Int]), deleteFirstsBy, unionBy :: (a -> a -> Bool) -> (->) [a] ([a] -> [a]), intersectBy :: (a -> a -> Bool) -> (->) [a] ([a] -> [a]), groupBy, insertBy -- , maximumBy, minimumBy
                       ) |]),
                $(p [| (intersperse, subsequences, permutations,
                       inits, tails,                                
                       flip . flip mapAccumL :: acc -> (->) [x] ((acc -> x -> (acc, y)) -> (acc, [y])),
                       flip . flip mapAccumR :: acc -> (->) [x] ((acc -> x -> (acc, y)) -> (acc, [y]))

                       -- , isPrefixOf :: [Char] -> [Char] -> Bool, isSuffixOf :: [Char] -> [Char] -> Bool, isInfixOf :: [Char] -> [Char] -> Bool
                       ) |])]
fromDataChar = [$(p [| (toUpper :: (->) Char Char, toLower :: (->) Char Char) |])++
                $(p [| (ord, isControl :: (->) Char Bool, isSpace :: (->) Char Bool, isLower :: (->) Char Bool, isUpper :: (->) Char Bool, isAlpha :: (->) Char Bool, isAlphaNum :: (->) Char Bool, isDigit :: (->) Char Bool, isSymbol :: (->) Char Bool, isPunctuation :: (->) Char Bool, isPrint :: (->) Char Bool) |]),
                $(p [| (isOctDigit :: (->) Char Bool, isHexDigit :: (->) Char Bool) |]), 
                []]
fromDataMaybe = [[],
                 $(p [| (catMaybes, listToMaybe :: (->) [a] (Maybe a), maybeToList :: (->) (Maybe a) [a]) |]),
                 []]
                -- mapMaybe f = catMaybes . map f

pgWithDoubleRatio :: ProgGenSF
pgWithDoubleRatio = mkPGXOpt options{tv1=True,nrands=repeat 20,timeout=Just 100000} (eqs++ords++doubleCls++ratioCls) clspartialss withDoubleRatio tupartialssNormal
pgWithDoubleRatios :: [ProgGenSF]
pgWithDoubleRatios = map pgWithDoubleRatioSized [0..]
  where pgWithDoubleRatioSized sz = mkPGXOpt options{memoCondPure = \t d -> size t < sz && 0<d {- && d<7 -}, tv1=True,nrands=repeat 20,timeout=Just 100000} (eqs++ords++doubleCls++ratioCls) clspartialss withDoubleRatio tupartialssNormal

withDoubleRatio = zipWith (++) withRatio fromPrelDouble

pgWithRatio :: ProgGenSF
pgWithRatio = mkPGXOpt options{tv1=True,nrands=repeat 20,timeout=Just 100000} (eqs++ords++ratioCls) clspartialss withRatio tupartialssNormal
pgWithRatios :: [ProgGenSF]
pgWithRatios = map pgWithRatioSized [0..]
  where pgWithRatioSized sz = mkPGXOpt options{memoCondPure = \t d -> size t < sz && 0<d {- && d<7 -}, tv1=True,nrands=repeat 20,timeout=Just 100000} (eqs++ords++ratioCls) clspartialss withRatio tupartialssNormal

-- pgRatio and pgRatios are currently for debugging, but there may be other uses.
pgRatio :: ProgGenSF
pgRatio = mkPGXOpt options{tv1=True,nrands=repeat 20,timeout=Just 100000} ratioCls [] (zipWith (++) fromPrelRatio fromDataRatio) [[],[],[]]
pgRatios :: [ProgGenSF]
pgRatios = map pgWithRatioSized [0..]
  where pgWithRatioSized sz = mkPGXOpt options{memoCondPure = \t d -> size t < sz && 0<d {- && d<7 -}, tv1=True,nrands=repeat 20,timeout=Just 100000} ratioCls []  (zipWith (++) fromPrelRatio fromDataRatio) [[],[],[]]

withRatio = foldr (zipWith (++)) full [fromPrelRatio, fromDataRatio]

ratioCls = $(p [| (eq :: Equivalence (Ratio Int), cmp :: Ordered (Ratio Int)) |])
fromPrelRatio = [ $(p [| (1      :: Ratio Int, 
                          10     :: Ratio Int,
                          100     :: Ratio Int,
                          1000     :: Ratio Int,
                          succ   :: Ratio Int -> Ratio Int,
                          negate :: Ratio Int -> Ratio Int,
                          abs    :: Ratio Int -> Ratio Int,
                          sum    :: (->) [Ratio Int] (Ratio Int),
                          product :: (->) [Ratio Int] (Ratio Int),
                          (+) :: Ratio Int -> Ratio Int -> Ratio Int,
                          (-) :: Ratio Int -> Ratio Int -> Ratio Int,
                          (*) :: Ratio Int -> Ratio Int -> Ratio Int,
                          (/) :: Ratio Int -> Ratio Int -> Ratio Int,
                          fromIntegral :: Int -> Ratio Int,
                          properFraction :: (->) (Ratio Int) (Int, Ratio Int),
                          round   :: (->) (Ratio Int) Int,
                          floor   :: (->) (Ratio Int) Int,
                          ceiling :: (->) (Ratio Int) Int,
                          (^^) :: Ratio Int -> Int -> Ratio Int) |]),
                  [],
                  [] ]
fromDataRatio = [  
                  $(p [| ((%)  :: Int -> Int -> Ratio Int,
                          numerator   :: (->) (Ratio Int) Int,
                          denominator :: (->) (Ratio Int) Int) |]),                                            
                  [], [] ]

pgWithDouble :: ProgGenSF
pgWithDouble = mkPGXOpt options{tv1=True,nrands=repeat 20,timeout=Just 100000} (eqs++ords++doubleCls) clspartialss withDouble tupartialssNormal
pgWithDoubles :: [ProgGenSF]
pgWithDoubles = map pgWithDoubleSized [0..]
  where pgWithDoubleSized sz = mkPGXOpt options{memoCondPure = \t d -> size t < sz && 0<d {- && d<7 -}, tv1=True,nrands=repeat 20,timeout=Just 100000} (eqs++ords++doubleCls) clspartialss withDouble tupartialssNormal

mkPgWithDouble :: IO ProgGenSF
mkPgWithDouble = mkPGXOpts mkTrieOptSFIO options{tv1=True,nrands=repeat 20,timeout=Just 100000} (eqs++ords++doubleCls) clspartialss withDouble tupartialssNormal

withDouble = zipWith (++) full fromPrelDouble

doubleCls = $(p [| ( -- eq :: Equivalence Double,
                    cmp :: Ordered Double) |])
fromPrelDouble= [ $(p [| (1      :: Double, 
                          10     :: Double,
                          100     :: Double,
                          1000     :: Double,
                          succ   :: Double -> Double,
                          negate :: Double -> Double,
                          abs    :: Double -> Double,
                          signum :: Double -> Double,
                          recip  :: Double -> Double,
                          sum    :: (->) [Double] Double,
                          product :: (->) [Double] Double,
                          (+) :: Double -> Double -> Double,
                          (-) :: Double -> Double -> Double,
                          (*) :: Double -> Double -> Double,
                          (/) :: Double -> Double -> Double,
                          fromIntegral :: Int -> Double,
                          properFraction :: (->) Double (Int, Double),
                          round   :: (->) Double Int,
                          floor   :: (->) Double Int,
                          ceiling :: (->) Double Int,
                          truncate :: (->) Double Int,
                          (^^) :: Double -> Int -> Double,
                          pi :: Double
                          ) |]),
                  $(p [| (          
                          exp :: Double -> Double,
                          log :: Double -> Double,
                          sqrt :: Double -> Double,
                          (**) :: Double -> Double -> Double,
                          logBase :: Double -> Double -> Double,
                          sin :: Double -> Double,
                          cos :: Double -> Double,
                          tan :: Double -> Double,
                          asin :: Double -> Double,
                          acos :: Double -> Double,
                          atan :: Double -> Double,
                          sinh :: Double -> Double,
                          cosh :: Double -> Double,
                          tanh :: Double -> Double,
                          asinh :: Double -> Double,
                          acosh :: Double -> Double,
                          atanh :: Double -> Double,
                          floatDigits :: Double -> Int,
                          exponent :: Double -> Int,
                          significand :: Double -> Double,
                          scaleFloat :: Int -> Double -> Double,
                          atan2 :: Double -> Double -> Double
                         ) |]),
                  [] ]
