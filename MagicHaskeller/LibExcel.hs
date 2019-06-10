-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE TemplateHaskell, NoMonomorphismRestriction, PatternGuards, CPP #-}
module MagicHaskeller.LibExcel(module MagicHaskeller.LibExcel, module MagicHaskeller.LibExcelStaged) where

import MagicHaskeller
import MagicHaskeller.LibExcelStaged
import MagicHaskeller.Types(size)
import Control.Monad(liftM2)
import Data.List
import Data.Char
import Data.Maybe
-- import Data.Ratio
import MagicHaskeller.FastRatio
import qualified Data.Generics as G

import MagicHaskeller.ProgGenSF(mkTrieOptSFIO)

import qualified Data.IntMap as IM
-- import Data.Hashable

-- whether succ is used only for numbers or not
succOnlyForNumbers = True -- This is True for Excel.

-- total variants of prelude functions
last' = (\x xs -> last (x:xs))

-- init xs = zipWith const xs (drop 1 xs)


-- | 'ppExcel' replaces uncommon functions like catamorphisms with well-known functions.
ppExcel :: Exp -> Exp
ppExcel (AppE (AppE (AppE (AppE (AppE (AppE (VarE name) e1) e2) e3) e4) e5) e6) | Just stem <- stripPrefix "6'" $ reverse nb = mkUncurried (reverse stem) (map ppExcel [e1, e2, e3, e4, e5, e6])
  where nb = nameBase name
ppExcel (AppE (AppE (AppE (AppE (AppE (VarE name) e1) e2) e3) e4) e5) | Just stem <- stripPrefix "5'" $ reverse nb = mkUncurried (reverse stem) (map ppExcel [e1, e2, e3, e4, e5])
  where nb = nameBase name
ppExcel (AppE (AppE (AppE (InfixE (Just e1) (VarE name) (Just e2)) e3) e4) e5) | nameBase name == "." = ppExcel $ ((e1 `AppE` (e2 `AppE` e3)) `AppE` e4) `AppE` e5   -- ad hoc pattern:S
ppExcel (AppE (AppE (InfixE (Just e1) (VarE name) (Just e2)) e3) e4) | nameBase name == "." = ppExcel $ (e1 `AppE` (e2 `AppE` e3)) `AppE` e4
ppExcel (AppE (AppE (AppE (AppE (ConE name) e1) e2) e3) e4) | nameBase name == "(,,,)" = ppExcel $ TupE [e1, e2, e3, e4]
ppExcel (AppE (AppE (AppE (AppE (VarE name) e1) e2) e3) e4) | nb == "flip"             = ppExcel $ ((e1 `AppE` e3) `AppE` e2) `AppE` e4
                                                            | nb == "sUBST4"           = mkUncurried "sUBSTITUTE" (map ppExcel [e1, e2, e3, mkVarOp lit1 "+" (absE `AppE` e4)])
                                                            | Just stem <- stripPrefix "4'" $ reverse nb = mkUncurried (reverse stem) (map ppExcel [e1, e2, e3, e4])
  where nb = nameBase name
ppExcel (AppE (InfixE (Just e1) (VarE name) (Just e2)) e3) | nameBase name == "." = ppExcel $ e1 `AppE` (e2 `AppE` e3)
ppExcel (AppE (e@(AppE (AppE (ConE name) p) t)) f) | nameBase name == "(,,)" = ppExcel $ TupE [p,t,f]
ppExcel (AppE (e@(AppE (AppE (VarE name) p) t)) f)
    = case reverse $ nameBase name of
        "xIdnif"      -> mkVarOp (mkUncurried "finD" [char7, mkUncurried "sUBSTITUTE" [mkUncurried "concatenate" [ppp,ppt], ppp, char7, ppExcel $ mkVarOp lit1 "+" (absE `AppE` f) ]]) "-" lit1   -- The "findIx" case.  findIx c xs n = finD(char(7), sUBSTITUTE(concatenate(c,xs), c, char(7), 1+abs(n)))-1
        "pilf"        -> ppExcel $ (ppp `AppE` ppf) `AppE` ppt -- The "flip" case
        "."           -> ppExcel (p `AppE` (t `AppE` f))
        '3':'\'':stem -> ppExcel $ mkUncurried (reverse stem) [p,t,f]
        _             -> ppExcel e `AppE` ppf
  where ppp = ppExcel p
        ppt = ppExcel t
        ppf = ppExcel f
ppExcel (AppE f@(AppE (ConE name) lj) e) | nameBase name == "(,)" = ppExcel $ TupE [lj, e]
ppExcel (AppE (AppE (VarE name) e1) e2) | nb == "fLOOR0" = case ppe2 of LitE (IntegerL n) | n>0 -> floore1e2
                                                                                          | otherwise -> lit0
                                                                        LitE (RationalL n) | n>0 -> floore1e2
                                                                                           | otherwise -> lit0
                                                                        AppE (VarE nm) _  | nameBase nm == "pI" -> floore1e2 -- just to avoid the awkward case of iF(pI() > 0, blah)
                                                                        _                  -> mkIF (mkVarOp ppe2 ">" lit0) floore1e2 lit0
                                        | nb == "countStr" = case ppe2 of LitE (StringL "") -> lit0
                                                                          LitE (StringL _)  -> counted
                                                                          ListE []          -> lit0
                                                                          ListE _           -> counted
                                                                          _                 -> mkIF (mkVarOp ppe2 "<>" (LitE $ StringL "")) counted lit0
                                        | nb == "dropLeft" = mkUncurried "right" [ppe1, mkVarOp (ppExcel $ lenE `AppE` ppe1) "-" ppe2]
                                        | Just stem <- stripPrefix "2'" $ reverse nb = ppExcel $ mkUncurried (reverse stem) [e1, e2]
  where nb = nameBase name
        ppe1 = ppExcel e1
        ppe2 = ppExcel e2
        counted = ppExcel $ mkVarOp (mkVarOp (lenE `AppE` e1) "-" (lenE `AppE` (mkSUBST4 [e1, ppe2, LitE (StringL "")]))) "/" (lenE `AppE` ppe2) -- countStr x str = (len(x)-len(sUBsTITUTE(x,str,""))) / len(str)
        floore1e2 = mkUncurried "fLOOR" [ppe1, ppe2]
ppExcel (AppE (InfixE m@(Just _) op Nothing)    e) = ppExcel (InfixE m        op (Just e))
ppExcel (AppE (InfixE Nothing    op m@(Just _)) e) = ppExcel (InfixE (Just e) op m)
ppExcel (AppE v@(VarE name) e)
    = case nameBase name of
        "negate" -> case ppe of LitE (IntegerL i)        -> LitE $ IntegerL $ (-i)
                                LitE (RationalL r)       -> LitE $ RationalL $ (-r)
                                _                        -> mkVarOp (LitE $ IntegerL 0) "-" ppe -- @negate x@ should become @0 - x@
        "abs"    -> case ppe of LitE (IntegerL i)        -> LitE $ IntegerL $ abs i
                                LitE (RationalL r)       -> LitE $ RationalL $ abs r
                                ParensE _                -> AppE (ppv v) ppe
                                _                        -> AppE (ppv v) $ ParensE ppe
        "floor"  -> ppe
        "fromIntegral" -> ppe
        "succ"   -> case ppe of
                      LitE (IntegerL i)        -> LitE $ IntegerL $ succ i
                      LitE (RationalL r)       -> LitE $ RationalL $ succ r
                      LitE (CharL c)           -> LitE $ CharL $ succ c
                      InfixE (Just (LitE (IntegerL n))) (VarE nm) (Just e)
                        | nameBase nm == "+"    -> mkVarOp (LitE $ IntegerL $ succ n) "+" e
                      AppE (VarE nm) e
                        | succOnlyForNumbers &&
                          nameBase nm == "succ" -> mkVarOp (LitE $ IntegerL 2) "+" e -- This is OK, if we use succ only for numbers.
                      _                       -> AppE (ppv v) ppe
        "left1" -> case ppe of
                       LitE (StringL xs)        -> LitE $ StringL $ take 1 xs
                       ListE es                 -> ListE $ take 1 $ map ppExcel es
                       ArithSeqE (FromToR (LitE (IntegerL f)) (LitE (IntegerL t))) -> ListE [LitE $ IntegerL f]
                       AppE (VarE name) e' | nameBase name == "left1" -> ppe
                       _         -> AppE leftE $ TupE [ppe, LitE $ IntegerL 1]
        "right1" -> case ppe of
                       LitE (StringL xs)        -> LitE $ StringL $ right(xs,1)
                       ListE es                 -> ListE $ right(map ppExcel es, 1)
                       AppE (VarE name) e' | nameBase name == "right1" -> ppe
                       _         -> AppE rightE $ TupE [ppe, LitE $ IntegerL 1]
        "reverse" -> case ppe of
                       LitE (StringL xs)        -> LitE $ StringL $ reverse xs
                       ListE es                 -> ListE $ reverse $ map ppExcel es
                       ArithSeqE (FromToR (LitE (IntegerL f)) (LitE (IntegerL t))) -> ArithSeqE $ FromThenToR (LitE $ IntegerL t) (LitE $ IntegerL $ t-1) (LitE $ IntegerL f)
                       AppE (VarE name) e' | nameBase name == "reverse" -> e'
                       _         -> AppE reverseE ppe
        "len" -> case ppe of
                       LitE (StringL xs)        -> LitE $ IntegerL $ toInteger $ length xs
                       ListE es                -> LitE $ IntegerL $ toInteger $ length es
                       ArithSeqE (FromToR (LitE (IntegerL f)) (LitE (IntegerL t))) -> LitE $ IntegerL $ t - f + 1 -- can be bottom, if t is less than f.
                       AppE (VarE name) e' | nameBase name == "reverse" -> AppE lenE e' -- length . reverse => length
                       -- There can also be the length . map f => length rule. The length . map f pattern can appear when f includes some absent argument.
                       ParensE _ -> AppE lenE ppe
                       _         -> AppE lenE (ParensE ppe)
        "sum"    -> case ppe of
                       AppE (VarE name) e' | nameBase name == "reverse" -> AppE sumE e'
                       _         -> AppE sumE ppe
        "product" -> case ppe of
                       AppE (VarE name) e' | nameBase name == "reverse" -> AppE productE e'
                       _         -> AppE productE ppe
        nb       -> case ppe of 
                       TupE _                            -> AppE (ppv v) ppe
                       ConE name | nameBase name == "()" -> AppE (ppv v) ppe
                       _                                 -> AppE (ppv v) (ParensE ppe)
  where ppe = ppExcel e 
-- The following pattern is actually unnecessary if only eta-long normal expressions will be generated.
ppExcel e@(VarE _)          = ppv e
ppExcel e@(ConE _)          = ppv e
ppExcel (AppE f x)          = case ppx of
                                    TupE _ -> ppExcel f `AppE` ppx
                                    _      -> ppExcel f `AppE` ParensE ppx
  where ppx = ppExcel x
ppExcel (InfixE me1 op me2)
  = let j1 = fmap ppExcel me1
        j2 = fmap ppExcel me2
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
                       (Just e, Just (LitE (IntegerL 1)))
                                        | nameBase opname `elem` ["/","*"] -> e
                       _ -> theDefault
                   where theDefault = InfixE j1 (VarE $ ppopn opname) j2

ppExcel (LamE pats e)       = LamE pats (ppExcel e)

ppExcel (TupE es)           = TupE (map ppExcel es)
ppExcel (ListE es)          = ListE (map ppExcel es)
ppExcel (SigE e ty)         = ppExcel e `SigE` ty
ppExcel e = e


{-
ppv e@(VarE name) | nameBase name `elem` ["iF", "nat_cata"] = LamE [ VarP n | n <- names ] (ppExcel (AppE (AppE (AppE e p) t) f))
                  | nameBase name == "last'"                = LamE [ VarP n | n <- tail names ] (ppExcel (AppE (AppE e t) f))
                  | otherwise                               = VarE $ ppopn name
    where names   = [ mkName [n] | n <- "ptf" ]
          [p,t,f] = map VarE names
-}
ppv (VarE name) = VarE $ ppopn name 
ppv (ConE name) = ConE $ ppopn name 
ppopn name = mkName $ nameBase name



ppdrop m0j e 
  = case ppExcel e of
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
leftE = VarE $ mkName "left"
rightE = VarE $ mkName "right"
lenE   = VarE $ mkName "len"
absE   = VarE $ mkName "abs"

mkIF p t f  = VarE (mkName "iF")  `AppE` TupE [p, t, f]
mkUncurried str es = VarE (mkName str) `AppE` TupE es
mkSUBST4 = mkUncurried "sUBSTITUTE"
mkVarOp e1 op e2 = InfixE (Just e1) (VarE $ mkName op) (Just e2)

char7 = VarE (mkName "char") `AppE` LitE (IntegerL 7)
lit0  = LitE (IntegerL 0)
lit1  = LitE (IntegerL 1)

procSucc n (AppE (VarE name) e) | nameBase name == "succ" = procSucc (n+1) e
procSucc n (LitE (CharL c))     = LitE $ CharL $ iterate succ c `genericIndex` n
procSucc n (LitE (IntegerL i))  = LitE $ IntegerL $ n+i
procSucc n (LitE (RationalL r)) = LitE $ RationalL $ fromInteger n + r
procSucc n e | succOnlyForNumbers = InfixE (Just $ LitE $ IntegerL n) (VarE $ mkName "+") (Just $ ppExcel e) -- This is OK, if we use succ only for numbers.
             | otherwise          = iterate (AppE (VarE $ mkName "succ")) (ppExcel e) `genericIndex` n



nrnds = repeat 5



mkPgExcel :: IO ProgGenSF
mkPgExcel = mkPGXOpts mkTrieOptSFIO options{tv0=True,nrands=repeat 20,timeout=Just 100000} [] [] excel [[],[],[]]
mkPgExcels :: Int -> IO ProgGenSF
mkPgExcels sz = mkPGXOpts mkTrieOptSFIO options{memoCondPure = \t d -> size t < sz && 0<d {- && d<7 -}, tv0=True,nrands=repeat 20,timeout=Just 100000} [] [] excel [[],[],[]]

(<>) = (/=)

-- doubleCls = $(p [| (eq :: Equivalence Double) |])

excel = [$(p [| (" " :: [Char], "," :: [Char], "-" :: [Char], 
                 fromIntegral :: Int -> Double, floor :: Double -> Int, -- These two are hidden by ppExcel.
                 0::Int, 1::Int, (1+)::Int->Int, 3::Int,
                 0::Double, 1::Double, -- (1+)::Double->Double, 
                 (<) :: Int -> Int -> Bool, (<=) :: Int -> Int -> Bool, (<>) :: Int -> Int -> Bool, 
                 (<) :: Double -> Double -> Bool, -- (<=) :: Double -> Double -> Bool, (<>) :: Double -> Double -> Bool, 
                 (<>) :: [Char] -> [Char] -> Bool, 
                 not :: (->) Bool Bool, True :: Bool, False :: Bool, aND'2 :: (->) Bool ((->) Bool Bool), oR'2 :: (->) Bool ((->) Bool Bool), iF'3 :: (->) Bool (a -> a -> a),
                 (,) :: a -> b -> (a,b), (,,) :: a -> b -> c -> (a,b,c), (,,,) :: a -> b -> c -> d -> (a,b,c,d)) |])
         ++ $(p [| (
                                            upper::[Char]->[Char],                                             
                                            lower::[Char]->[Char],
                                            proper::[Char]->[Char],
                                            left1 :: [Char] -> [Char],
                                            right1 :: [Char] -> [Char],
                                            left'2 :: [Char] -> Int -> [Char],
                                            right'2 :: [Char] -> Int -> [Char],
                                            dropLeft :: [Char] -> Int -> [Char],
                                            mid'3 :: [Char] -> Int -> Int -> [Char],
                                            len :: (->) [Char] Int,
                                            concatenate'2 :: (->) [Char] ([Char] -> [Char]),
                                            concatenatE'3 :: (->) [Char] ([Char] -> [Char] -> [Char]),
                                            concatenaTE'4 :: (->) [Char] ([Char] -> [Char] -> [Char] -> [Char]),
                                            concatenATE'5 :: (->) [Char] ([Char] -> [Char] -> [Char] -> [Char] -> [Char]),
                                            concateNATE'6 :: (->) [Char] ([Char] -> [Char] -> [Char] -> [Char] -> [Char] -> [Char]),
                                            {-
                                            sum :: [Double] -> Double,
                                            product :: [Double] -> Double,
                                            max :: [Double] -> Double,
                                            min :: [Double] -> Double,
                                            average :: [Double] -> Double,
                                            count :: [Double] -> Double,
                                            sumif :: [Maybe Double] -> Double,
-}
                                            flip cEILING'2 . abs :: Double -> (->) Double Double,
                                            fLOOR0   :: (->) Double (Double -> Double),
                                            rOUND'2   :: (->) Double (Int -> Double),
                                            roundup'2 :: (->) Double (Int -> Double),
                                            rounddown'2 :: (->) Double (Int -> Double),
                                            trim::[Char]->[Char],
                                            fIND'3 :: [Char] -> [Char] -> Int -> Maybe Int,
                                            ifERROR'2 :: Maybe a -> a -> a,
                                            fact   :: Int -> Maybe Int,
                                            combin'2 :: Int -> Int -> Maybe Int, 
                                            mOD'2    :: Int -> Int -> Maybe Int,
                                            degrees :: Double -> Double,
                                            radians :: Double -> Double,
                                            findIx  :: [Char] -> [Char] -> Int -> Int,
                                            sUBsTITUTE'3 :: [Char] -> [Char] -> [Char] -> [Char],
                                            sUBST4 :: [Char] -> [Char] -> [Char] -> Int -> [Char],
                                            countStr :: [Char] -> [Char] -> Int,
                          negate :: Int -> Int,
                          abs    :: Int -> Int,
                          (+) :: (->) Int ((->) Int Int),
                          (-) :: Int -> Int -> Int,
                          (*) :: Int -> Int -> Int,
                          10     :: Double,
                          100     :: Double,
                          1000     :: Double,
                          negate :: Double -> Double,
                          abs    :: Double -> Double,
                          sign :: Double -> Double,
--                          recip  :: Double -> Double,  -- (1/) だけど、まあ(/)と1で作れるし、いらんやろ。
                          (+) :: (->) Double ((->) Double Double),
                          (-) :: Double -> Double -> Double,
                          (*) :: Double -> Double -> Double,
                          (/) :: Double -> Double -> Double, -- 本当はエラー処理すべし。
--                          fromIntegral :: Int -> Double,
                          pI () :: Double
                          ) |]),
                  $(p [| (          
                          exp :: Double -> Double,
                          ln  :: Double -> Maybe Double,
                          sQRT :: Double -> Maybe Double,
                          power'2 :: Double -> Double -> Maybe Double,
                          lOG'2 :: Double -> Double -> Maybe Double,
                          sin :: Double -> Double,
                          cos :: Double -> Double,
                          tan :: Double -> Double,
                          asin :: Double -> Double, -- この辺もエラー処理せんと。
                          acos :: Double -> Double,
                          atan :: Double -> Double,
                          sinh :: Double -> Double,
                          cosh :: Double -> Double,
                          tanh :: Double -> Double,
                          asinh :: Double -> Double,
                          acosh :: Double -> Double,
                          atanh :: Double -> Double,
            --              floatDigits :: Double -> Int,
              --            exponent :: Double -> Int,
                --          significand :: Double -> Double,
                  --        scaleFloat :: Int -> Double -> Double,
                          aTAN2'2 :: Double -> Double -> Double
                         ) |]),
                  [] ]
