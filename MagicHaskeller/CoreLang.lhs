-- 
-- (c) Susumu Katayama
--
CoreLang.lhs
extracted haskell-src-free stuff that can be used with Hat.
(This looks like Bindging.hs....)

\begin{code}
{-# LANGUAGE CPP, ExistentialQuantification, RankNTypes, TemplateHaskell #-}
-- workaround Haddock invoked from Cabal unnecessarily chasing imports. (If cpp fails, haddock ignores the remaining part of the module.)
#ifndef __GLASGOW_HASKELL__
-- x #hoge
#endif


module MagicHaskeller.CoreLang where
import Language.Haskell.TH
import Data.Array

import Debug.Trace

import qualified MagicHaskeller.PolyDynamic as PD
-- import MagicHaskeller.MyDynamic

import Data.Char(chr,ord,isDigit)
import MagicHaskeller.TyConLib
import MagicHaskeller.ReadTHType(thTypeToType)
#ifdef FORCE
import Control.Parallel.Strategies
#endif
-- required to make sure expressions are ready, so we can measure the exact time consumed to execute the expressions before time out.

import Data.Bits

import Data.Function(fix)

import Data.Int
import Data.Word
import Data.List(genericLength, genericIndex)

infixl :$

type Var = Int16

data CoreExpr = S | K | I | B | C | S' | B' | C' | Y
                | Lambda CoreExpr | X {-# UNPACK #-} !Int8 -- de Bruijn notation
--                | Lambda CoreExpr | X Int8 -- de Bruijn notation
                | FunLambda CoreExpr | FunX Int8 -- different system of de Bruijn notation for functions, used by IOPairs.hs
                | Tuple {-# UNPACK #-} !Int8
--                | Tuple Int8
{-                
                | Primitive Int 
                            Bool   -- True if the primitive is a constructor expression
-}
                | Primitive {primId :: {-# UNPACK #-} !Var}  -- (This should be Var instead of Int8 because the number space is being exhausted!)
                | PrimCon   {primId :: {-# UNPACK #-} !Var}  -- the primitive is a constructor expression
--                | Primitive {primId :: Var}  -- (This should be Var instead of Int8 because the number space is being exhausted!)
--                | PrimCon   {primId :: Var}  -- the primitive is a constructor expression
                | Context Dictionary
                | CoreExpr :$ CoreExpr
                | Case CoreExpr [(Var,Int8,CoreExpr)] -- the case expression. [(primitive ID of the constructor, arity of the constructor, rhs of ->)]
                | Fix  CoreExpr Int8 [Int8]            -- Fix expr n is === foldl (:$) (Y :$ FunLambda (napply n Lambda expr)) (map X is)
{-
                | FixCase       [(Int,Int,CoreExpr)] -- FixCase ts === (Y :$ Lambda (Lambda (Case (X 0) ts)))
                                                     -- See notes on July 3, 2010
-}
                | VarName String -- This is only used for pretty printing IOPairs.Expr. Use de Bruijn variables for other purposes.
                  deriving (Eq, Show, Ord)
newtype Dictionary = Dict {undict :: PD.Dynamic} deriving (Show)
instance Ord Dictionary where
    compare _ _ = EQ -- This should work for the current purposes, but can cause a bug.
instance Eq Dictionary where
    _ == _ = True -- This should work for the current purposes, but can cause a bug.

-- required to make sure expressions are ready, so we can measure the exact time consumed to execute the expressions before time out.
#ifdef FORCE
instance NFData CoreExpr where
    rnf (Lambda e) = rnf e
    rnf (X i)      = rnf i
    rnf (Tuple i)  = rnf i
    rnf (Primitive _) = () -- 最後のパターンにマッチするのでこれは要らなかったか．
    rnf (c :$ d)         = rnf c `seq` rnf d
    rnf e                = ()
#endif

arityCE :: CoreExpr -> Int
arityCE (Lambda e)    = 1 + arityCE e
arityCE (FunLambda e) = 1 + arityCE e
arityCE _             = 0

isAbsent :: Int -> CoreExpr -> Bool
isAbsent numArgs expr = isa (2^numArgs - 1) expr /= 0
isa :: Integer -> CoreExpr -> Integer
isa bits (X n) = clearBit bits $ fromIntegral n
isa bits (Lambda e) = isa (bits `unsafeShiftL` 1) e `unsafeShiftR` 1
isa bits (f :$ e )  = isa (isa bits f) e
isa bits Primitive{} = bits
isa bits PrimCon{}   = bits
isa bits Context{}   = bits
{- unused due to inefficiency
ceToInteger (Lambda e)    = ceToInteger e -- 型が変わっちゃうのでLambdaは無視できるはず．...  といいつつ自信無．July 24, 2008のnotesを参照. ま，hashには使えるという程度のつもり．
ceToInteger (f :$ e)      = 3 * (ceToInteger f `interleave` ceToInteger e)
ceToInteger (X n)         = 3 * toInteger n + 1
ceToInteger (Primitive n _) = 3 * toInteger n + 2

0 `interleave` 0 = 0
i `interleave` j = (j `interleave` (i `shiftR` 1)) * 2 + (i `mod` 2)
-- IntegerでなくIntを使う場合，算術右シフトshiftRでなく論理右シフトを使う必要がある...のはいいけど，なぜライブラリに論理右シフトがない?
logShiftR1 n = (n `clearBit` 0) `rotateR` 1 
-}
#if __GLASGOW_HASKELL__ < 710
instance Ord Exp where
    compare (VarE n0) (VarE n1) = n0 `compare` n1
    compare (VarE n0) _         = LT
    compare (ConE n0) (VarE n1) = GT
    compare (ConE n0) (ConE n1) = n0 `compare` n1
    compare (ConE n0) _         = LT
    compare (AppE _ _) (VarE _) = GT
    compare (AppE _ _) (ConE _) = GT
    compare (AppE e0 f0) (AppE e1 f1) = case compare e0 e1 of EQ -> compare f0 f1
                                                              c  -> c
    compare (AppE _ _) _        = LT

    compare a b = show a `compare` show b -- 超遅そう....
#endif
instance Read Exp where
    readsPrec _ str = [(error "ReadS Exp is not implemented yet", str)]


type VarLib = Array Var PD.Dynamic
type VarPriorityLib = Array Var Int

actualVarName :: String -> Exp
actualVarName = VarE . mkName . stripByd_
stripByd_ ('b':'y':d:'_':name) | isDigit d = name
stripByd_ ('-':'-':'#':name) = dropWhile (=='#') name
stripByd_ name = name

headIsX :: CoreExpr -> Bool
headIsX (Lambda e)    = headIsX e
headIsX (FunLambda e) = headIsX e
headIsX (f :$ e)      = headIsX f
headIsX (X _)         = True
headIsX (FunX _)      = True
headIsX _             = False

isAPrimitiveCombinator :: CoreExpr -> Bool
isAPrimitiveCombinator (Lambda e) = isAPrimitiveCombinator e
isAPrimitiveCombinator (FunLambda e) = isAPrimitiveCombinator e
isAPrimitiveCombinator (X _)      = True
isAPrimitiveCombinator (FunX _)   = True
isAPrimitiveCombinator (Primitive _) = False -- The meaning of "primitive" is different!
isAPrimitiveCombinator (PrimCon   _) = False
isAPrimitiveCombinator (Context   _) = False
isAPrimitiveCombinator (f :$ e)      = isAPrimitiveCombinator f && isAPrimitiveCombinator e
isAPrimitiveCombinator (Fix _ _ _)   = True
isAPrimitiveCombinator _             = True -- bothered. Anyway, there is no plan of using this function for analytical synthesis.

-- removeAbsents removes absent arguments.
removeAbsents :: CoreExpr -> CoreExpr
removeAbsents (Lambda e) = removeAbsents e
removeAbsents e
    = let args     = unboundXs 0 e :: Int
          newArity = popCount args
      in napply newArity Lambda $ adjustXs args 0 e
adjustXs args dep (Lambda e) = Lambda $ adjustXs args (dep+1) e
adjustXs args dep (X n) | diff >= 0 = X $ fromIntegral (popCount ((bit (fromIntegral diff) - 1) .&. args)) + dep
                          where diff = n - dep
adjustXs args dep (f :$ x)   = adjustXs args dep f :$ adjustXs args dep x
adjustXs _    _   e          = e

-- This is similar to isAbsent.
unboundXs dep (Lambda e)      = unboundXs (dep+1) e
unboundXs dep (X n) | diff>=0 = bit (fromIntegral diff) where diff = n-dep
unboundXs dep (f :$ e)        = unboundXs dep f .|. unboundXs dep e
unboundXs dep _               = 0


subexprs :: CoreExpr -> [CoreExpr]
subexprs e = sub 0 e
sub dep (Lambda e) = sub (succ dep) e
sub dep e          = napply dep Lambda e : concatMap (sub dep) (args e)

branches :: CoreExpr -> [CoreExpr]
branches e = bra 0 e
bra dep (Lambda e) = bra (succ dep) e
bra dep e@(_:$_)   = napply dep Lambda e : concatMap (bra dep) (args e)
bra _   _          = []

-- | 'parentsOfLeaves' collects branch nodes whose children are leaf nodes. This can be used for incremental learning.
parentsOfLeaves :: CoreExpr -> [CoreExpr]
parentsOfLeaves e | isALeaf e = []
                  | otherwise = pol 0 e
pol dep (Lambda e) = pol (succ dep) e
pol dep e = case filter (not . isALeaf) $ args e of []       -> [napply dep Lambda e]
                                                    branches -> concatMap (pol dep) branches
args (f :$ e) = e : args f
args _        = []

{-
-- \a b c -> f (\d e -> E) を \a b c -> f ((\a b c d e -> E) a b c)に．
mkRedundant :: CoreExpr -> CoreExpr
mkRedundant = mR 0 0
mR :: Int8 -> Int8 -> CoreExpr -> CoreExpr
mR dep fdep (Lambda e)    = Lambda $ mR (succ dep) fdep e
mR dep fdep (FunLambda e) = FunLambda $ mR dep (succ fdep) e
mR dep fdep (f :$ x)      = mR dep fdep f :$ foldl (:$) (napply dep Lambda $ napply fdep FunLambda $ mR dep fdep x) (map X [dep+fdep-1,dep+fdep-2..fdep] ++ map FunX [fdep-1,fdep-2..0])
--mR dep fdep (f :$ x)      = mR dep fdep f :$ foldl (:$) (napply dep Lambda $ napply fdep FunLambda $ mR dep fdep x) (map X [0..dep-1] ++ map FunX [dep..dep+fdep-1])
mR _   _    e             = e
-}

isALeaf :: CoreExpr -> Bool
isALeaf (Lambda e) = isALeaf e
isALeaf (_ :$ _)   = False
isALeaf _          = True

{-
skipLambdas dep (Lambda e)    = skipLambdas (dep+1) e
skipLambdas dep (FunLambda e) = skipLambdas (dep+1) e
skipLambdas dep e             = (dep,e)
-}


ceToPriority :: VarPriorityLib -> CoreExpr -> Int
ceToPriority vpl (Lambda e)    = ceToPriority vpl e
ceToPriority vpl (FunLambda e) = ceToPriority vpl e
ceToPriority vpl (f :$ x)      = 1 + ceToPriority vpl f + ceToPriority vpl x
ceToPriority _   (X _)         = 0
ceToPriority _   (FunX _)      = 0
ceToPriority vpl (Primitive i) = vpl ! i
ceToPriority vpl (PrimCon i)   = vpl ! i
ceToPriority vpl (Context dict)= 0



-- x 第1引数のplはArray Con Stringなんだけど，もう全部Primitiveを使うことになったので不要．
-- exprToTHExp converts CoreLang.CoreExpr into Language.Haskell.TH.Exp
exprToTHExp, exprToTHExpLite :: VarLib -> CoreExpr -> Exp
exprToTHExp vl e = exprToTHExp' True vl $ lightBeta e
exprToTHExpLite vl e = exprToTHExp' False vl $ lightBeta e
exprToTHExp' pretty vl e = x2hsx (fromIntegral $ ord 'a'-1 :: Int8) (fromIntegral $ ord 'a' -1) e
    where x2hsx :: Int8 -> Int8 -> CoreExpr -> Exp
          x2hsx dep fdep (Lambda e) = 
                       case x2hsx (dep+1) fdep e of LamE pvars expr -> LamE (pvar:pvars) expr
                                                    expr            -> LamE [pvar] expr
              where var  = mkName [chr $ fromIntegral (dep+1)]
                    pvar | not pretty || 0 `occursIn` e = VarP var
                         | otherwise                     = WildP
          x2hsx dep fdep (FunLambda e) = 
                       case x2hsx dep (fdep+1) e of LamE pvars expr -> LamE (pvar:pvars) expr
                                                    expr            -> LamE [pvar] expr
              where var  = mkName ['f', chr $ fromIntegral (fdep+1)]
                    pvar | not pretty || 0 `funOccursIn` e = VarP var
                         | otherwise                        = WildP
          x2hsx dep fdep (X n)            = VarE (mkName [chr $ fromIntegral (dep - n :: Int8)])         -- X nはX 0, X 1, ....
          x2hsx dep fdep (FunX n)            = VarE (mkName ['f', chr $ fromIntegral (fdep - n)])         -- X nはX 0, X 1, ....
--          x2hsx _   (Qualified con)  = VarE (mkName (pl ! con))
          x2hsx _   _    (Primitive n)  = x2hsxPrim n
          x2hsx _   _    (PrimCon   n)  = x2hsxPrim n
          x2hsx dep fdep (p@(Primitive _) :$ e :$ e0 :$ e1) | hdIsCxt e = x2hsxPrim3 dep fdep p e0 e1
          x2hsx dep fdep (p@(PrimCon   _) :$ e :$ e0 :$ e1) | hdIsCxt e = x2hsxPrim3 dep fdep p e0 e1 -- cannot happen currently, but maybe in future if negate and succ will become polymorphic and regarded as constructors.
          x2hsx dep fdep (p@(Primitive _) :$ e0 :$ e1) = x2hsxPrim3 dep fdep p e0 e1
          x2hsx dep fdep (p@(PrimCon   _) :$ e0 :$ e1) = x2hsxPrim3 dep fdep p e0 e1
          x2hsx dep fdep (Y :$ FunLambda e) = case x2hsx dep fdep (FunLambda e) of LamE [WildP]     expr -> expr
                                                                                   LamE (WildP:pvs) expr -> LamE pvs expr
                                                                                   expr                  -> VarE 'fix `AppE` expr
          -- This is still necessary because systematic synthesizer still uses Lambda and X even for functions.
          x2hsx dep fdep (Y :$ Lambda e) = case x2hsx dep fdep (Lambda e) of LamE [WildP]     expr -> expr
                                                                             LamE (WildP:pvs) expr -> LamE pvs expr
                                                                             expr                  -> VarE 'fix `AppE` expr
          x2hsx dep fdep (e0 :$ e1) | hdIsCxt e1 = x2hsx dep fdep e0
                                    | otherwise  = x2hsx dep fdep e0 `AppE` x2hsx dep fdep e1
          x2hsx dep fdep (Case ce ts)     = CaseE (x2hsx dep fdep ce) (map (tsToMatch dep fdep) ts)
--          x2hsx dep fdep (Fix ce n is)    = x2hsx dep fdep $ foldl (:$) (Y :$ FunLambda (napply n Lambda ce)) (map X is)          -- letを使って書いた方がいい感じになる．
          x2hsx dep fdep (Fix ce n is)
              = case x2hsx dep fdep (FunLambda (napply (fromIntegral n) Lambda ce)) of
                  LamE (WildP:ps) e -> foldl AppE (LamE ps e) $ map (x2hsx dep fdep . X) is


-- let のあと caseがある場合にさらにrefactorしてたのだが，
-- \a -> let fa (b@0) = 0
--           fa (b@succc) | succc > 0 = GHC.Enum.succ (GHC.Enum.succ (GHC.Enum.succ (fa c)))
--                  where c = succc - 1
--        in fa a
-- みたいなのができてめんどくさい．

-- てゆーか，pretty printしすぎると，ExecuteAPIするとき逆に遅そう．
                  LamE (VarP name : ps) (CaseE (VarE n) ms)
                      | VarP n `elem` ps -> LetE [FunD name (map (\(Match p b decls) -> Clause (map (replacePat n p) ps) b decls) ms)]
                                                  (foldl AppE (VarE name) $ map (x2hsx dep fdep . X) is)
                  LamE (VarP name : ps) e -> LetE [FunD name [Clause ps (NormalB e) []]]
                                                  (foldl AppE (VarE name) $ map (x2hsx dep fdep . X) is)
--          x2hsx dep (FixCase ts)     = x2hsx dep (Y :$ Lambda (Lambda (Case (X 0) ts)))
          x2hsx dep _ (VarName str) = VarE (mkName str)
          x2hsx _   _ Y                = VarE 'fix
          x2hsx _   _ K                = VarE 'const
          x2hsx _   _ B                = VarE '(.)
          x2hsx _   _ C                = VarE 'flip
          x2hsx _   _ S                = VarE $ mkName "ap"
          x2hsx _   _ I                = VarE 'id
          x2hsx _   _ S'               = VarE $ mkName "sprime"
          x2hsx _   _ B'               = VarE $ mkName "bprime"
          x2hsx _   _ C'               = VarE $ mkName "cprime"
          x2hsx _   _ e                = error ("exprToTHExp: converting " ++ show e)
          x2hsxPrim n = case PD.dynExp (vl ! n) of 
                                         ConE name -> ConE $ mkName $ nameBase name
                                         VarE name -> actualVarName $ nameBase name
                                         e -> e
          x2hsxPrim3 dep fdep p e0 e1
            | hdIsCxt e0 = x2hsx dep fdep (p :$ e1)
            | otherwise
              = let hsx0 = x2hsx dep fdep e0
                    hsx1 = x2hsx dep fdep e1
                    n    = primId p
                in case PD.dynExp (vl ! n) of 
                                      e@(VarE name) | head base `elem` "!@#$%&*+./<=>?\\^|-~"
                                                        -> InfixE (Just hsx0) (actualVarName base) (Just hsx1)
                                                    | otherwise -> (actualVarName base `AppE` hsx0) `AppE` hsx1
                                                    where base = nameBase name
                                      e@(ConE name) | namestr == ":"      -> case hsx1 of ListE hsxs                  -> ListE (hsx0 : hsxs)
                                                                                          ConE n | nameBase n == "[]" -> ListE [hsx0]
                                                                                          _                           -> InfixE (Just hsx0) (ConE $ mkName ":") (Just hsx1)
                                                    | head namestr == ':' -> InfixE (Just hsx0) (ConE $ mkName namestr) (Just hsx1)
                                                    | otherwise -> (ConE (mkName namestr) `AppE` hsx0) `AppE` hsx1
                                                    where 
                                                       namestr = nameBase name
                                      e             -> (e `AppE` hsx0) `AppE` hsx1

          hdIsCxt (Context{}) = True
          hdIsCxt (e :$ _)    = hdIsCxt e
          hdIsCxt _           = False
          replacePat name new (VarP o) | o==name   = AsP name new
          replacePat _    _   old      = old
          tsToMatch dep fdep (ctor, arity, expr)
              = case PD.dynExp (vl ! ctor) of
                  ConE name -> case x2hsx dep fdep (napply arint Lambda expr) of
                                 LamE pvars ex -> case compare (length pvars) arint of
                                                    LT -> error "too few lambda abstractions in Case...can't happen!"
                                                    EQ -> Match (mkPat nameb pvars) (NormalB ex) []
                                                    GT -> Match (mkPat nameb tk) (NormalB $ LamE dr ex) []
                                                                         where (tk,dr) = splitAt arint pvars
                                 ex -- -- | not pretty && nameb == "[]" -> Match (ConP '[] []) (NormalB ex) []
                                    | otherwise        -> Match (ConP (mkName nameb) []) (NormalB ex) []
                      where nameb = nameBase name
                            arint = fromIntegral arity
                            mkPat ":"     [pv1,pv2] = InfixP pv1 (mkName ":") pv2
                            mkPat (':':_) [pv1,pv2] = InfixP pv1 (mkName nameb) pv2
                            mkPat nmb     pvs       = ConP (mkName nameb) pvs
                  VarE name | nameBase name == "succ" ->
                                case x2hsx (dep+1) fdep expr of -- ここのcaseは最初x2hsx dep $ Lambda exprにしていたのだが，WildPになってしまうとguardできなくなるし，かといってCaseの内側でWildPへの置換をやらないとするとみにくいし，このパターンだけWildPを止めるくらいならLambdaの分を展開した方が早いや，ってことで．
                                  ex -> Match (VarP succn) (GuardedB [(NormalG (InfixE (Just $ VarE succn) (VarE $ mkName ">") (Just $ LitE $ IntegerL 0)),ex)]) [ValD (VarP name) (NormalB (InfixE (Just $ VarE succn) (VarE $ mkName "-") (Just $ LitE (IntegerL 1)))) []]
                                                    where str   = [chr $ fromIntegral (dep+1)]
                                                          name  = mkName str
                                                          succn = mkName ("succ"++str)
                            | nameBase name == "negate"  ->
                                case x2hsx (dep+1) fdep expr of
                                  ex -> Match (VarP negn) (GuardedB [(NormalG (InfixE (Just $ VarE negn) (VarE $ mkName "<") (Just $ LitE $ IntegerL 0)),ex)]) [ValD (VarP name) (NormalB ((VarE 'negate) `AppE` (VarE negn))) []]
                                                    where str   = [chr $ fromIntegral (dep+1)]
                                                          name  = mkName str
                                                          negn = mkName ("neg"++str)
                  LitE lit  -> Match (LitP lit) (NormalB $ x2hsx dep fdep expr) []
                  e         -> error (pprint e ++ " : non-constructor where a constructor is expected.")
          n `occursIn` Lambda e      = succ n `occursIn` e
          n `occursIn` FunLambda e   = n      `occursIn` e
          --          n `occursIn` FixCase ts = any (\(_,a,ce) -> (n+a+2) `occursIn` ce) ts
          n `occursIn` X m           = n==m
          n `occursIn` (f :$ e)   = (n `occursIn` f) || (n `occursIn` e)
          n `occursIn` Case x ts  = n `occursIn` x   || any (\(_,a,ce) -> (n+a) `occursIn` ce) ts
          n `occursIn` Fix e m is = n `elem` is      || (n+m) `occursIn` e
          _ `occursIn` _          = False
n `funOccursIn` Lambda e      = n      `funOccursIn` e
n `funOccursIn` FunLambda e   = succ n `funOccursIn` e
n `funOccursIn` FunX m        = n==m
n `funOccursIn` (f :$ e)   = (n `funOccursIn` f) || (n `funOccursIn` e)
n `funOccursIn` Case x ts  = n `funOccursIn` x || any (\(_,a,ce) -> n `funOccursIn` ce) ts
n `funOccursIn` Fix e _ _  = succ n `funOccursIn` e
_ `funOccursIn` _          = False


lightBeta :: CoreExpr -> CoreExpr
lightBeta (Fix e m is) | 0 `funOccursIn` e = Fix (lightBeta e) m is
                       | otherwise         = liftFun 0 $ nlift 0 m $ foldr ($) (lightBeta e) $ zipWith replace [m-1,m-2..0] $ map (m+) is
lightBeta (Lambda e)    = Lambda $ lightBeta e
lightBeta (FunLambda e) = FunLambda $ lightBeta e
lightBeta (Lambda e :$ X n) = lightBeta $ nlift 0 1 $ replace 0 n e

lightBeta (f :$ e)      = lightBeta f :$ lightBeta e
lightBeta (Case x ts)   = Case (lightBeta x) (map (\(c,a,ce) -> (c,a,lightBeta ce)) ts)
lightBeta e             = e

replace o n e@(X i)       | i==o = X n
replace o n (Lambda e)    = Lambda (replace (succ o) (succ n) e)
replace o n (FunLambda e) = FunLambda $ replace o n e
replace o n (f :$ e)      = replace o n f :$ replace o n e
replace o n (Case x ts)   = Case (replace o n x) (map (\(c,a,ce) -> (c,a,replace (o+a) (n+a) ce)) ts)
replace o n (Fix e m is)  = Fix (replace (o+m) (n+m) e) m (map (\x -> if x==o then n else x) is)
replace o n e = e

liftFun th (FunX i) | th<i = FunX (pred i)
liftFun th (Lambda e) = Lambda (liftFun th e)
liftFun th (FunLambda e) = FunLambda (liftFun (succ th) e)
liftFun th (f :$ e) = liftFun th f :$ liftFun th e
liftFun th (Case x ts) = Case (liftFun th x) (map (\(c,a,ce) -> (c,a,liftFun th ce)) ts)
liftFun th (Fix e m is) = Fix (liftFun (succ th) e) m is
liftFun _  e = e
nlift :: Int8 -> Int8 -> CoreExpr -> CoreExpr
nlift th n (X i) | th<i = X (i-n)
nlift th n (Lambda e) = Lambda (nlift (succ th) n e)
nlift th n (FunLambda e) = FunLambda (nlift th n e)
nlift th n (f :$ e) = nlift th n f :$ nlift th n e
nlift th n (Case x ts) = Case (nlift th n x) (map (\(c,a,ce) -> (c,a,nlift (th+a) n ce)) ts)
nlift th n (Fix e m is) = Fix (nlift (th+m) n e) m (map (nliftInt th n) is)
nlift th n e = e
nliftInt :: Int8 -> Int8 -> Int8 -> Int8
nliftInt th n i | th < i    = i-n
                | otherwise = i


napply n f x = iterate f x `genericIndex` n



-- Another 'Primitive' moved from MagicHaskeller.lhs, which should be renamed in some way....
type Primitive = (HValue, Exp, Type)
newtype HValue = HV (forall a. a)

primitivesToTCL :: [Primitive] -> TyConLib
primitivesToTCL ps = let (_,_,ts) = unzip3 ps in thTypesToTCL ts
-- thTypesToTCL encloses defaultTyCons

primitivesToVL :: TyConLib -> [Primitive] -> VarLib
primitivesToVL tcl ps = dynamicsToVL (map (primitiveToDynamic tcl) ps ++ defaultPrimitives)

-- | 'dynamicsToVL' is useful for incremental learning.
dynamicsToVL :: [PD.Dynamic] -> VarLib
dynamicsToVL = listToArray

prioritiesToVPL :: [Int] -> VarPriorityLib
prioritiesToVPL = listToArray

listToArray :: (Integral i, Ix i) => [a] -> Array i a
listToArray ds = listArray (0, genericLength ds - 1) ds

primitiveToDynamic :: TyConLib -> Primitive -> PD.Dynamic
primitiveToDynamic tcl (HV x, e, ty) = PD.unsafeToDyn tcl (thTypeToType tcl ty) x e

-- | 'defaultVarLib' can be used as a VarLib for testing and debugging. Currently this is used only by the analytical synthesizer.
defaultVarLib :: VarLib
defaultVarLib = primitivesToVL undefined []   --  = listArray (0, lenDefaultPrimitives-1) defaultPrimitives

lenDefaultPrimitives = genericLength defaultPrimitives

-- | @defaultPrimitives@ is the set of primitives that we want to make sure to appear in VarLib but may not appear in the primitive set with which to synthesize.
--   In other words, it is the set of primitives we want to make sure to assign IDs to.
defaultPrimitives :: [PD.Dynamic]
defaultPrimitives
    = [
       $(PD.dynamic [|defaultTCL|] [|()::()|]),
       $(PD.dynamic [|defaultTCL|] [|(,)     ::a->b->(a,b)|]),
       $(PD.dynamic [|defaultTCL|] [|(,,)    ::a->b->c->(a,b,c)|]),
       $(PD.dynamic [|defaultTCL|] [|(,,,)   ::a->b->c->d->(a,b,c,d)|]),
       $(PD.dynamic [|defaultTCL|] [|(,,,,)  ::a->b->c->d->e->(a,b,c,d,e)|]),
       $(PD.dynamic [|defaultTCL|] [|(,,,,,) ::a->b->c->d->e->f->(a,b,c,d,e,f)|]),
       $(PD.dynamic [|defaultTCL|] [|(,,,,,,)::a->b->c->d->e->f->g->(a,b,c,d,e,f,g)|]),

       $(PD.dynamic [|defaultTCL|] [|Left    :: a -> Either a b|]),
       $(PD.dynamic [|defaultTCL|] [|Right   :: b -> Either a b|]),
       $(PD.dynamic [|defaultTCL|] [|Nothing :: Maybe a|]),
       $(PD.dynamic [|defaultTCL|] [|Just    :: a -> Maybe a|]),
       $(PD.dynamic [|defaultTCL|] [|LT      :: Ordering|]),
       $(PD.dynamic [|defaultTCL|] [|EQ      :: Ordering|]),
       $(PD.dynamic [|defaultTCL|] [|GT      :: Ordering|]),

       $(PD.dynamic [|defaultTCL|] [|(+)::Int->Int->Int|]),
       $(PD.dynamic [|defaultTCL|] [|False::Bool|]),
       $(PD.dynamic [|defaultTCL|] [|True::Bool|]),
       $(PD.dynamic [|defaultTCL|] [|[]::[a]|]),
       $(PD.dynamic [|defaultTCL|] [|(:)::a->[a]->[a]|]),
       $(PD.dynamic [|defaultTCL|] [|0::Int|]),         -- What if, e.g., Integer instead of Int is used?
       $(PD.dynamic [|defaultTCL|] [|succ::Int->Int|]),
       $(PD.dynamic [|defaultTCL|] [|negate::Int->Int|])]

-- succ, viewed as a constructor, can be converted into n+k pattern while postprocessing, but what can I do for negate?
-- Maybe I could say @ case x of _ | x<0 -> ... where i = -x @, so I can avoid introducing a new variable.
-- ... but then, what if x is not actually a variable?
-- ... Uh, n+k pattern can not yet be handled by TH. (Try  @runQ [| case 3 of k+1 -> k |] >>= print@  in GHCi.)
-- The above are dealt with by CoreLang.exprToTHExp.

\end{code}
