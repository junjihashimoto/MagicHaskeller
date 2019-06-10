-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE MagicHash, TemplateHaskell #-}
module MagicHaskeller.ExprStaged where
import MagicHaskeller.CoreLang
import MagicHaskeller.MyDynamic
-- import ReadType
import Data.Array
import MagicHaskeller.Types as Types
import MagicHaskeller.Execute(unDeBruijn)
import Debug.Trace
import GHC.Exts(unsafeCoerce#)
import Language.Haskell.TH hiding (Con)
import MagicHaskeller.MHTH

-- The following two are used only by printTable(s) for debugging.
import MagicHaskeller.TyConLib(defaultTCL, tuplename)
import MagicHaskeller.ReadTHType(typeToTHType)

import Data.Int
import Data.List(genericTake, genericSplitAt)

see i j = pprint $ e2THE $ mkCE i j
seeType i j =   unDeBruijn $ mkCE i j

sees i j k = pprint $ e2THE $ mkCE_LambdaBoundHead i j k
seesType i j k =   unDeBruijn $ mkCE_LambdaBoundHead i j k

e2THE = exprToTHExp (error "exprToTHExp: vl required")


printTables = mapM_ putStrLn [ shows i $ (' ':) $ shows m $ (' ':) $ shows n $ ("\t("++) $ pprint (aimnTHE i m n) ++ ") :: " ++ pprintType (MagicHaskeller.ReadTHType.typeToTHType MagicHaskeller.TyConLib.defaultTCL $ aimnty i m n)
                                  | i <- [0..2], m <- [0..2], n <- [i+1..3] ]

printTable = mapM_ putStrLn [ shows m $ (' ':) $ shows n $ ("\t("++) $ pprint (hdmnTHE m n) ++ ") :: " ++ pprintType (MagicHaskeller.ReadTHType.typeToTHType MagicHaskeller.TyConLib.defaultTCL $ hdmnty m n)
                                  | m <- [0..2], n <- [0..2] ]


-- pprintType is copied (and improved a little) from MagicHaskeller.lhs. I think I reported the bug and sent a patch to ghc-bugs, but it seems it is not fixed yet.... Here HEAD means the head of my copy.

-- 'pprintType' is a workaround for the problem that @Language.Haskell.TH.pprint :: Type -> String@ does not print parentheses correctly.
-- (try @Language.Haskell.TH.runQ [t| (Int->Int)->Int |] >>= \e -> putStrLn (pprint e)@ in your copy of GHCi.)
-- The implementation here is not so pretty, but that's OK for my purposes. Also note that 'pprintType' ignores foralls.
pprintType (ForallT _ [] ty) = pprintType ty
pprintType (ForallT _ _  ty) = error "Type classes are not supported yet. Sorry...."
pprintType (VarT name)      = pprint name
pprintType (ConT name)      = pprint name
pprintType (TupleT n)       = tuplename n
pprintType ArrowT           = "(->)"
pprintType ListT            = "[]"
pprintType (AppT (AppT ArrowT t) u)       = '(' : pprintType t ++ " -> " ++ pprintType u ++ ")"
pprintType (AppT t u)       = '(' : pprintType t ++ ' ' : pprintType u ++ ")"
-- The problem of @Language.Haskell.TH.pprint :: Type -> String@ is now fixed at the darcs HEAD.



{-
-- $B4pK\E*$K(BCoreExpr$B$+$i(BDynamic$B$rI=$9(BTH.Exp$B$r:n$k!%(B
-- unsafeExecute ce$B$H(B $(exprToExpDynamic ce)$B$H$N0c$$$O!$8e<T$O&K<0$r%W%m%0%i%`Cf$KE=$jIU$1$k$N$G!$B?$/$N(Bprimitive combinators$B$r=hM}$9$k%3%9%H$,$+$+$i$J$$$C$F$3$H!%(BSupercombinator$B$K$h$k<BAu$_$?$$$J$b$N!%(B
exprToExpDynamic :: Language.Haskell.TH.Type -> CoreExpr -> ExpQ
exprToExpDynamic ty ce
    = case -- trace ("ce = "++pprint (exprToTHExp ce)) $
           e2THE ce of
                       the ->
--        the -> case tiExpression tl (error ("exprToExpDynamic: tcl required. unDeBruijn ce = "++show (unDeBruijn ce)++",\n and the = "++pprint the)) $ unDeBruijn ce of
                            do thee <- expToExpExp the  -- $B<B$O$3$3$,0lHV;~4V$,$+$+$k5$$,$9$k$N$@$,!$%G%P%C%0>pJs$7$+$J$$$N$G!$(BREALDYNAMIC$B$G$J$$>l9g$O$J$s$H$+$G$-$k$+$b!%(B
                               thty <- MHTH.typeToExpType ty         $B$3$l$@$H!$(Bsplice$B$7$?7k2L$,(BTH.Type$B$K$J$C$F$7$^$&!%(B
                               return ((((VarE 'unsafeToDyn) `AppE` thty)
                                                             `AppE` the)
                                                             `AppE` thee)
-}
mkVName :: Char -> Int -> Q Language.Haskell.TH.Name
mkVName c i = newName (c : show i)
mkVNames :: Char -> Int -> Q [Language.Haskell.TH.Name]
mkVNames c n = mapM (mkVName c) [0..n-1]
mkEs, mkAs, mkXs :: Int -> Q [Language.Haskell.TH.Name]
mkEs = mkVNames 'e'
mkAs = mkVNames 'a'
mkXs = mkVNames 'x'
mkHd = newName "hd"

hdmnTHEQ :: Int8 -> Int8 -> ExpQ
hdmnTHEQ m n = return $ (VarE 'unsafeCoerce#) `AppE` hdmnTHE m n
{-
hdmnTHEQ m n = do hd  <- mkHd
                  mes <- mkEs m
                  mxs <- mkXs m
                  nas <- mkAs n
                  let lambdas = LamE (map VarP (hd : mes ++ nas))
                      appa1an var = foldl AppE (VarE var) $ map VarE nas
                  return $ (VarE 'unsafeCoerce#) `AppE` lambdas (foldl AppE (VarE hd) (map appa1an mes))
-}
aimnTHEQ :: Int8 -> Int8 -> Int8 -> ExpQ
aimnTHEQ i m n = return $ (VarE 'unsafeCoerce#) `AppE` aimnTHE i m n
{-
aimnTHEQ i m n = do
                  mes <- mkEs m
                  nas <- mkAs n
                  let lambdas = LamE (map VarP (mes ++ nas))
                      appa1an var = foldl AppE (VarE var) $ map VarE nas
                  return $ (VarE 'unsafeCoerce#) `AppE` lambdas (foldl AppE (VarE (nas!!i)) (map appa1an mes))
-}

hdmnTHE :: Int8 -> Int8 -> Exp
hdmnTHE m n = e2THE (mkCE n m)
aimnTHE :: Int8 -> Int8 -> Int8 -> Exp
aimnTHE i m n = e2THE (mkCE_LambdaBoundHead i n m)

-- copied from ExecuteAPI $B$F$f!<$+!$(BmkCE_LambdaBoundHead$B$G$O(Bde Bruijn index$B$r;H$C$F$$$k$,!$(BExecuteAPI.aimn$B$O5U8~$-$K(Bindex$B$r3d$jEv$F$F$$$k$N$G!$$=$N$^$^;}$C$F$-$F$O%@%a!%(B
hdmnty :: Int8 -> Int8 -> Types.Type
hdmnty m n = hdty Types.:-> foldr (Types.:->) (foldr (Types.:->) tvr nas) (map (\r -> foldr (Types.:->) r nas) mrs)
    where hdty = foldr (Types.:->) tvr mrs
          mrs  = genericTake m tvrs
          nas  = genericTake n tvas
aimnty :: Int8 -> Int8 -> Int8 -> Types.Type
aimnty i m n = foldr (Types.:->) (foldr (Types.:->) tvr nas) (map (\r -> foldr (Types.:->) r nas) mrs)
    where hdty = foldr (Types.:->) tvr mrs
          mrs  = genericTake m tvrs
          nas  = case genericSplitAt (n-i-1) tvas of (tk,_:dr) -> tk ++ hdty : genericTake i dr -- hdmnty$B$H$N0c$$$O$3$3$@$1(B
mkTV :: Types.TyVar -> Types.Type
mkTV = Types.TV
tvrs = map mkTV [1,3..]
tvas = map mkTV [2,4..]
tvr  = mkTV 0


-- $B0J2<$N?tCM$O!$$I$N%5%$%:$^$GD>@\(Bsupercombinator$B$rMQ0U$9$k$+$rI=$9!%(B
-- $B$3$NHO0O$K<}$^$i$J$$>l9g$G$b!$(Bprimitive combinators$B$G%;%3%;%3$7$J$1$l$P$J$i$J$$$H$$$&Lu$G$O$J$$(B
maxArity, maxLenavails :: Int8
maxArity = 4
maxLenavails = 8 -- $B4pK\E*$K2?2s4X?t9g@.$9$k$+$NLdBj$J$N$G!$$?$H$($P(B13$B$H$+$J$i(B8+5$B$H9M$($F(B2$B2s9g@.$7$F$b$=$s$J$K8zN($OMn$A$J$$!$$H;W$&!%(B
maxDebindex = maxLenavails-1
-- maxArity = 0
-- maxLenavails = 0

mkCE :: Int8           -- ^ length of avails
        -> Int8          -- ^ arity of the head function
        -> CoreExpr
mkCE 0        _     = Lambda (X 0)
mkCE lenavail 0     = napply (lenavail+1) Lambda (X lenavail)
mkCE lenavail arity
     = let vs = map X $ reverse [0..lenavail-1]
           fs = map X $ reverse [lenavail..lenavail+arity-1]
           ce = X (lenavail+arity)
       in napply (arity+1+lenavail) Lambda (foldl (:$) ce $ fmap (\f -> foldl (:$) f vs) fs)

{-
usage:   (dynss !! length avail !! (arity_of_head)) `dynApp` (dynamic_head_as_ce) `dynApp` (dynamic_as_result_of_recursive_call_as_f) `dynApp` ... `dynApp` (dynamic_as_result_of_recursive_call_as_h)

[ [ \ce ->         ce ,  \ce -> \f ->         ce  f,        \ce -> \f g ->         ce  f       g,        \ce -> \f g h ->         ce  f       g       h,       ... ],
  [ \ce ->   (\e-> ce),  \ce -> \f ->   (\e-> ce (f e)),    \ce -> \f g ->   (\e-> ce (f e)   (g e)),    \ce -> \f g h -> (\e  -> ce (f e)   (g e)   (h e)),   ... ],
  [ \ce -> (\e b-> ce),  \ce -> \f -> (\e b-> ce (f e b)),  \ce -> \f g -> (\e b-> ce (f e b) (g e b)),  \ce -> \f g h -> (\e b-> ce (f e b) (g e b) (h e b)), ... ],
  ... ]
-}

-- mkCE$B$G(B\ce->$B$r$H$C$F(Bce$B$r(BX debindex$B$K$9$k$@$1!%(B
mkCE_LambdaBoundHead debindex lenavails arity
     = let vs = map X $ reverse [0..lenavails-1]
           fs = map X $ reverse [lenavails..lenavails+arity-1]
           ce = X debindex
       in napply (arity+lenavails) Lambda (foldl (:$) ce $ fmap (\f -> foldl (:$) f vs) fs)
-- $B$F$f!<$+!$(Bce$B$r:G8e$K;}$C$F$/$k$h$&$K$9$l$PE}9g$G$-$kLu$M!%(B
-- mkCE_LambdaBoundHead debindex lenavails arity = (mkCE lenavails (arity+1) :$ (Lambda $ X 0)) :$ (napply lenavails Lambda $ X debindex)

