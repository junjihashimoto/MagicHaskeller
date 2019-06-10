-- 
-- (c) Susumu Katayama
--
MHTH used to consist of combinators which include quasi-quotes. They are moved from MagicHaskeller.lhs because Haddock dislikes quasi-quotes.
\begin{code}
-- #hide

{-# OPTIONS -XTemplateHaskell -cpp #-}
module MagicHaskeller.MHTH(expToExpExp, typeToExpType, decsToExpDecs) where 
import Language.Haskell.TH
import System.IO.Unsafe(unsafePerformIO)
import Data.IORef
-- import Types
import Control.Monad(liftM)

import MagicHaskeller.ReadTHType(showTypeName, plainTV, unPlainTV)


#ifdef __GLASGOW_HASKELL__
nameToNameStr :: (Name -> String) -> Name -> ExpQ
nameToNameStr shw name = return $ LitE (StringL (shw name))

-- This is necessary because GHC.Base.[] would not parse as expected.
showName :: Name -> String
showName name | name == '[]  = "[]" -- data constructor
              | name == ''[] = "[]" -- type constructor
              | otherwise    = show name

-- showVarName = nameBase
showVarName = showName

expToExpExp :: Exp -> ExpQ
expToExpExp (VarE name) = [| VarE (mkName $(nameToNameStr showVarName name)) |]
expToExpExp (ConE name) = [| ConE (mkName $(nameToNameStr showVarName name)) |]
expToExpExp (AppE e0 e1) = [| AppE $(expToExpExp e0) $(expToExpExp e1) |]
expToExpExp (LamE ps e) = [| LamE $(liftM ListE $ mapM patToExpPat ps) $(expToExpExp e) |]  
expToExpExp (InfixE Nothing   e Nothing)   = [| InfixE Nothing                  $(expToExpExp e) Nothing |]
expToExpExp (InfixE (Just e0) e Nothing)   = [| InfixE (Just $(expToExpExp e0)) $(expToExpExp e) Nothing |]
expToExpExp (InfixE Nothing   e (Just e1)) = [| InfixE Nothing                  $(expToExpExp e) (Just $(expToExpExp e1)) |]
expToExpExp (InfixE (Just e0) e (Just e1)) = [| InfixE (Just $(expToExpExp e0)) $(expToExpExp e) (Just $(expToExpExp e1)) |]
expToExpExp (TupE es) = [| TupE $((return . ListE) =<< mapM expToExpExp es) |]
expToExpExp (CondE e0 e1 e2) = [| CondE $(expToExpExp e0) $(expToExpExp e1) $(expToExpExp e2) |]
expToExpExp (ListE es) = [| ListE $((return . ListE) =<< mapM expToExpExp es) |]
expToExpExp e@(LitE (CharL c))     = [| LitE (CharL     $(return e)) |]
expToExpExp e@(LitE (StringL s))   = [| LitE (StringL   $(return e)) |]
expToExpExp e@(LitE (IntegerL c))  = [| LitE (IntegerL  $(return e)) |]
expToExpExp e@(LitE (RationalL s)) = [| LitE (RationalL $(return e)) |]
expToExpExp (SigE e t)             = [| SigE $(expToExpExp e) $(typeToExpType t) |]
expToExpExp e = [| VarE (mkName $(return $ LitE (StringL (show e)))) |]

{-
typeToExpType :: Type -> Exp
typeToExpType (TC (Con k i))      = [| TC (Con $(return $ LitE (IntegerL k)) $(return $ LitE (IntegerL i)) |]
typeToExpType (TV (Var i True k)) = [| TV (Var $(return $ LitE (IntegerL i)) True $(return $ LitE (IntegerL k)) |]
typeToExpType (TA t0 t1)          = [| TA $(typeToExpType t0) $(typeToExpType t1) |]
typeToExpType (t0 :-> t1)         = [| $(typeToExpType t0) :-> $(typeToExpType t1) |]
-}
typeToExpType :: Type -> ExpQ
typeToExpType (ForallT ns [] t) = [| ForallT (map (plainTV . mkName) $(return $ ListE $ map (LitE . StringL . showTypeName . unPlainTV) ns)) [] $(typeToExpType t) |]
typeToExpType (ForallT _ (_:_) _) = error "typeToExpType: Type classes are not implemented yet."
typeToExpType (ConT name)      = [| ConT (mkName $(nameToNameStr showTypeName name)) |]
typeToExpType (VarT name)      = [| VarT (mkName $(nameToNameStr showTypeName name)) |]
typeToExpType (AppT t0 t1)     = [| AppT $(typeToExpType t0) $(typeToExpType t1) |]
typeToExpType (TupleT n)       = [| TupleT $(return $ LitE (IntegerL (toInteger n))) |]
typeToExpType ArrowT           = [| ArrowT |]
typeToExpType ListT            = [| ListT |]

patToExpPat (VarP name) = [| VarP (mkName $(nameToNameStr showVarName name)) |]
patToExpPat (TupP ps)   = [| TupP $(liftM ListE $ mapM patToExpPat ps) |]
patToExpPat (ConP name ps) = [| ConP (mkName $(nameToNameStr showVarName name)) $(liftM ListE $ mapM patToExpPat ps) |]
patToExpPat (InfixP p0 name p1) = [| InfixP $(patToExpPat p0) (mkName $(nameToNameStr showVarName name)) $(patToExpPat p1) |]
patToExpPat (TildeP p)          = [| TildeP $(patToExpPat p) |]
patToExpPat (AsP name p)        = [| AsP (mkName $(nameToNameStr showVarName name)) $(patToExpPat p) |]
patToExpPat WildP               = [| WildP |]
patToExpPat (ListP ps)          = [| ListP $(liftM ListE $ mapM patToExpPat ps) |]
patToExpPat (SigP p t)          = [| SigP $(patToExpPat p) $(typeToExpType t) |]
patToExpPat (LitP (IntegerL i)) = [| LitP (IntegerL $(return $ LitE (IntegerL i))) |]
patToExpPat (LitP (CharL c))    = [| LitP (CharL    $(return $ LitE (CharL    c))) |]
patToExpPat (LitP (StringL cs)) = [| LitP (StringL  $(return $ LitE (StringL cs))) |]
patToExpPat (LitP (RationalL r)) = [| LitP (RationalL $(return $ LitE (RationalL r))) |]

decsToExpDecs ds = fmap ListE $ mapM decToExpDec ds
decToExpDec (FunD name clauses)         = [| FunD (mkName $(nameToNameStr showTypeName name)) $(liftM ListE $ mapM clauseToExpClause clauses) |]
decToExpDec (ValD pat (NormalB e) decs) = [| ValD $(patToExpPat pat) (NormalB $(expToExpExp e)) $(liftM ListE $ mapM decToExpDec decs) |]
decToExpDec (SigD name ty)              = [| SigD (mkName $(nameToNameStr showTypeName name)) $(typeToExpType ty) |]
decToExpDec d = error (show d ++ " : unsupported")

clauseToExpClause (Clause pats (NormalB e) decs) = [| Clause $(liftM ListE $ mapM patToExpPat pats) (NormalB $(expToExpExp e)) $(liftM ListE $ mapM decToExpDec decs) |]

#if __GLASGOW_HASKELL__ < 710
instance Ord Type where
    compare (ForallT _ [] t0) (ForallT _ [] t1) = compare t0 t1
    compare (ForallT _ [] _)  _                = GT
    compare _                 (ForallT _ _  _ ) = LT
    compare (VarT   n0)       (VarT    n1)     = compare n0 n1
    compare (VarT   _)        _                = GT
    compare _                 (VarT      _)    = LT
    compare (ConT   n0)       (ConT    n1)     = compare n0 n1
    compare (ConT   _)        _                = GT
    compare _                 (ConT      _)    = LT
    compare (TupleT   n0)     (TupleT    n1)   = compare n0 n1
    compare (TupleT   _)      _                = GT
    compare _                 (TupleT      _)  = LT
    compare ArrowT            ArrowT           = EQ
    compare ArrowT            _                = GT
    compare _                 ArrowT           = LT
    compare ListT             ListT            = EQ
    compare ListT             _                = GT
    compare _                 ListT            = LT
    compare (AppT f0 x0)      (AppT f1 x1)     = case compare f0 f1 of EQ -> compare x0 x1
                                                                       o  -> o
#endif
#endif
\end{code}
