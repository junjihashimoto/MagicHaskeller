-- 
-- (c) Susumu Katayama
--
-- Dynamic with unsafe execution.

{-# LANGUAGE CPP, TemplateHaskell, MagicHash, RankNTypes #-}
module MagicHaskeller.PolyDynamic (
        Dynamic(..),
        fromDyn,        -- :: Type -> Dynamic -> a -> a
        fromDynamic,    -- :: Type -> Dynamic -> Maybe a
        dynApply,
        dynApp,
        dynAppErr,
        unsafeToDyn -- :: Type -> a -> Dynamic
        , aLittleSafeFromDyn -- :: Type -> Dynamic -> a
        , fromPD, dynamic,dynamicH
        -- I (susumu) believe the above is enough, provided unsafeFromDyn does not invoke typeOf for type checking. (Otherwise there would be ambiguity error.)
  ) where


import Data.Typeable
import Data.Maybe

import GHC.Exts(unsafeCoerce#)

import MagicHaskeller.Types
import MagicHaskeller.TyConLib
import Control.Monad

import Language.Haskell.TH hiding (Type)

import Debug.Trace

import MagicHaskeller.ReadTypeRep(trToType)
import MagicHaskeller.ReadTHType(typeToTHType)


import MagicHaskeller.ReadTHType(thTypeToType)
import MagicHaskeller.MHTH
import Data.Typeable(typeOf)


infixl `dynApp`

data Dynamic = Dynamic {dynType::Type, unsafeFromDyn::forall a. a, dynExp::Exp}
-- CoreExprはPrimitiveがDynamicを使っているので，Expの代わりに使うとhibootしないといけなくなる．

unsafeToDyn :: TyConLib -> Type -> a -> Exp -> Dynamic
unsafeToDyn tcl tr a e = Dynamic (unChin tr) (unsafeCoerce# a) e
-- unsafeToDyn tcl tr a e = Dynamic tr (unsafeCoerce# a) (SigE e (typeToTHType tcl tr)) -- こっちはこっちで便利っぽいのだが．

aLittleSafeFromDyn :: Type -> Dynamic -> a
aLittleSafeFromDyn tr (Dynamic t o _)
    = case mgu tr t of
        Just _  -> o
        Nothing -> error ("aLittleSafeFromDyn: type mismatch between "++show tr++" and "++show t)
fromDyn :: Typeable a => TyConLib -> Dynamic -> a -> a
fromDyn tcl (Dynamic t o _) dflt
    = case mgu (trToType tcl (typeOf dflt)) t of
        Just _  -> o
        Nothing -> dflt
fromDynamic :: MonadPlus m => Type -> Dynamic -> m a
fromDynamic tr (Dynamic t o _) = mgu tr t >> return o

instance Show Dynamic where
   showsPrec _ (Dynamic t _ e) = ("<dynamic "++) . (pprint e++) . ("::"++) . showsPrec 0 t . ('>':)

-- (f::(a->b)) `dynApply` (x::a) = (f a)::b
dynApply :: Dynamic -> Dynamic -> Maybe Dynamic
dynApply (Dynamic t1 f e1) (Dynamic t2 x e2) =
  case mguFunAp t1 t2 of
    Just t3 -> -- trace ("dynApply t1 = "++ show t1++", and t2 = "++show t2++", and t3 = "++show t3) $
               Just (Dynamic t3 ((unsafeCoerce# f) x) (AppE e1 e2))
    Nothing -> Nothing

dynApp :: Dynamic -> Dynamic -> Dynamic
dynApp = dynAppErr ""
dynAppErr :: String ->Dynamic -> Dynamic -> Dynamic
dynAppErr s f x = case dynApply f x of 
                    Just r -> r
                    Nothing -> error ("Type error in dynamic application.\n" ++
                               "Can't apply function " ++ show f ++
                               " to argument " ++ show x ++ "\n" ++ s)

fromPD = id


-- 以下はMyDynamicからとってきたもので，PolyDynamicにあるのと全く同じ．
{-
$(dynamic [|tcl|] [| (,) :: forall a b. a->b->(a,b) |])
のようにできるようにする．CLEANのdynamicみたいな感じ．
-}
dynamic :: ExpQ -> ExpQ -> ExpQ
dynamic eqtcl eq = eq >>= p' eqtcl


-- Quasi-quotes with higher-rank types are not permitted. When that is the case, take the type info apart from the expression.
-- E.g. $(dynamicH [|tcl|] 'foo [t| forall a b. a->b->(a,b) |]) is equivalent to $(dynamic [|tcl|] [| foo :: forall a b. a->b->(a,b) |])
dynamicH :: ExpQ -> Name -> TypeQ -> ExpQ
dynamicH eqtcl nm tq = do t <- tq
                          px eqtcl (VarE nm) t
-- p' is like MagicHaskeller.p'
p' eqtcl (SigE e ty) = px eqtcl e ty
p' eqtcl e           = [| unsafeToDyn $eqtcl (trToType $eqtcl (typeOf $(return e)))    $(return e)  $(expToExpExp e) |]
-- px eqtcl e ty        = [| unsafeToDyn $eqtcl (thTypeToType $eqtcl $(typeToExpType ty)) $(return se) $(expToExpExp se) |] -- こっちはこっちで便利っぽいのだが．
px eqtcl e ty        = [| unsafeToDyn $eqtcl (thTypeToType $eqtcl $(typeToExpType ty)) $(return se) $(expToExpExp e) |]
    where se = SigE e ty
