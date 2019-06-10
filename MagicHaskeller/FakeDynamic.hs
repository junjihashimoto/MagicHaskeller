-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE MagicHash, ExistentialQuantification, PolymorphicComponents, TemplateHaskell, ImpredicativeTypes #-}
module MagicHaskeller.FakeDynamic(
        Dynamic,
        fromDyn,
        fromDynamic,
        dynApply,
        dynApp,
        dynAppErr,
        unsafeFromDyn, -- :: Dynamic -> a
        unsafeToDyn, -- :: Type -> a -> Dynamic
        aLittleSafeFromDyn, -- :: Type -> Dynamic -> a
        fromPD,
        dynamic, dynamicH
        -- I (susumu) believe this is enough, provided unsafeFromDyn does not invoke typeOf for type checking. (Otherwise there would be ambiguity error.)
                                 ) where

import Data.Typeable

import GHC.Exts

import MagicHaskeller.Types
import MagicHaskeller.TyConLib
import Control.Monad

import qualified MagicHaskeller.PolyDynamic as PD

import MagicHaskeller.ReadTHType(thTypeToType)
import MagicHaskeller.ReadTypeRep(trToType)
import Language.Haskell.TH hiding (Type)
import MagicHaskeller.MHTH
import Data.Typeable(typeOf)



newtype Dynamic = Dynamic {unsafeFromDyn::forall a. a}

unsafeToDyn :: TyConLib -> Type -> a -> e -> Dynamic
unsafeToDyn _ tr a e = Dynamic (unsafeCoerce# a)

aLittleSafeFromDyn :: Type -> Dynamic -> a
aLittleSafeFromDyn _ (Dynamic o) = o

fromDyn :: Typeable a => TyConLib -> Dynamic -> a -> a
fromDyn tcl (Dynamic o) dflt = o
fromDynamic :: MonadPlus m => Type -> Dynamic -> m a
fromDynamic tr (Dynamic o) = return o

instance Show Dynamic where
   showsPrec _ _ = showString "<< FakeDynamic >>"

dynApply :: Dynamic -> Dynamic -> Maybe Dynamic
dynApply f x = Just (dynApp f x)

dynApp :: Dynamic -> Dynamic -> Dynamic
dynApp (Dynamic f) (Dynamic x) = Dynamic ((unsafeCoerce# f) x)
dynAppErr :: String -> Dynamic -> Dynamic -> Dynamic
dynAppErr _ f x = dynApp f x

fromPD :: PD.Dynamic -> Dynamic
fromPD = Dynamic  .  PD.unsafeFromDyn


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

px eqtcl e ty        = [| unsafeToDyn $eqtcl (thTypeToType $eqtcl $(typeToExpType ty)) $(return se) $(expToExpExp se) |]
    where se = SigE e ty
