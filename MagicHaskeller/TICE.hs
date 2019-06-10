-- This module infers the type of given CoreExpr.
-- This is an updated version of the old Infer.lhs
{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
module MagicHaskeller.TICE where
import MagicHaskeller.CoreLang
import MagicHaskeller.Types
import MagicHaskeller.TyConLib
import MagicHaskeller.Execute(unsafeExecute, unDeBruijn, s, sprime, bprime, cprime, fix)
import MagicHaskeller.PriorSubsts
import qualified MagicHaskeller.PolyDynamic as PD
import MagicHaskeller.MyDynamic(unsafeFromDyn)
import MagicHaskeller.ReadTHType(thTypeToType)
import Data.Array.IArray
import Control.Monad(MonadPlus)
import Language.Haskell.TH(pprint)

import Debug.Trace

type TI = PriorSubsts Maybe

ceToDynamic :: TyConLib -> VarLib -> CoreExpr -> PD.Dynamic
ceToDynamic tcl vl ce = case tiCE tcl vl ce of
                          Nothing -> error ("ceToDynamic: " ++ pprint (exprToTHExp' False vl ce) ++ " type mismatch.")
                          Just ty -> PD.unsafeToDyn tcl ty (unsafeFromDyn $ unsafeExecute vl ce) $ exprToTHExp vl ce

tiCE :: (Functor m, MonadPlus m) => TyConLib -> VarLib -> CoreExpr -> m Type
tiCE tcl vl ce = do t <- runPS (tiEx tcl vl (unDeBruijn ce) >>= applyPS)
                    return $ normalize t
tiEx tcl vl ex = tie ex
    where
      tie (e :$ f) = do
        te <- tie e
        tf <- tie f
        tv <- newTVar
        let t = TV tv
        (if runPS (unify (tf :-> t) te) == Nothing then trace ("unifying " ++ show (tf :-> t) ++ " and " ++ show te) else id)
                     unify (tf :-> t) te
        t' <- applyPS t -- 勝手にこの行入れちゃったけど，いらないの？
        return t'
      tie prim     = freshInst (PD.dynType $ exe prim)
      -- myTypeOf is a version of exe defined in Execute.hs. 
      {-# INLINE exe #-}
      exe :: CoreExpr -> PD.Dynamic
      exe (Primitive n) = vl!n
      exe (PrimCon   n) = vl!n
      exe (Context (Dict pd)) = pd
      exe S = $(PD.dynamic [|defaultTCL|] [| s     :: (b->c->a) -> (b->c) -> b -> a |])
      exe K = $(PD.dynamic [|defaultTCL|] [| const :: a->b->a |])
      exe I = $(PD.dynamic [|defaultTCL|] [| id    :: a->a    |])
      exe B = $(PD.dynamic [|defaultTCL|] [| (.)   :: (c->a) ->    (b->c) -> b -> a |])
      exe C = $(PD.dynamic [|defaultTCL|] [| flip  :: (b->c->a) ->     c  -> b -> a |])
      exe S' = $(PD.dynamic [|defaultTCL|] [| sprime :: (a->b->c)->(d->a)->(d->b)->d->c |])
      exe B' = $(PD.dynamic [|defaultTCL|] [| bprime :: (a->b->c)->    a ->(d->b)->d->c |])
      exe C' = $(PD.dynamic [|defaultTCL|] [| cprime :: (a->b->c)->(d->a)->b->d->c |])
      exe Y  = $(PD.dynamic [|defaultTCL|] [| fix    :: (a->a)->a |])
      exe foo = error ("TICE.tiEx: " ++ show foo ++ " : unknown combinator")
