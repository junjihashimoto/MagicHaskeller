-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE MagicHash, TemplateHaskell #-}
module MagicHaskeller.Execute(unsafeExecute, unDeBruijn, s, sprime, bprime, cprime, fix) where
import System.IO.Unsafe(unsafeInterleaveIO)
import MagicHaskeller.CoreLang
import GHC.Exts(unsafeCoerce#)
import Control.Concurrent(yield, ThreadId, throwTo)
import Control.Monad(mplus)
import MagicHaskeller.TyConLib
import Data.Array((!))

import MagicHaskeller.MyDynamic

import Language.Haskell.TH hiding (Type)

import Data.Int

unDeBruijn e = undeb 0 e

undeb dep (Lambda e) = lambda (dep+1) (undeb (dep+1) e)
undeb dep (X n)      = X (dep-n)
undeb dep (Y :$ e) = case undeb dep e of K :$ und -> und       -- fix (\_ -> foo) = foo 
                                         unde     -> Y :$ unde
undeb dep (e0 :$ e1) = undeb dep e0 :$ undeb dep e1
undeb dep (Fix e n is)  = undeb dep $ foldl (:$) (Y :$ FunLambda (napply (fromIntegral n) Lambda e)) (map X is)
undeb dep e          = e

-- well, B' is not so efficient.
lambda :: Int8 -> CoreExpr -> CoreExpr
lambda v e | v `isFreeIn` e = K :$ e
lambda v (X n)           = I
lambda v (f :$ x :$ y)
        | v `isFreeIn` f = if v `isFreeIn` x
                           then B' :$ f :$ x :$ (lambda v y)
                           else if v `isFreeIn` y
                                then C' :$ f :$ (lambda v x) :$ y
                                else S' :$ f :$ (lambda v x) :$ (lambda v y)
lambda v (x :$ y)
        | v `isFreeIn` x = B :$ x          :$ lambda v y
        | v `isFreeIn` y = C :$ lambda v x :$ y
        | otherwise      = S :$ lambda v x :$ lambda v y
v `isFreeIn` (f :$ x) = v `isFreeIn` f && v `isFreeIn` x
v `isFreeIn` (X n)    = v /= n
v `isFreeIn` _        = True

-- checks if there is a free variable. usually used after unDeBruijn is applied and before tiExpression is applied. 
-- と思ったのだが，tiExpressionが内部でunDeBruijnを呼んでる．
-- やっぱtiExpressionでfail使ってメッセージ運んだ方がよい？
freeVar :: CoreExpr -> Maybe String
freeVar (Lambda e)        = freeVar e
freeVar (e0 :$ e1)        = freeVar e0 `mplus` freeVar e1
freeVar _ = Nothing

-- Use haddock-2.2.2. Later (and much earlier) versions of haddock do not like quasi-quotes. See http://www.nabble.com/build-problems-on-Hackage-td21848164.html
unsafeExecute :: VarLib -> CoreExpr -> Dynamic
unsafeExecute vl e = exe (unDeBruijn e) where
    exe (e0 :$ e1) = dynAppErr "apply" (exe e0) (exe e1)
    exe (Primitive n) = fromPD (vl!n)
    exe (PrimCon   n) = fromPD (vl!n)
    exe (Context (Dict pd)) = fromPD pd
    exe S = $(dynamic [|defaultTCL|] [| s     :: (b->c->a) -> (b->c) -> b -> a |])
    exe K = $(dynamic [|defaultTCL|] [| const :: a->b->a |])
    exe I = $(dynamic [|defaultTCL|] [| id    :: a->a    |])
    exe B = $(dynamic [|defaultTCL|] [| (.)   :: (c->a) ->    (b->c) -> b -> a |])
    exe C = $(dynamic [|defaultTCL|] [| flip  :: (b->c->a) ->     c  -> b -> a |])
    exe S' = $(dynamic [|defaultTCL|] [| sprime :: (a->b->c)->(d->a)->(d->b)->d->c |])
    exe B' = $(dynamic [|defaultTCL|] [| bprime :: (a->b->c)->    a ->(d->b)->d->c |])
    exe C' = $(dynamic [|defaultTCL|] [| cprime :: (a->b->c)->(d->a)->b->d->c |])
    exe Y  = $(dynamic [|defaultTCL|] [| fix    :: (a->a)->a |])
    exe foo = error (show foo ++ " : unknown combinator")
-- readType assumes the tcl is undefined, so it cannot be used when type constructors other than -> are used.
s = \f g x -> f x (g x)
sprime = \f g h x -> f (g x) (h x)
bprime = \f g h x -> f  g    (h x)
cprime = \f g h x -> f (g x)  h
fix f = let x = f x in x
