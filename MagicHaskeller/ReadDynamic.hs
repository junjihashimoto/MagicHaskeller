-- 
-- (c) Susumu Katayama
--
-- -prof$B$9$k$H$-$K(B-auto-all$B$9$k$H(BPAP$B$K(Benter$B$7$F$7$^$&ItJ,$r$o$1$F$_$?!%:G=i(BMyDynamic$B$KF~$l$h$&$H;W$C$?$N$@$,!$(Bcyclic$B$K$J$C$?$N$G!%(B

{-# LANGUAGE TemplateHaskell #-}
module MagicHaskeller.ReadDynamic where
-- import ReadType
import MagicHaskeller.MyDynamic
import Language.Haskell.TH
import MagicHaskeller.TyConLib(defaultTCL)
dynS = $(dynamic [|undefTCL|] [| s :: (b->c->a) -> (b->c) -> b -> a |])
dynK = $(dynamic [|undefTCL|] [| const :: a->b->a |])
dynI = $(dynamic [|undefTCL|] [| id :: a->a |])
dynB = $(dynamic [|undefTCL|] [| (.) :: (c->a) -> (b->c) -> b -> a |])
dynC = $(dynamic [|undefTCL|] [| flip :: (b->c->a) -> c -> b -> a |])
dynS' = $(dynamic [|undefTCL|] [| sprime :: (a->b->c)->(d->a)->(d->b)->d->c |])
dynB' = $(dynamic [|undefTCL|] [| bprime :: (a->b->c)->a->(d->b)->d->c |])
dynC' = $(dynamic [|undefTCL|] [| cprime :: (a->b->c)->(d->a)->b->d->c |])
-- readType assumes the tcl is undefTCL, so it cannot be used when type constructors other than -> are used.
s = \f g x -> f x (g x)
sprime = (\f g h x -> f (g x) (h x))
bprime = (\f g h x -> f  g    (h x))
cprime = (\f g h x -> f (g x)  h)

-- undefTCL = error "undefTCL" -- This is bad, actually, because we cannot expect laziness to work here, because the tcl is spliced.
undefTCL = defaultTCL