-- 
-- (C) Susumu Katayama
--
module MagicHaskeller.Analytical.Syntax where

import Control.Monad -- hiding (guard)
import Data.List(nub)

import qualified MagicHaskeller.Types as T

import Data.Word

import MagicHaskeller.CoreLang(Var)

--
-- Datatypes
--

data IOPair a = IOP { numUniIDs :: Int  -- ^ number of variables quantified with forall
                    , inputs    :: [Expr a] -- ^ input example for each argument. The last argument comes first.
                    , output    :: Expr a}
             deriving (Show,Eq)
instance Functor IOPair where
  fmap f iop = iop{inputs = map (fmap f) $ inputs iop, output = fmap f $ output iop}

type TBS = [Bool]                 -- ^ the to-be-sought list
data Expr a = E {ann :: a, iD :: Int} -- ^ existential variable. When doing analytical synthesis, there is no functional variable. 
            | U {ann :: a, iD :: Int} -- ^ universal variable. When doing analytical synthesis, there is no functional variable. 
                     --   IntではなくTH.Nameを直接使った方がよい？
            | C {ann :: a, sz :: Int, ctor :: T.Typed Constr, fields :: [Expr a]}
            deriving (Show)
instance Eq (Expr a) where   -- We just ignore the annotations and compare syntactically.
  E{iD=i} == E{iD=j} = i==j
  U{iD=i} == U{iD=j} = i==j
  C{ctor=c,fields=fs} == C{ctor=d,fields=gs} = T.typee c == T.typee d && fs == gs
                                               -- We do not chech the equivalence of sizes because that would force evaluation. 
  _ == _ = False
instance Functor Expr where
  fmap f (E a i) = E (f a) i
  fmap f (U a i) = U (f a) i
  fmap f c       = c{ann = f (ann c), fields = map (fmap f) $ fields c}

type Constr  = Var
normalizeMkIOP :: [Expr a] -> Expr a -> IOPair a
normalizeMkIOP ins out = let varIDs = nub $ concatMap vr (out : ins)
                             tup    = zip varIDs [0..]
                         in mapIOP (mapU (\tv -> case lookup tv tup of Just n  -> n)) IOP{numUniIDs = length varIDs, inputs = ins, output = out}
vr (U _ i)      = [i]
vr (C{fields=es}) = concatMap vr es
mapU f (U a i) = U a $ f i
mapU f e@(C{fields=xs}) = e{fields=map (mapU f) xs}

maybeCtor :: Expr a -> Maybe (T.Typed Constr)
maybeCtor (C{ctor=c}) = Just c
maybeCtor _           = Nothing

hasExistential (E{}) = True
hasExistential (U{}) = False
hasExistential (C{fields=es}) = any hasExistential es

visibles tbs ins = [ i | (True,i) <- zip tbs ins ]

--
-- unification
--

type Subst a = [(Int, Expr a)]


unify (C _ _ i xs) (C _ _ j ys) | T.typee i == T.typee j = unifyList xs ys
                                | otherwise = mzero
unify e          f          | e==f      = return []
unify (E _ i)    e          = bind i e
unify e          (E _ i)    = bind i e
unify _        _        = mzero

unifyList []     []     = return []
unifyList (x:xs) (y:ys) = do s1 <- unify x y
                             s2 <- unifyList (map (apply s1) xs) (map (apply s1) ys)
                             return $ s2 `plusSubst` s1
unifyList _      _      = error "Partial application to a constructor." -- Can this happen?

bind i e | i `occursIn` e = mzero           -- I think permitting infinite data would break the unification algorithm.
         | otherwise      = return [(i,e)]

-- | 'apply' applies a substitution which replaces existential variables to an expression.
apply subst v@(E _ i)  = maybe v id $ lookup i subst
apply subst v@(U _ _)  = v
apply subst (C a _ i xs) = cap a i (map (apply subst) xs) -- 遅いかね

i `occursIn` (E _ j)      = i==j
i `occursIn` (U _ _)      = False
i `occursIn` (C _ _ _ xs) = any (i `occursIn`) xs


plusSubst :: Subst a -> Subst a -> Subst a
s0 `plusSubst` s1 = [(u, apply s0 t) | (u,t) <- s1] ++ s0

emptySubst = []


fresh f e@(E{})      = e
fresh f (U a i)    = E a $ f i
fresh f (C a s c xs) = C a s c (map (fresh f) xs)
-- | fusion of @apply s@ and @fresh f@
apfresh s e@(E{})      = e -- NB: this RHS is incorrect if apfresh is used for UniT (because s may include a replacement of e).
apfresh s (U a i) = maybe (E a i) id $ lookup i s
apfresh s (C a _sz c xs) = cap a c (map (apfresh s) xs)
mapE f e@(U{})    = e
mapE f (E a i)      = E a $ f i
mapE f e@(C{fields=xs}) = e{fields=map (mapE f) xs}


-- Note that numUniIDs will not be touched.
applyIOPs s iops = map (applyIOP s) iops
applyIOP s iop = mapIOP (apply s) iop
mapIOP f (IOP bvs ins out) = IOP bvs (map f ins) (f out)
mapTypee f (x T.::: t) = f x T.::: t


--
-- termination
--

newtype TermStat = TS {unTS :: [Bool]} deriving Show

initTS :: TermStat
initTS = TS $ replicate (length termCrit) True
updateTS :: [Expr a] -> [Expr a] -> TermStat -> TermStat
updateTS bkis is (TS bs) = TS $ zipWith (&&) bs [ bkis < is | (<) <- termCrit ]
evalTS :: TermStat -> Bool
evalTS (TS bs) = or bs

-- termination criteria. Enumerate anything that come to your mind. (Should this be an option?)
termCrit :: [[Expr a]->[Expr a]->Bool]
-- termCrit = [fullyLex, aWise, revFullyLex, revAWise ] -- , linear
--termCrit = [aWise,revAWise]
termCrit = [aWise]

fullyLex, revFullyLex, aWise, revAWise, linear :: [Expr a]->[Expr a]->Bool
fullyLex   = lessRevListsLex cmpExprs
revFullyLex= lessListsLex cmpExprs
aWise      = lessRevListsLex cmpExprSzs
revAWise   = lessListsLex cmpExprSzs
-- linear is really slow, so is not recommended.
linear ls rs = sum (map size ls) < sum (map size rs)
-- でも，caseでぶった切ったあとのすべての引数を比較しているから遅いのであって，一番最初の段階の引数だけで比較すれば速いのでは？
-- でも，Ackermann's functionで考えると，やっぱそれではダメっぽい．

revArgs :: ([Expr a]->[Expr a]->Bool) -> [Expr a]->[Expr a]->Bool
revArgs cmp ls rs = cmp (reverse ls) (reverse rs)

lessRevListsLex cmp  = revArgs (lessListsLex cmp)
lessListsLex cmp []       _        = False -- In general, input arguments of BKs should be shorter, and we have to compare only this length.
lessListsLex cmp (e0:es0) (e1:es1) = case cmp e0 e1 of LT -> True
                                                       EQ -> lessListsLex cmp es0 es1
                                                       GT -> False
cmpExprss []       []       = EQ
cmpExprss []       _        = LT
cmpExprss _        []       = GT
cmpExprss (e0:es0) (e1:es1) = case cmpExprs e0 e1 of EQ -> cmpExprss es0 es1
                                                     c  -> c
cmpExprs (C _ _ _ fs) (C _ _ _ gs) = cmpExprss fs gs
cmpExprs _            (C _ _ _ _)  = LT
cmpExprs (C _ _ _ _)  _            = GT
cmpExprs _            _            = EQ

cmpExprSzs e0 e1 = compare (size e0) (size e1)
size (C _ sz _ fs) = sz
size _        = 1 -- questionable?
cap a con fs = C a (1 + sum (map size fs)) con fs

-- Q: Are existential variables always smaller than constructor applications? A: No, I'm afraid.
-- If we want to make sure the termination, we can always return GT when questionable;
-- if we want to save all questionable expressions, we can always return LT when questionable.
