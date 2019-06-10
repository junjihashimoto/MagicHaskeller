-- 
-- (c) Susumu Katayama
--

Everything written in this module can be rewritten using StateT.
When I wrote this first (around 2003?) I did not know the term `Monad Transformer' and I reinvented it....

\begin{code}
{-# LANGUAGE CPP, FlexibleInstances #-}
module MagicHaskeller.PriorSubsts where

import Control.Monad
import Control.Applicative -- necessary for backward compatibility
import Control.Monad.Search.Combinatorial
-- import Control.Monad.Search.BalancedMerge
import MagicHaskeller.Types
import Data.Array.IArray
import Data.Monoid
import MagicHaskeller.T10(mergeWithBy)

-- import T10(nubSortBy)
import Data.List

import Debug.Trace

-- sumPS :: [PriorSubsts Matrix a] -> PriorSubsts Matrix a
-- sumPS pss = PS $ \s i -> sumMx [ f s i | PS f <- pss]

substOKPS :: (Functor m, Monad m) => String -> PriorSubsts m ()
substOKPS str = do subst <- getSubst
                   if substOK subst then return () else error (str ++ "subst not OK. subst = "++show subst)

monsubst :: (Functor m, Monad m) => PriorSubsts m ()
monsubst = do s <- getSubst
              trace ("subst = "++show s) $ return ()

mkPS :: Monad m => m a -> PriorSubsts m a
mkPS x = PS (\subst mx -> x >>= \a -> return (a,subst,mx))


runPS :: Monad m => PriorSubsts m a -> m a
runPS (PS f) = do (x,_,_) <- f emptySubst 0
                  return x

-- delayPS :: (Delay (m a)) => PriorSubsts m a -> PriorSubsts m a
-- delayPS = convertPS delay
delayPS (PS f) = PS g where g s i = delay (f s i)
ndelayPS n (PS f) = PS g where g s i = ndelay n (f s i)

{-# SPECIALIZE convertPS :: ([(a,Subst,TyVar)] -> Recomp (a,Subst,TyVar)) -> PriorSubsts [] a -> PriorSubsts Recomp a #-}
{-# SPECIALIZE convertPS :: ([(a,Subst,TyVar)] -> [(a,Subst,TyVar)]) -> PriorSubsts [] a -> PriorSubsts [] a #-}
convertPS :: (m (a,Subst,TyVar) -> n (b,Subst,TyVar)) -> PriorSubsts m a -> PriorSubsts n b
convertPS f (PS g) = PS h where h s i = f (g s i)

newtype PriorSubsts m a = PS {unPS :: Subst -> TyVar -> m (a, Subst, TyVar)}
instance (Functor m, Monad m) => Applicative (PriorSubsts m) where
    {-# SPECIALIZE instance Applicative (PriorSubsts []) #-}
    pure x = PS (\s m -> return (x, s, m))
    (<*>)  = ap
instance (Functor m, Monad m) => Monad (PriorSubsts m) where
    {-# SPECIALIZE instance Monad (PriorSubsts []) #-}
    return     = pure
    PS x >>= f = PS (\s i -> do (a,t,j) <- x s i
                                unPS (f a) t j)
--    {-# INLINE (>>=) #-} 意味なかった．
--    PS x >>= f = x `thenPS` f これも意味なかった．まあ，Monadはデフォルトでinlineしてるかも？

-- {-# INLINE listThenPS #-}
-- {-# INLINE thenPS #-}
-- x `thenPS` f = PS (\s i -> do (a,t,j) <- x s i
--                               unPS (f a) t j)
-- x `listThenPS` f = PS (\s i -> [ (b, u, k) | (a, t, j) <- x s i, (b, u, k) <- unPS (f a) t j ])
-- {-# RULES "listThenPS" thenPS = listThenPS #-}

-- distPS is also used to implement ifDepthPS
distPS op (PS f) (PS g) = PS (\s i -> f s i `op` g s i)

instance (Functor m, MonadPlus m) => Alternative (PriorSubsts m) where
    {-# SPECIALIZE instance Alternative (PriorSubsts []) #-}
    empty = mzero
    (<|>) = mplus
instance (Functor m, MonadPlus m) => MonadPlus (PriorSubsts m) where
    {-# SPECIALIZE instance MonadPlus (PriorSubsts []) #-}
    mzero = PS (\_ _->mzero)
    mplus = distPS mplus
instance Delay m => Delay (PriorSubsts m) where
  delay (PS f) = PS $ \s i -> delay $ f s i
instance Monoid a => Monoid (PriorSubsts [] a) where
    mempty = PS (\_ _ -> [])
    mappend = distPS $ mergeWithBy (\(xs,k,i) (ys,_,_) -> (xs `mappend` ys, k, i)) (\ (_,k,_) (_,l,_) -> k `compare` l)
instance Monoid a => Monoid (PriorSubsts Recomp a) where
    mempty = PS (\_ _ -> mzero)
    PS f `mappend` PS g = PS $ \s i -> Rc $ \dep -> mergeWithBy (\(xs,k,i) (ys,_,_) -> (xs `mappend` ys, k, i)) (\ (_,k,_) (_,l,_) -> k `compare` l) (unRc (f s i) dep) (unRc (g s i) dep)

instance Functor m => Functor (PriorSubsts m) where
    fmap f (PS g) = PS (\s i -> fmap (\ (x, s', i') -> (f x, s', i')) (g s i))

{-# RULES "fmap/fmap" [2] forall f g x. fmap f (fmap g x) = fmap (f . g) x #-}


{-# SPECIALIZE applyPS :: Type -> PriorSubsts [] Type #-}
applyPS :: Monad m => Type -> PriorSubsts m Type
applyPS  ty    = PS (\s i -> return (apply s ty, s, i))
{-# SPECIALIZE updatePS :: Subst -> PriorSubsts [] () #-}
updatePS :: Monad m => Subst -> PriorSubsts m ()
updatePS subst = PS (\s i -> return ((), subst `plusSubst` s, i))
{-# SPECIALIZE updateSubstPS :: (Subst -> [] Subst) -> PriorSubsts [] () #-}
updateSubstPS :: Monad m => (Subst -> m Subst) -> PriorSubsts m ()
updateSubstPS f = PS (\s i -> f s >>= \s' -> return ((), s', i))

{-# SPECIALIZE setSubst :: Subst -> PriorSubsts [] () #-}
setSubst :: Monad m => Subst -> PriorSubsts m ()
setSubst subst = updateSubstPS (\_ -> return subst)

{-# SPECIALIZE mguPS :: Type -> Type -> PriorSubsts [] () #-}
mguPS, matchPS :: (Functor m, MonadPlus m) => Type -> Type -> PriorSubsts m ()
mguPS t0 t1 = do subst <- mgu t0 t1
                 updatePS subst
-- てゆーかmgtPSをmguPSの定義にしてもいいくらい．
mgtPS :: (Functor m, MonadPlus m) => Type -> Type -> PriorSubsts m Type
mgtPS t1 t2 = do mguPS t1 t2
                 applyPS t1
{-# SPECIALIZE varBindPS :: TyVar -> Type -> PriorSubsts [] () #-}
varBindPS :: (Functor m, MonadPlus m) => TyVar -> Type -> PriorSubsts m ()
varBindPS v t = do subst <- varBind v t
                   updatePS subst
matchPS t0 t1 = do subst <- match t0 t1
                   updatePS subst
{-
symPlusPS :: MonadPlus m => Subst -> PriorSubsts m ()
symPlusPS subst = do s0 <- getSubst
                     s1 <- symPlus subst s0
                     setSubst s1
-}

lookupSubstPS :: (Functor m, MonadPlus m) => TyVar -> PriorSubsts m Type
lookupSubstPS tvid = do subst <- getSubst
                        case lookupSubst subst tvid of Nothing -> mzero
                                                       Just ty -> return ty

-- what follow are mainly used by module Infer, but can be reused if necessary.
{-# SPECIALIZE getSubst :: PriorSubsts [] Subst #-}
getSubst :: Monad m => PriorSubsts m Subst
getSubst = PS (\s i -> return (s,s,i))
{-# SPECIALIZE getMx :: PriorSubsts [] TyVar #-}
getMx    :: Monad m => PriorSubsts m TyVar
getMx    = PS (\s i -> return (i,s,i))
{-# SPECIALIZE updateMx :: (TyVar->TyVar) -> PriorSubsts [] () #-}
updateMx :: Monad m => (TyVar->TyVar) -> PriorSubsts m ()
updateMx f = PS (\s i -> return ((), s, f i))
{-# SPECIALIZE unify :: Type -> Type -> PriorSubsts [] () #-}
unify :: (Functor m, MonadPlus m) => Type -> Type -> PriorSubsts m ()
unify t1 t2 = do s <- getSubst
                 u <- mgu (apply s t1) (apply s t2)
                 updatePS u

newTVar :: Monad m => PriorSubsts m TyVar
newTVar = PS (\ s n -> return (n, s, n+1))

-- I do not remember why this was removed. It has come back with the coming back of Infer.lhs as TICE.hs.
freshInst :: (Functor m, Monad m) => Type -> PriorSubsts m Type
freshInst ty = do tv <- reserveTVars $ maxVarID ty + 1
                  return $ mapTV (tv+) ty
{-
freshInst ty = do let tvs = tyvars ty
		  ntvs <- mapM (const newTVar) tvs
		  let ar = array (0,maxVarID ty) (zip (map tvID tvs) ntvs) 
		  return (inst ar ty)
    where inst :: Array Int TyVar -> Type -> Type
	  -- inst ar = mapTV (\tv -> ar ! tvID tv) -- mapTVはType.lhsからexportしない方が良さそうなので．てゆーか単に，Type.unifyFunAp(QTy)でmapTV相当のものを実装すれば良いのか？
	  inst ar (TA l r) = TA (inst ar l) (inst ar r)
	  inst ar (l:->r)  = inst ar l :-> inst ar r
	  inst ar (TV tv)  = TV (ar ! tvID tv)
	  inst _  t@(TC _) = t
-}



-- 同じ名前の関数がallifdefs/PSList.hsにもあったりする．役割も似たようなもん．
psListToPSRecomp :: (Int -> PriorSubsts [] a) -> PriorSubsts Recomp a
psListToPSRecomp f = PS (\subst int -> Rc (\dep -> case f dep of PS g -> g subst int))
psRecompToPSList :: PriorSubsts Recomp a -> Int -> PriorSubsts [] a
psRecompToPSList (PS f) dep = PS (\subst int -> case f subst int of Rc g -> g dep)

psListToPSDBound :: (Int -> PriorSubsts [] (a,Int)) -> PriorSubsts DBound a
psListToPSDBound f = PS (\subst int -> DB (\dep -> case f dep of PS g -> map tup23 $ g subst int))
psDBoundToPSList :: PriorSubsts DBound a -> Int -> PriorSubsts [] (a,Int)
psDBoundToPSList (PS f) dep = PS (\subst int -> case f subst int of DB g -> map tup32 $ g dep)

tup23 ((a,i),k,m) = ((a,k,m),i)
tup32 ((a,k,m),i) = ((a,i),k,m)

nubSortBy :: (a -> a -> Ordering) -> [a] -> [a]
nubSortBy cmp = uniqBy (\a b->cmp a b==EQ) . sortBy cmp
uniqBy :: (a->a->Bool) -> [a] -> [a]
uniqBy eq []     = []
uniqBy eq (x:xs) = case span (eq x) xs of (_,ns) -> x : uniqBy eq ns


-- | reserveTVars takes the number of requested tvIDs, reserves consecutive tvIDs, and returns the first tvID. 
reserveTVars :: Monad m => TyVar -> PriorSubsts m TyVar
reserveTVars n = PS (\s i -> return (i,s,i+n))
{- こっちの定義にしたら阿呆みたいに時間を食った．訳ワカメ
reserveTVars n = do i <- getMx
                    updateMx (n+)
                    return i
-}


{-
flatten :: PriorSubsts [a] -> PriorSubsts a
flatten (PS sbb) = PS (\s i -> map cat $ unMx (sbb s i))
cat :: Bag ([a], Subst, TyVar) -> Bag (a, Subst, TyVar)
cat xs = [ (y, s, i) | (ys, s, i) <- xs, y <- ys ]
-}
\end{code}
