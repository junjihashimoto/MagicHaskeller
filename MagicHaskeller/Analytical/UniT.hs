{-# LANGUAGE FlexibleContexts #-}
-- 
-- (C) Susumu Katayama
--
module MagicHaskeller.Analytical.UniT where

import Control.Monad -- hiding (guard)
import Control.Monad.State -- hiding (guard)

import MagicHaskeller.Analytical.Syntax

type UniT a = StateT (St a)
data St   a = St {subst::Subst a, nextVar :: Int} deriving Show

emptySt = St {subst=[], nextVar=0}
{-
freshVar :: Monad m => UniT m Expr
freshVar = do st <- get
              let nv = nextVar st
              put st{nextVar = succ nv}
              return $ E nv
-}
freshIOP (IOP n ins out) = do st <- get
                              let nv = nextVar st
                              put st{nextVar = nv + n}
                              return $ IOP 0 (map (fresh (nv+)) ins) (fresh (nv+) out)

applyUT :: Monad m => Expr a -> UniT a m (Expr a)
applyUT ex = do s <- gets subst
                return $ apply s ex
applyIOPUT iop = do s <- gets subst
                    return $ applyIOP s iop
 
unifyUT :: MonadPlus m => Expr a -> Expr a -> UniT a m ()
unifyUT e1 e2 = case unify e1 e2 of Just s  -> modify (\st -> st{subst = s `plusSubst` subst st})
                                    Nothing -> mzero
{- Obviously this is slower, but I do not remember why I used this.
unifyUT e1 e2 = do s <- unify e1 e2
                   modify (\st -> st{subst = s `plusSubst` subst st})
-}
appUnifyUT e1 e2 = do s <- gets subst
                      unifyUT (apply s e1) (apply s e2)
