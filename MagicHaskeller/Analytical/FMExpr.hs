-- 
-- (C) Susumu Katayama
--
-- Finite trie indexed by Expr, used for fast pattern match
module MagicHaskeller.Analytical.FMExpr where

import qualified Data.IntMap as IntMap

import qualified MagicHaskeller.Types as Types

import MagicHaskeller.Analytical.Syntax


iopsToVisFME :: TBS -> [IOPair a] -> FMExpr [IOPair a]
iopsToVisFME tbs = iopsToFME . map (visIOP tbs)
iopsToFME :: [IOPair a] -> FMExpr [IOPair a]
iopsToFME = assocsToFME . map iop2Assoc

visIOP :: TBS -> IOPair a -> IOPair a
visIOP tbs iop = iop {inputs = visibles tbs $ inputs iop}

iop2Assoc :: IOPair a -> (Expr a, IOPair a)
iop2Assoc iop = (output iop, iop)



-- | @FMExpr a@ is a finite trie representing @Expr () -> a@
data FMExpr a = EmptyFME -- use of emptyFME in place of EmptyFME should not be as efficient, because there are many EmptyFME's.
              | FME { existentialFME :: IntMap.IntMap a, universalFME :: [a], conApFME :: IntMap.IntMap (FMExprs a) } deriving Show
data FMExprs a = EmptyFMEs -- and there are many EmptyFMEs's, too.
               | FMEs { nilFMEs :: a, consFMEs :: FMExpr (FMExprs a) } deriving Show
instance Functor FMExpr where
  fmap _ EmptyFME = EmptyFME
  fmap f (FME {existentialFME=e, universalFME=u, conApFME=c}) = FME{existentialFME = fmap f e, universalFME = fmap f u, conApFME = fmap (fmap f) c}
instance Functor FMExprs where
  fmap f EmptyFMEs = EmptyFMEs
  fmap f (FMEs {nilFMEs = n, consFMEs = c}) = FMEs {nilFMEs = f n, consFMEs = fmap (fmap f) c}
assocsToFME :: [(Expr b, a)] -> FMExpr [a]
assocsToFME = foldr (\(k,v) -> updateFME (v:) [] k) emptyFME
updateFME :: (a->a) -> a -> Expr b -> FMExpr a -> FMExpr a
updateFME f x t                EmptyFME = updateFME f x t emptyFME
updateFME f x (E _ i)            fme      = fme { existentialFME = IntMap.insertWith (\_ -> f) i (f x) $ existentialFME fme }
updateFME f x (U _ i)            fme      = fme { universalFME   = insertNth f x i $ universalFME fme }
updateFME f x (C _ _ (c Types.:::_) fs) fme  = fme { conApFME       = IntMap.insertWith (\_ -> updateFMEs f x fs) (fromIntegral c) (updateFMEs f x fs EmptyFMEs) $ conApFME fme }
updateFMEs f x es         EmptyFMEs = updateFMEs f x es FMEs{nilFMEs = x, consFMEs = EmptyFME} 
updateFMEs f x []              fmes = fmes { nilFMEs  = f $ nilFMEs fmes }
updateFMEs f x (e:es)          fmes = fmes { consFMEs = updateFME (updateFMEs f x es) EmptyFMEs e $ consFMEs fmes }
emptyFME = FME{ existentialFME = IntMap.empty, universalFME = [], conApFME = IntMap.empty }


insertNth upd zero n []     = replicate n zero ++ [upd zero]
insertNth upd zero 0 (x:xs) = upd x : xs
insertNth upd zero n (x:xs) = x : insertNth upd zero (n-1) xs



-- returns the set of possible substitutions. Should the name be matchFME?
unifyFME :: Expr b -> FMExpr a -> [(a, Subst b)]
unifyFME x fme = unifyFME' x fme emptySubst
--unifyFME = matchFME
unifyFME' :: Expr b -> FMExpr a -> Subst b -> [(a, Subst b)]
unifyFME' x         EmptyFME s = []
-- unifyFME' (E i)        fme s = error "cannot happen for now"
unifyFME' (E{})        fme s = [ (x, s) | x <- valsFME fme ] -- ただし，unifyFME (E _) fmeの場合（全体がexistentialの場合）はそもそもintroBKせずにundefinedな引数にしてしまうべき．どうせその引数は使われないってことだから．
  {-
unifyFME' x@(E i)        fme s o = case lookup i s of Nothing -> [ (x, [(i,e')] `plusSubst` s) | (e,x) <- assocsFME fme, let e' = fresh (o+) e ] -- assocsFME :: FMExpr a -> [(Expr,a)]だけど，FMExprに情報を残しておけば無駄な計算がなくなるか．てゆーか，Typed ConstrのTypeの部分のためにそうする必要がある．
	       		       	   	       	      Just e  -> unifyFME' e fme s o
-}
unifyFME' x@(U _ i)      fme s = [ (v, subst `plusSubst` s)
                                 | (k,v) <- zip [0..] (universalFME fme)
                                 , subst <- case lookup k s of Nothing        -> [[(k,x)]]
                                                               Just (E{iD=j}) -> [[(j,x)]]
                                                               Just (U{iD=j}) | i==j -> [[]]
                                                               _              -> []
                                 ]
unifyFME' x@(C _ _sz (c Types.::: _) xs) fme s = matchExistential ++ matchConstr
    where matchExistential = [ (v, subst `plusSubst` s)
                             | (k,v) <- zip [0..] (universalFME fme)
                             , subst <- case lookup k s of Nothing -> [[(k,x)]]
                                                           Just e  -> unify e x
                             ]
          matchConstr      = case IntMap.lookup (fromIntegral c) (conApFME fme) of 
                                                                    Nothing   -> []
                                                                    Just fmes -> unifyFMEs xs fmes s
unifyFMEs :: [Expr b] -> FMExprs a -> Subst b -> [(a, Subst b)]
unifyFMEs _ EmptyFMEs _ = []
unifyFMEs []     fmes s = [ (nilFMEs fmes, s) ]
unifyFMEs (x:xs) fmes s = [ t | (fmes', s') <- unifyFME' x (consFMEs fmes) s, t <- unifyFMEs xs fmes' s' ]
{-
assocsFME :: FMExpr a -> [(Expr,a)]
assocsFME EmptyFME = []
assocsFME fme = [ (E i, v) | (i,v) <- IntMap.toList (existentialFME fme) ] ++ [ (U i, v) | (i,v) <- zip [0..] (universalFME fme) ]
	   ++ [ (C (sum $ map size xs) (c Types.::: error "Not implemented yet!") xs, v)  | (c,fmes) <- IntMap.toList (conApFME fme), (xs, v) <- assocsFMEs fmes ]
assocsFMEs :: FMExprs a -> [([Expr],a)]
assocsFMEs EmptyFMEs = []
assocsFMEs fmes = ([], nilFMEs fmes) : [ (x:xs, v) | (x,fmes') <- assocsFME (consFMEs fmes), (xs, v) <- assocsFMEs fmes ]
-}

-- valsFME = map snd . assocsFME
valsFME :: FMExpr a -> [a]
valsFME EmptyFME = []
valsFME fme = IntMap.elems (existentialFME fme) ++ universalFME fme
	   ++ [ v  | fmes <- IntMap.elems (conApFME fme), v <- valsFMEs fmes ]
valsFMEs :: FMExprs a -> [a]
valsFMEs EmptyFMEs = []
valsFMEs fmes = nilFMEs fmes : [ v | fmes' <- valsFME (consFMEs fmes), v <- valsFMEs fmes' ]

-- 短くした物．効率は確認してない．
matchFME :: Expr b -> FMExpr a -> [(a, Subst b)]
matchFME x fme = matchFME' x fme emptySubst
matchFME' :: Expr b -> FMExpr a -> Subst b -> [(a, Subst b)]
matchFME' x         EmptyFME s = []
matchFME' (E {}) fme s = [ (x, s) | x <- valsFME fme ] -- ただし，matchFME (E _) fmeの場合（全体がexistentialの場合）はそもそもintroBKせずにundefinedな引数にしてしまうべき．どうせその引数は使われないってことだから．
-- Universal variables only match to existentials
matchFME' x@(U{}) fme s = matchExistential x fme s
-- Constractor applications can match to both existentials and constructor applications with the same constructor.
matchFME' x@(C _ _sz (c Types.::: _) xs) fme s = matchExistential x fme s ++ matchConstr
    where matchConstr = case IntMap.lookup (fromIntegral c) (conApFME fme) of 
                                                               Nothing   -> []
                                                               Just fmes -> matchFMEs xs fmes s
matchExistential x fme s = [ (v, subst `plusSubst` s)
                           | (k,v) <- zip [0..] (universalFME fme)
                           , subst <- case lookup k s of Nothing -> [[(k,x)]]
                                                         Just e  -> unify e x
                           ]
-- matchFMEs matches corresponding constructor fields
matchFMEs :: [Expr b] -> FMExprs a -> Subst b -> [(a, Subst b)]
matchFMEs _ EmptyFMEs _ = []
matchFMEs []     fmes s = [ (nilFMEs fmes, s) ]
matchFMEs (x:xs) fmes s = [ t | (fmes', s') <- matchFME' x (consFMEs fmes) s, t <- matchFMEs xs fmes' s' ]

