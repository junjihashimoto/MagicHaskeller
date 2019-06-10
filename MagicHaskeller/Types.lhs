-- 
-- (c) Susumu Katayama
--

\begin{code}


{-# OPTIONS -cpp -funbox-strict-fields #-}
module MagicHaskeller.Types(Type(..), Kind, TyCon, TyVar, TypeName, Typed(..), tyvars, Subst, plusSubst, 
            emptySubst, apply, mgu, varBind, match, maxVarID, normalizeVarIDs, normalize, unChin,
            Decoder(..), typer, typee, negateTVIDs, limitType, saferQuantify, quantify, quantify', unquantify, lookupSubst, unifyFunAp,
            alltyvars, mapTV, size, unitSubst, applyCheck, assertsubst, substOK, eqType, getRet, getArity, getArities, getAritiesRet, splitArgs, getArgs, pushArgs, popArgs, mguFunAp, revSplitArgs, revGetArgs, module Data.Int
           ) where
import Data.List
import Control.Monad
import Data.Char(ord)
#ifdef QUICKCHECK
import Test.QuickCheck -- this is since 6.4
-- import Debug.QuickCheck
#endif
import Data.Int

-- import Debug.Trace

infixr :->, :>

trace _ = id


{- Heap profiling with -hy (i.e. by types) flag the -O0 code shows Type (and TyVar) could be improved (by using #Int's),
   but still I think that is not essential. I think recomputation (without memoization) and improvement in Runnable.hs should be tried.
-}


-- :> is same as :-> except FMType.lhs assumes it is a type constructor.
data Type = TV {-# UNPACK #-} !TyVar | TC {-# UNPACK #-} !TyCon | TA Type Type | Type :> Type | Type :-> Type | Type :=> Type
        deriving (Eq, Ord, Read)

size :: Type -> Int
size (TC _) = 1
size (TV _) = 1 -- but potentially large.
size (TA t0 t1)  = size t0 + size t1
size (t0 :> t1)  = size t0 + size t1
size (t0 :-> t1) = size t0 + size t1

{-
-- sizeCheck is normally id, but if the size is too large it fails.
sizeCheck :: Type -> Type
sizeCheck ty = sc 100 ty
    where sc 0 _ = error ("sizeCheck: " ++ show ty)
          sc n (TA t0 t1) = 
-}

{- I comment this out because this is unused (except in Classification.tex, where arityOf is redefined) and confusing along with |:>|.
arityOf :: Type -> Int
arityOf (t1 :-> t0) = 1 + arityOf t0
arityOf _ = 0 -- including :>
-}

#ifdef QUICKCHECK
instance Arbitrary Type where
    arbitrary = sized arbType

arbType 0 = oneof [liftM TV arbitrary, liftM TC arbitrary]
arbType n = frequency [ (8, arbType 0),
                        (2, liftM2 TA    (arbType (n `div` 2)) (arbType (n `div` 2))),
                        (2, liftM2 (:->) (arbType (n `div` 2)) (arbType (n `div` 2))) ]
#endif

-- {-# INLINE mapTV #-}
mapTV :: (TyVar -> TyVar) -> Type -> Type
mapTV f t = -- if t/=t then undefined else
            mtv t
    where mtv (TA t0 t1)  = TA (mtv t0) (mtv t1)
          mtv (t1 :=> t0) = (mtv t1) :=> (mtv t0)
          mtv (t1 :-> t0) = (mtv t1) :-> (mtv t0)
          mtv (t1 :> t0)  = (mtv t1) :>  (mtv t0)
          mtv (TV tv)     = TV (f tv)
          mtv tc@(TC _)   = tc

negateTVIDs :: Type -> Type
negateTVIDs   = mapTV (\tvid -> -1 - tvid)

-- limitType is like counting the size of a type, but is specialised to limit it.
limitType n (TC _)    = n-1
limitType n (TV _)    = n-1
limitType n (u :-> t) = lt n t u
limitType n (u :> t)  = lt n t u
limitType n (TA t u)  = lt n t u

lt n t u = case limitType n t of m | m > 0     -> limitType m u
                                   | otherwise -> -1

alltyvars :: Type -> Subst -> [TyVar]
alltyvars ty s = alltyvars' ty s []
alltyvars' :: Type -> Subst -> [TyVar] -> [TyVar]
alltyvars' (TV tv)   s = case lookupSubst s tv of Just t  -> alltyvars' t s
                                                  Nothing -> (tv:)
alltyvars' (TC tc)   s = id
alltyvars' (TA t u)  s = alltyvars' t s . alltyvars' u s
alltyvars' (u :> t)  s = alltyvars' t s . alltyvars' u s
alltyvars' (u :-> t) s = alltyvars' t s . alltyvars' u s
alltyvars' (u :=> t) s = alltyvars' t s -- Is this enough?

-- These can sometimes be VERY time-consuming, because they are used by mgu, varBind, etc.
{-# INLINE tyvars  #-}
{-# INLINE tyvars' #-}
tyvars :: Type -> [TyVar]
tyvars ty = tyvars' ty []
tyvars' :: Type -> [TyVar] -> [TyVar]
tyvars' (TV tv)   = (tv:)
tyvars' (TC tc)   = id
tyvars' (TA t u)  = tyvars' t . tyvars' u
tyvars' (u :> t)  = tyvars' t . tyvars' u
tyvars' (u :-> t) = tyvars' t . tyvars' u
tyvars' (u :=> t) = tyvars' t

-- use this instead of QType
maxVarID :: Type -> TyVar
maxVarID (TV tv)   = tv
maxVarID (TC _)    = -1 -- assume non-negative.
maxVarID (TA t u)  = maxVarID t `max` maxVarID u
maxVarID (t :> u)  = maxVarID t `max` maxVarID u
maxVarID (t :-> u) = maxVarID t `max` maxVarID u
maxVarID (_ :=> u) =                  maxVarID u
{- higher-order kindは考えないというか，(*->*)->*と*->*を区別しない（型引数の数のみ考慮する）．その上で，type Kind = Intとする．MemoするときにKindでindexしたいってのと，型引数のKindは推論できないので．

やっぱ正確には，「(*->*)->*と*->*を区別しない」ではなく，「(*->*)->* (higher order kind)を認めない」というべき．
TyApp t uにおいて，u::*を仮定してしまっているので．

data Kind = Star | Kind ::-> Kind deriving (Show, Eq, Ord, Read)
instance Arbitrary Kind where
    arbitrary = sized arbKind

arbKind 0 = return Star
arbKind n = frequency [ (4, return Star),
                        (1, liftM2 (::->) (arbKind (n `div` 2)) (arbKind (n `div` 2))) ]
-}
type Kind = Int

 -- comparison between cs and ds is done in TypeLib, comparing types of different vars.

type TyVar = Int8
type TyCon = TyVar -- TyCon should be the same or bigger than TyVar, because the quantify function converts TyVar into TyCon

type TypeName = String

-- Encoder and Decoder are partly moved to FMType.lhs

-- TyVar should be shared, so it is returned by the decoder.
-- あと、decoListはひだりからみぎにのびていったほうがいいのか？

data Decoder = Dec [TyVar] TyVar
               deriving Show

{-# INLINE normalizeVarIDs #-}
-- FMType，MemoTreeなどでindexするときのために，varIDを0,1,...にroot側から順に正規化する
normalizeVarIDs :: Type -> TyVar -> (Type, Decoder)
normalizeVarIDs ty mx = let decoList = nub $ tyvars ty
                            tup      = zip decoList [0..]
                            encoType = mapTV (\tv -> case lookup tv tup of Just n  -> n) ty
                            len      = genericLength decoList
                            margin   = -- trace ("normalizeVarIDs: mx == "++show mx++ " and len = " ++ show len) $
                                       mx + 1 - len
                        in -- trace ("len = " ++ show len) $ ほとんどのケースで0か1，たまーに2か3
                           (encoType, Dec decoList margin)
normalize ty = fst $ normalizeVarIDs ty (error "undef of normalize")

eqType :: Type -> Type -> Bool
eqType t0 t1 = normalize t0 == normalize t1


-- quantify freezes tyvars into tycons whose IDs are negative.
saferQuantify, quantify, quantify', unquantify :: Type -> Type
saferQuantify = quantify . negUnquantify
negUnquantify (TC i) | i < 0 = TV $ fromIntegral i
negUnquantify (TA t u) = TA (negUnquantify t) (negUnquantify u)
negUnquantify (u :-> t) = negUnquantify u :-> negUnquantify t
negUnquantify (u :> t)  = negUnquantify u :> negUnquantify t
negUnquantify (u :=> t) = error "negUnquantify: applied to types with contexts"
negUnquantify t = t

quantify ty = quantify' (normalize ty)
quantify' (TV iD) = TC $ fromIntegral (-iD-1)
quantify' tc@(TC _) = tc
quantify' (TA t u)  = TA (quantify' t) (quantify' u)
quantify' (u :-> t) = quantify' u :-> quantify' t
quantify' (u :> t)  = quantify' u :>  quantify' t

-- unquantify is used only as a preprocessor of normalize, when used as a preprocessor of quantify. See notes on Nov. 17, 2006.
unquantify (TC tc) | tc < 0 = TV $ fromIntegral (-1-tc)
unquantify (TA t u) = TA (unquantify t) (unquantify u)
unquantify (u :-> t) = unquantify u :-> unquantify t
unquantify (u :> t) = unquantify u :> unquantify t
unquantify (u :=> t) = error "unquantify: applied to types with contexts"
unquantify t = t

{-
mbQuantify ty = return (quantify ty)
-}
{-
encodeSubst :: Encoder -> Subst -> Subst
encodeSubst = plusSubst
-}
unifyFunAp str t u = case uniFunAp t u of Just v -> trace (str ++ ". unify "++show t ++" and "++show u) v
                                          Nothing -> error (str ++ ". unifyFunAp: t = "++show t++", and u = "++show u)
uniFunAp :: MonadPlus m => Type -> Type -> m Type
uniFunAp (a:->r) t = do subst <- mgu (getRet a) (getRet t)
                        return (apply subst r)
uniFunAp (a:=>r) t = uniFunAp (a:->r) t
uniFunAp f t = mzero -- error ("uniFunAp: f = "++show f++" and t = "++show t)


mguFunAp :: MonadPlus m => Type -> Type -> m Type
mguFunAp t0 t1 = trace ("mguFunAp t0 = "++ show t0++", and t1 = "++show t1) $
                 case maxVarID t1 + 1 of mx -> mfa (mapTV (mx+) t0) t1
mfa (a:->r) t = do subst <- mgu a t
--                   return (apply subst r)
                   let retv = (apply subst r)
                   trace ("retv = "++show retv) $ return retv
mfa (a:>r)  t = mfa (a:->r) t -- mguFunAp is only used by PolyDynamic
mfa (a:=>r) t = mfa (a:->r) t -- mguFunAp is only used by PolyDynamic
mfa t@(TV _) _ = return t -- mguFunAp assumes different name spaces
mfa f       t = mzero



pushArgsCPS :: Integral i => (i -> i -> [Type] -> Type -> a) -> [Type] -> Type -> a
pushArgsCPS f = pa 0 0
  where 
        pa c n args (t0:->t1)        = pa c (n+1) (t0:args) t1
        pa c n args (t0:>t1)         = pa c (n+1) (t0:args) t1
        pa c n args (t0:=>t1)        = pa (c+1) n (t0:args) t1 -- So, the arity is not incremented in this case.
        pa c n args retty            = f c n args retty

pushArgs :: [Type] -> Type -> ([Type],Type)
pushArgs = pushArgsCPS (\_ _ a r -> (a,r))

getRet  = pushArgsCPS (\_ _ _ r -> r) undefined
getArgs = pushArgsCPS (\_ _ a _ -> a) []
getNumCxts, getArity :: Integral i => Type -> i
getNumCxts = pushArgsCPS (\c _ _ _ -> c) undefined
getArity   = pushArgsCPS (\_ i _ _ -> i) undefined
getArities :: Integral i => Type -> (i,i)
getArities = pushArgsCPS (\c i _ _ -> (c,i)) undefined
getAritiesRet :: Integral i => Type -> (i,i,Type)
getAritiesRet = pushArgsCPS (\c i _ r -> (c,i,r)) undefined


-- splitArgsCPS :: (Int -> [Type] -> Type -> a) -> Type -> a
-- splitArgsCPS f = pushArgsCPS f []

splitArgs :: Type -> ([Type],Type)
splitArgs = pushArgs []

-- 逆順に積んでいく. :=>も:>もないと仮定．
revSplitArgs :: Integral i => Type -> (i,[Type],Type)
revSplitArgs (t0:->t1) = case revSplitArgs t1 of (n,args,ret) -> (n+1, t0:args, ret)
revSplitArgs t         = (0, [], t)

-- 逆順に積んでいく. :=>も:>もないと仮定．
revGetArgs :: Type -> [Type]
revGetArgs ty = case revSplitArgs ty of (_,ts,_) -> ts

popArgs :: [Type] -> Type -> Type
popArgs = flip (foldl (flip (:->)))

{- ひっくり返さなかったバージョン
popArgs = flip (foldr (:->))
splitArgs (t0:->t1) = let (ts, t) = splitArgs t1 in (t0:ts, t)
splitArgs t         = ([], t)
-}

\end{code}

data "Typed", taken from obsolete/Binding.hs

\begin{code}

data Typed a   = a ::: !Type deriving (Show, Eq, Ord)

typee (a ::: _) = a
typer (_ ::: t) = t

instance Functor Typed where
  fmap f (a ::: t) = f a ::: t

\end{code}

\section{Type inference tools}

\begin{code}

type Subst = [(TyVar,Type)]

showsAssoc [] = id
showsAssoc ((k,v):assocs) = (' ':) . shows k . ("\t|-> "++) . shows v . ('\n':) . showsAssoc assocs

emptySubst = []
unitSubst k e = [(k, e)]


-- substにくわえるときは:>を:->にせねばならないが、apply s (a:>b)はapply s a :> apply s b
match, mgu :: MonadPlus m => Type -> Type -> m Subst

match (l :-> r) (l' :-> r') = match2Ap l r l' r'
{-
match (l :-> r) (l' :> r')  = match2Ap l r l' r'
match (l :> r)  (l' :-> r') = match2Ap l r l' r'
match (l :> r)  (l' :> r')  = match2Ap l r l' r'
-}
match (TA l r) (TA l' r') = match2Ap l r l' r'
match (TV u)   t        = varBind u t
match (TC tc1) (TC tc2) | tc1==tc2 = return emptySubst
match _        _        = mzero

match2Ap l r l' r' = do s1 <- match l l'
                        s2 <- match (apply s1 r) r'
                        return (s2 `plusSubst` s1)

unChin (TA l r)  = TA l $ unChin r
unChin (l :> r)  = unChin l :-> unChin r
unChin (l :-> r) = unChin l :-> unChin r
unChin (l :=> r) =        l :=> unChin r
unChin t         = t

-- mgu t t' = mgu' (toChin t) (toChin t')
mgu (l :-> r) (l' :-> r') = mgu2Ap l r l' r'
#ifdef REALDYNAMIC
-- 起こらないはずだし，効率を考えると....
mgu (l :-> r) (l' :> r')  = mgu2Ap l r l' r'
mgu (l :> r)  (l' :-> r') = mgu2Ap l r l' r'
mgu (l :> r)  (l' :> r')  = mgu2Ap l r l' r'
#endif
mgu (TA l r) (TA l' r') = mgu2Ap l r l' r'
mgu (TV u)   t        = varBind u t
mgu t        (TV u)   = varBind u t
mgu (TC tc1) (TC tc2) | tc1==tc2 = return emptySubst
mgu _        _        = mzero

mgu2Ap l r l' r' = do s1 <- mgu l l'
                      s2 <- mgu (apply s1 r) (apply s1 r')
                      return (s2 `plusSubst` s1)

varBind :: MonadPlus m => TyVar -> Type -> m Subst
varBind _ (_:=>_) = mzero
varBind u t | t == TV u                     = return emptySubst
            | u `elem` (tyvars t)           = mzero
            | otherwise        = return (unitSubst u t)

substOK :: Subst -> Bool
substOK = all (\ (i,ty) -> not (i `elem` (tyvars ty)))


assertsubst :: String -> Subst -> Subst
assertsubst str = \s -> if substOK s then s else error (str ++ ": assertsubst failed. substitution = " ++ show s)
instance Show Type where
-- classesを表示するのがめんどい．最初にまとめなきゃダメ? ReadTypeのところでPrinterでやっときゃ楽だったかも．
    showsPrec _ ty = toString' 0 ty -- The kind info can be incorrect, because we assume *.
        where toString' k (TV i)   = ('a':) . shows i -- can be used to synthesize a generically typed program.
              toString' k (TC i) = ('K':) . shows k . ('I':) . shows i
              toString' k (TA t0 t1)   = showParen True (toString' (k+1) t0 . (' ':) . toString' 0 t1) -- mandatory, just in case.
              toString' k (t0 :=> t1)    = showParen True (toString' 0 t0 . ("=>"++) . toString' 0 t1)
              toString' k (t0 :-> t1)    = showParen True (toString' 0 t0 . ("->"++) . toString' 0 t1)
              toString' k (t0 :> t1)   = showParen True (("(->) "++) . toString' 0 t0 . (' ':) . toString' 0 t1)

plusSubst :: Subst -> Subst -> Subst
s0 `plusSubst` s1 = [(u, -- if u `elem` tvids t then error "u is in t" else
                         --         trace ("in plusSubst, s0="++show s0) $
                         applyCheck s0 t) | (u,t) <- s1] ++ s0


{-
prop_merge t0 t1 u0 u1 = mgu (t0:->t1) (u0:->u1) == ((do s0 <- mgu t0 u0
                                                         s1 <- mgu t1 u1
                                                         symPlus s0 s1) :: [Subst])
-}

-- 循環している場合はplusSubstがillegalになりうる
-- prop_PlusSubst s0 s1 = not (isIllegalSubst s0) && not (isIllegalSubst s1) ==> not (isIllegalSubst (s0 `plusSubst` s1))

-- applyをmapした上で結合しないと，varBindしたときに多段階の循環をチェックできない．
-- s1をやったあとs0をapply

-- applyHoge s t = if isIllegalSubst s then error "Illegal in applyHoge" else apply s t
lookupSubst :: MonadPlus m => Subst -> TyVar -> m Type
lookupSubst subst i = case lookup i subst of Nothing -> mzero
                                             Just x  -> return x

apply :: Subst -> Type -> Type
apply subst ty = apply' ty
                                      where apply' tc@(TC _)    = tc
                                            apply' tg@(TV tv)
                                                = case lookupSubst subst tv of Just tt -> tt
                                                                               Nothing -> tg
                                            apply' (TA t0 t1) = TA (apply' t0) (apply' t1)
                                            apply' (t0:->t1)  = apply' t0 :-> apply' t1
                                            apply' (t0:>t1)   = apply' t0 :>  apply' t1
                                            apply' (t0:=>t1)  = apply' t0 :=> apply' t1

applyCheck subst t = -- trace ("t= " ++ show t ++ " and subst = "++ show subst) $
                     apply subst t


-- moved from ReadType.lhs

{- This used to be Ok, but now I want to use Int8 for TyVar.
strToVarType str
    = TV (bakaHash str)
-- This is Ok, because eventually normalizeVarIDs will be called. (But there can be Int overflow....) Also, when I coded normalizeVarIDs I assumed the tvIDs are small.
bakaHash :: String -> TyVar
bakaHash []     = 0
bakaHash (c:cs) = fromIntegral (ord c) + bakaHash cs * 131
-}
\end{code}
