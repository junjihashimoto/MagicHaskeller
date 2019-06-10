-- 
-- (c) Susumu Katayama
--
\begin{code}
{-# OPTIONS -cpp #-}
module MagicHaskeller.DebMT where
import MagicHaskeller.Types as Types
import MagicHaskeller.TyConLib
import Control.Monad

-- import CoreLang
import Control.Monad.Search.Combinatorial
import MagicHaskeller.PriorSubsts
import Data.Array

import MagicHaskeller.T10((!?))

import Data.List(genericIndex)

import System.IO.Unsafe(unsafeInterleaveIO)

-- type MemoTrie    = MapType (Matrix Possibility)
type Possibility e = (Bag e, Subst, TyVar)
data MapType a
    = MT  {
           tvMT   :: [a],
           tcMT   :: [a],
           genMT  :: [a], -- "forall" stuff
           taMT   :: MapType (MapType a),
           funMT  :: MapType (MapType a)
          }

lookupMT :: MapType a -> Type -> a
-- lookupMT :: MonadPlus m => MapType (m a) -> Type -> (m a)
lookupMT mt (TV tv)    = tvMT  mt `genericIndex` tv
lookupMT mt (TC tc)    | tc < 0  = genMT mt `genericIndex` (-1-tc)
                       | otherwise = tcMT mt `genericIndex` tc
lookupMT mt (TA t0 t1) = lookupMT (lookupMT (taMT mt) t0) t1
lookupMT mt (t0:->t1)  = lookupMT (lookupMT (funMT mt) t0) t1


retrieve :: Decoder -> Subst -> Subst
-- retrieve deco sub = let news = [ (decodeVar deco i, decode deco ty) | (i, ty) <- sub ] in trace ("sub = " ++ show sub ++ " and news = " ++ show news ++ " and deco = " ++ show deco) news
retrieve deco sub = [ (decodeVar deco i, decode deco ty) | (i, ty) <- sub ]

decode :: Decoder -> Type -> Type
decode deco t = mapTV (decodeVar deco) t
decodeVar (Dec tvs margin) tv = case tvs !? tv of Nothing  -> tv+margin
                                                  Just ntv -> ntv

encode   :: Type -> TyVar -> (Type, Decoder)
encode = Types.normalizeVarIDs


mkMT :: TyConLib -> (Type->a) -> MapType a
mkMT tcl f = mkMT' tcl 0 f
mkMT' :: TyConLib -> Kind -> (Type->a) -> MapType a
mkMT' tcl k f = MT tvTree tcTree genTree taTree funTree where
      tcs = snd tcl ! k
      tvTree  = [ f (TV i) | i <- [0..] ]
      tcTree  = [ f (TC i) | i <- [0..] ]
      genTree  = [ f (TC i) | i <- [-1,-2..] ]
      taTree  = mkMT' tcl (k+1) (\t0 -> mkMT tcl (\t1 -> f (TA t0 t1)))
      funTree = if k==0 then mkMT tcl (\t0 -> mkMT tcl (\t1 -> f (t0 :-> t1))) else error "mkMT': the kind of functions must always be *"
mkMTIO :: TyConLib -> (Type -> IO a) -> IO (MapType a)
mkMTIO tcl f = mkMTIO' tcl 0 f
mkMTIO' :: TyConLib -> Kind -> (Type -> IO a) -> IO (MapType a) -- IOのところはMonad m => mでよさそう．実際にはMonadIOでやるかも．
mkMTIO' tcl k f = unsafeInterleaveIO $ liftM5 MT tvTree tcTree genTree taTree funTree where
      tcs = snd tcl ! k
      lazyf = unsafeInterleaveIO . f
      tvTree  = interleaveActions $ map (f . TV) [0..]
      tcTree  = interleaveActions $ map (f . TC) [0..]
      genTree = interleaveActions $ map (f . TC) [-1,-2..]
      taTree  = mkMTIO' tcl (k+1) (\t0 -> mkMTIO tcl  (\t1 -> lazyf (TA t0 t1)))
      funTree = mkMTIO tcl $ if k==0 then (\t0 -> mkMTIO tcl (\t1 -> lazyf (t0 :-> t1))) else error "mkMTIO': the kind of functions must always be *"
--      funTree = if k==0 then mkMTIO tcl (\t0 -> mkMTIO tcl (\t1 -> lazyf (t0 :-> t1))) else error "mkMTIO': the kind of functions must always be *" -- これは間違い．一番外側にunsafeInterleaveIOがないと，kindが0でないinvalidな関数の型も作ろうとしてしまう．

-- I do not add unsafe because I do not understand in what sense unsafeInterleaveIO is unsafe!
interleaveActions :: [IO a] -> IO [a]
interleaveActions = foldr (\x xs -> unsafeInterleaveIO (Control.Monad.liftM2 (:) x xs)) (return []) . map unsafeInterleaveIO
\end{code}
