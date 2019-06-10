-- 
-- (c) Susumu Katayama
--

-- bestのやつだけkeepするやつ．analyticalに適用するとIgorIIと同じになるし，exhaustiveに適用するとDjinnみたいな感じになる．
{-# LANGUAGE MultiParamTypeClasses #-}
module Control.Monad.Search.Best where
import Control.Monad
import Control.Monad.Search.Combinatorial
import Control.Applicative -- necessary for backward compatibility

-- | Unlike 'Matrix', 'Recomp', etc., the 'Best' monad only keeps the best set of results.
--   This makes the analytical synthesis like IgorII, and the exhaustive synthesis like Djinn,
--   i.e., the resulting algorithms are more efficient, but cannot be used for (analytically-)generate-and-test.
data Best a = Result [a] | Delay (Best a) deriving (Show, Read)

-- Note that getBests zero = _|_
getBests :: Best a -> [a]
getBests (Result xs) = xs
getBests (Delay b)   = getBests b

zero = Delay zero

instance Functor Best where
    fmap f (Result xs) = Result $ map f xs
    fmap f (Delay b)   = Delay  $ fmap f b
instance Applicative Best where
    pure x = Result [x]
    (<*>)  = ap
instance Monad Best where
    return = pure
    Result xs >>= f = msum $ map f xs
    Delay  b  >>= f = Delay $ b >>= f
instance Alternative Best where
    empty = mzero
    (<|>) = mplus
instance MonadPlus Best where
    mzero = zero
    Result xs    `mplus` Result ys    = Result $ xs++ys
    b@(Result _) `mplus` Delay  _     = b
    Delay _      `mplus` b@(Result _) = b
    Delay b      `mplus` Delay c      = Delay $ b `mplus` c
instance Delay Best where
    delay = Delay

instance Search  Best where
    fromRc             = fromMx . toMx
    toRc               = toRc   . toMx
    fromMx (Mx xss)    = fromLists xss
    toMx   (Result xs) = Mx $ xs : unMx mzero
    toMx   (Delay  b)  = let Mx xss = toMx b in Mx $ []:xss
    fromDF             = Result

fromLists :: [[a]] -> Best a
fromLists ([]:xss) = Delay (fromLists xss)
fromLists (xs:_)   = Result xs

instance Memoable Best Best where
    tabulate  = id
    applyMemo = id
