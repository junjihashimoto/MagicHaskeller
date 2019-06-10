{-# LANGUAGE CPP #-}
-- minimal set of definitions for safer use by a server
module MagicHaskeller.Minimal(e, f1E, f1EF, f1EIO, f1EFIO, simpleEF, ProgGenSF, NearEq((~=)), postprocess, ppExcel) where
import MagicHaskeller.LibTH
import MagicHaskeller.LibExcel
import MagicHaskeller.ProgGenSF
import MagicHaskeller.ProgramGenerator
import Data.Typeable
import MagicHaskeller.NearEq(NearEq((~=)))
import Language.Haskell.TH(Exp)
import MagicHaskeller.CoreLang(CoreExpr)

import MagicHaskeller.DebMT(interleaveActions)
#ifdef PAR
import Control.Monad.Par.IO
import Control.Monad.IO.Class(liftIO)
#endif

-- deadline = Just 20000 -- `timeout $ opt $ extractCommon pgsf' is used instead.

f1E :: Typeable a => (Exp->Exp) -> (a -> Bool) -> ProgGenSF -> Bool -> [[Exp]]
f1E  postproc pred pgsf withAbsents = let o = opt $ extractCommon pgsf in map (map (postproc . fst)) $ map (fpartial (timeout o) pred) $ etup undefined pgsf withAbsents
f1EF :: (Filtrable a, Typeable a) => (Exp->Exp) -> (a -> Bool) -> ProgGenSF -> Bool -> [[Exp]]
f1EF postproc pred pgsf withAbsents = let o = opt $ extractCommon pgsf in map (map (postproc . fst)) $ everyF o $ map (fpartial (timeout o) pred) $ etup undefined pgsf withAbsents


e :: Typeable a => (Exp->Exp) -> a -> ProgGenSF -> Bool -> [[Exp]]
e  postproc dmy pgsf withAbsents = let o = opt $ extractCommon pgsf in map (map (postproc . fst . fst))$ etup dmy pgsf withAbsents

f1EIO :: Typeable a => (Exp->Exp) -> (a -> Bool) -> ProgGenSF -> Bool -> IO [[Exp]]
f1EIO  postproc pred pgsf withAbsents 
  = let o = opt $ extractCommon pgsf 
    in fmap (map (map (postproc . fst))) $ interleaveActions $ map (fpartialIO (timeout o) pred) $ etup undefined pgsf withAbsents
--    in fmap (map (map (postproc . fst)) . concat) $ interleaveActions $ map (mapIO $ fpartialIO (timeout o) pred) $ chopN 2 $ etup undefined pgsf withAbsents
chopN n xs = map (take n) $ iterate (drop n) xs -- e.g. chopN 2 ['a'..] == ["ab","cd", ....

--    in fmap (map (map (postproc . fst))) $ mapIO (fpartialIO (timeout o) pred) $ etup undefined pgsf withAbsents
--    in fmap (map (map (postproc . fst))) $ runParIO $ mapParIO (fpartialParIO (timeout o) pred) $ etup undefined pgsf withAbsents
--    in fmap (map (map (postproc . fst))) $ interleaveActions $ map (runParIO . fpartialParIO (timeout o) pred) $ etup undefined pgsf withAbsents
--    in fmap (map (map (postproc . fst))) $ runParIO $ mapParIO (liftIO . fpartialIO (timeout o) pred) $ etup undefined pgsf withAbsents
f1EFIO :: (Filtrable a, Typeable a) => (Exp->Exp) -> (a -> Bool) -> ProgGenSF -> Bool -> IO [[Exp]]
f1EFIO postproc pred pgsf withAbsents 
  = let o = opt $ extractCommon pgsf 
    in fmap (map (map (postproc . fst)) . everyF o) $ interleaveActions $ map (fpartialIO (timeout o) pred) $ etup undefined pgsf withAbsents

simpleF1EFIO :: (Filtrable a, Typeable a) => (a -> Bool) -> ProgGenSF -> Bool -> IO [[(CoreExpr, a)]]
simpleF1EFIO pred pgsf withAbsents 
  = let o = opt $ extractCommon pgsf 
    in fmap (everyF o) $ interleaveActions $ map (ftotalIO (timeout o) pred) $ everyACE pgsf withAbsents

simpleEF :: (Filtrable a, Typeable a) => ProgGenSF -> Bool -> [[(CoreExpr,a)]]
simpleEF pgsf withAbsents 
  = let o = opt $ extractCommon pgsf 
    in everyF o $ everyACE pgsf withAbsents
