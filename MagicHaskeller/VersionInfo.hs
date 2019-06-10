{-# LANGUAGE TemplateHaskell, CPP #-}
{-# OPTIONS_GHC -fforce-recomp #-}
-- Recompilation is needed to obtain the correct build time.
module MagicHaskeller.VersionInfo where
import Data.Time
import Language.Haskell.TH
#ifdef CABAL
import Paths_MagicHaskeller(version)
import Data.Version(showVersion)
#endif

versionInfo, mhVersion, ghcVersion, now :: String
versionInfo = mhVersion ++ " built with GHC-" ++ ghcVersion ++ " at " ++ now
#ifdef CABAL
mhVersion = showVersion version
#else
mhVersion = ""
#endif
ghcVersion = case __GLASGOW_HASKELL__ `divMod` 100 of (b,s) -> shows b $ '.' : show s

now = $(runIO getCurrentTime >>= \t -> return (LitE $ StringL $ show t)) -- This requires the -fforce-recomp flag in order to be correct.
