-- 
-- (C) Susumu Katayama
--
-- test with ghci -XTemplateHaskell -cpp -DCHTO MagicHaskeller/Analytical.hs
-- Was: monolithic MagicHaskeller.TypedIOPairs
{-# LANGUAGE TemplateHaskell, CPP #-}
module MagicHaskeller.Analytical(
  -- * Analytical synthesizer
  -- | This module provides with analytical synthesis, that only generates expressions without testing.
  --   (So this alone may not be very useful, and for this reason this is not very well-documented.)
  --   In order to generate-and-test over the result of this module, use "MagicHaskeller.RunAnalytical".
  
  -- ** Synthesizers which can be used with any types. 
     get1, getMany, getManyM, getManyTyped, noBK, c, SplicedPrims,
  -- ** Synthesizers which are easier to use that can be used only with types appearing 'MagicHaskeller.CoreLang.defaultPrimitives'
     getOne, synth, synthM, synthTyped
                                ) where

import Data.Char(ord,chr)
import Data.Array
import qualified Data.Map as Map
import Data.Generics
import Language.Haskell.TH

import Control.Monad.Search.Combinatorial
import Control.Monad.Search.Best
import MagicHaskeller.TyConLib
import MagicHaskeller.CoreLang hiding (C)
import MagicHaskeller.PriorSubsts
import MagicHaskeller.ReadTHType(typeToTHType)
import MagicHaskeller.MHTH(decsToExpDecs)

import MagicHaskeller(p1)

import MagicHaskeller.Analytical.Synthesize
#ifdef DEBUG
import MagicHaskeller.Analytical.Debug
#endif


type Strategy = Matrix

type SplicedPrims = ([Dec],[Primitive])

-- | get1 can be used to synthesize one expression. For example,
--
-- >>> putStrLn $ pprint $ get1 $(c [d| f [] = 0; f [a] = 1; f [a,b] = 2 |]) noBK
-- > \a -> let fa (b@([])) = 0
-- >           fa (b@(_ : d)) = succ (fa d)
-- >       in fa a
get1 :: SplicedPrims    -- ^ target function definition by example
        -> SplicedPrims -- ^ background knowledge function definitions by example
        -> Exp
-- get1 target bk = head $ getBests $ getManyM target bk -- This uses Control.Monad.Search.Best. 
get1 target bk = head $ concat $ getMany target bk
-- | getMany does what you expect from its name.
getMany :: SplicedPrims    -- ^ target function definition by example
        -> SplicedPrims -- ^ background knowledge function definitions by example
        -> [[Exp]]
getMany tgt bk = unMx $ toMx (getManyM tgt bk :: Strategy Exp)
getManyM :: (Search m) =>
            SplicedPrims -- ^ target function definition by example
         -> SplicedPrims -- ^ background knowledge function definitions by example
         -> m Exp
getManyM (tgt,pt) (bk,pb) = let ps  = pt++pb
                                tcl = primitivesToTCL ps
                                vl  = primitivesToVL  tcl ps
                            in fmap (exprToTHExp vl) (analyticSynth tcl vl tgt bk)
-- | getManyTyped is a variant of 'getMany' that generates typed expressions.
--   This alone is not very useful, but the type info is required when compiling the expression and is used in "MagicHaskeller.RunAnalytical".
getManyTyped :: SplicedPrims    -- ^ target function definition by example
                -> SplicedPrims -- ^ background knowledge function definitions by example
                -> [[Exp]]
getManyTyped (tgt,pt) (bk,pb) 
  = let ps  = pt++pb
        tcl = primitivesToTCL ps
        vl  = primitivesToVL  tcl ps
        (unit, ty) = analyticSynthAndInfType tcl vl tgt bk
        addSignature thexp = SigE thexp $ typeToTHType tcl ty
    in map (map (addSignature . exprToTHExpLite vl)) $ unMx $ toMx (unit :: Strategy CoreExpr)

noBK :: SplicedPrims
noBK = ([],[])

c :: Q [Dec] -> ExpQ
-- ^ Also, @ $(c [d| ... |]) :: SplicedPrims @
--   'c' is a helper function for extracting some info from the quoted declarations.
c decq = do decs <- decq
            expdecs  <- decsToExpDecs decs
            expPrims <- fmap ListE $ mapM p1 $ cons decs
            return $ TupE [expdecs, expPrims]

cons, conEs, conPs :: (Data a, Typeable a) => a -> [Exp]
cons a = conEs a ++ conPs a
conEs = everything (++) (mkQ [] (\x -> [ e | e@(ConE _)   <- [x]]))
conPs = everything (++) (mkQ [] (\x -> [ ConE name | (ConP name _) <- [x]]))


-- Functions appearing from here are easier to use, but they work only for limited types, included in 'defaultPrimitives'.

getOne :: [Dec] -> [Dec] -> Exp
-- ^ Example:
--
-- >>> runQ [d| f [] = 0; f [a] = 1; f [a,b] = 2 |] >>= \iops -> putStrLn $ pprint $ getOne iops []
-- > \a -> let fa (b@([])) = 0
-- >           fa (b@(_ : d)) = succ (fa d)
-- >       in fa a
getOne iops bk = head $ concat $ synth iops bk
-- getOne iops bk = head $ getBests $ synthM iops bk -- This uses Control.Monad.Search.Best. 
synth :: [Dec] -> [Dec] -> [[Exp]]
synth  iops bk = unMx $ toMx (synthM iops bk :: Strategy Exp)
synthM :: Search m => [Dec] -> [Dec] -> m Exp
synthM iops bk = fmap (exprToTHExp defaultVarLib) (analyticSynth defaultTCL defaultVarLib iops bk)

-- | 'synthTyped' is like synth, but adds the infered type signature to each expression. This is useful for executing the expression at runtime using GHC API.
synthTyped :: [Dec] -> [Dec] -> [[Exp]]
synthTyped iops bk
    = let (unit, ty) = analyticSynthAndInfType defaultTCL defaultVarLib iops bk
          addSignature thexp = SigE thexp $ typeToTHType defaultTCL ty
      in map (map (addSignature . exprToTHExpLite defaultVarLib)) $ unMx $ toMx (unit :: Strategy CoreExpr)
synthesize :: [Dec] -> [Dec] -> [[String]]
synthesize iops bk
    = map (map pprint) $ synth iops bk
