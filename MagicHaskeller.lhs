-- 
-- (c) Susumu Katayama
--

\begin{code}

{-# LANGUAGE TemplateHaskell, CPP, MagicHash, Rank2Types #-}
module MagicHaskeller(
       -- * Re-exported modules
       -- | This library implicitly re-exports the entities from
       --   @module Language.Haskell.TH as TH@ and @module Data.Typeable@ from the Standard Hierarchical Library of Haskell.
       --   Please refer to their documentations on types from them --- in this documentation, types from TH are all qualified and the only type used from @module Typeable@ is Typeable.Typeable. Other types you had never seen should be our internal representation.
       module TH, module Typeable,

       -- * Setting up your synthesis
       -- | Before synthesis, you have to define at least one program generator algorithm (or you may define one once and reuse it for later syntheses).
       --   Other parameters are memoization depth and time out interval, which have default values.
       --   You may elect either to set those values to the \'global variables\' using \'@set@*\' functions (i.e. functions whose names are prefixed by @set@), or hand them explicitly as parameters.

       -- ** Class for program generator algorithms
       -- | Please note that @ConstrL@ and @ConstrLSF@ are obsoleted and users are expected to use the 'constrL' option in 'Option'.
       ProgramGenerator,
       ProgGen, ProgGenSF, ProgGenSFIORef,

       -- ** Functions for creating your program generator algorithm
       -- | You can set your primitives like, e.g., @'setPrimitives' $('p' [| ( (+) :: Int->Int->Int, 0 :: Int, \'A\', [] :: [a] ) |])@,
       --   where the primitive set is consisted of @(+)@ specialized to type @Int->Int->Int@, @0@ specialized to type @Int@, 
       --   @ \'A\' @ which has monomorphic type @Char@, and @[]@ with polymorphic type @[a]@.
       --   As primitive components one can include any variables and constructors within the scope. 
       --   However, because currently ad hoc polymorphism is not supported by this library, you may not write
       --   @'setPrimitives' $('p' [| (+) :: Num a => a->a->a |])@.
       --   Also, you have to specify the type unless you are using a primitive component whose type is monomorphic and instance of 'Data.Typeable.Typeable'
       --   (just like when using the dynamic expression of Concurrent Clean), and thus
       --   you may write @'setPrimitives' $('p' [| \'A\' |])@,
       --   while you have to write @'setPrimitives' $('p' [| [] :: [a] |])@ instead of @'setPrimitives' $('p' [| [] |])@.
       p, setPrimitives, mkPG, mkPGSF, setPG,

       -- | Older versions prohibited data types holding functions such as @[a->b]@, @(Int->Char, Bool)@, etc. just for efficiency reasons.
       --   They are still available if you use 'mkMemo' and 'mkMemoSF' instead of 'mkPG' and 'mkPGSF' respectively, though actually this limitation does not affect the efficiency a lot.
       --   (NB: recently I noticed that use of 'mkMemo' or 'mkMemoSF' might not improve the efficiency of generating lambda terms at all, though when I generated combinatory expressions it WAS necessary.
       --   In fact, I mistakenly turned this limitation off, and 'mkMemo' and 'mkMemoSF' were equivalent to 'mkPG' and 'mkPGSF', but I did not notice that....)
       mkMemo, mkMemoSF,

       -- | @mkMemo075@ enables some more old good optimization options used until Version 0.7.5, including guess on the primitive functions.
       --   It is for you if you prefer speed, but the result can be non-exhaustive if you use it with your own LibTH.hs.
       --   Also, you need to use the prefixed |(->)| in order for the options to take effect. See LibTH.hs for examples.
       mkPG075, mkMemo075,

       -- | 'mkPGOpt' can be used along with its friends instead of 'mkPG' when the search should be fine-tuned.
       mkPGOpt, 
       
       -- | 'mkPGX' and 'mkPGXOpt' can be used instead of 'mkPG' and 'mkPGOpt' if you want to prioritize the primitives. 
       --   They take a list of lists of primitives as an argument, whose first element is the list of primitives with the greatest priority, 
       --   second element the second greatest priority, and so on.
       mkPGX, mkPGXOpt,
       
       mkPGXOpts, updatePGXOpts, updatePGXOptsFilt,
       Options, Opt(..), options, MemoType(..),

       -- | These are versions for 'ProgramGeneratorIO'.
       mkPGIO, mkPGXOptIO,

#ifdef HASKELLSRC
       -- ***  Alternative way to create your program generator algorithm
       -- | 'load' and 'f' provides an alternative scheme to create program generator algorithms.
       load, f,
#endif

       -- ** Memoization depth
       -- | NB: 'setDepth' will be obsoleted. It is provided for backward compatibility, but
       --   not exactly compatible with the old one in that its result will not affect the behavior of 'everything', etc., which explicitly take a 'ProgramGenerator' as an argument.
       --   Also, in the current implementation, the result of 'setDepth' will be overwritten by setPrimitives.
       --   Use 'memodepth' option instead.
       setDepth,

       -- ** Time out
       -- | NB: 'setTimeout' and 'unsetTimeout' will be obsoleted. They are provided for backward compatibility, but
       --   not exactly compatible with the old ones in that their results will not affect the behavior of 'everything', etc., which explicitly take a 'ProgramGenerator' as an argument.
       --   Also, in the current implementation, the result of 'setTimeout' and 'unsetTimeout' will be overwritten by setPrimitives.
       --   Use 'timeout' option instead.
       --
       --   Because the library generates all the expressions including those with non-linear recursions, you should note that there exist some expressions which take extraordinarily long time. (Imagine a function that takes an integer n and increments 0 for 2^(2^n) times.)
       --   For this reason, time out is taken after 0.02
       --   second since each invocation of evaluation by default. This default behavior can 
       --   be overridden by the following functions.
       setTimeout, unsetTimeout,

       -- ** Defining functions automatically
       -- | In this case \"automatically\" does not mean \"inductively\" but \"deductively using Template Haskell\";)
       define, Everything, Filter, Every, EveryIO,

       -- * Generating programs
       -- | (There are many variants, but most of the functions here just filter 'everything' with the predicates you provide.)
       --
       --   Functions suffixed with \"F\" (like 'everythingF', etc.) are filtered versions, where their results are filtered to totally remove semantic duplications. In general they are equivalent to applying 'everyF' afterwards.
       --   (Note that this is filtration AFTER the program generation, unlike the filtration by using 'ProgGenSF' is done DURING program generation.)

       -- ** Quick start
       findOne, printOne, printAll, printAllF, io2pred,

       -- ** Incremental filtration
       -- | Sometimes you may want to filter further after synthesis, because the predicate you previously provided did not specify
       --   the function enough. The following functions can be used to filter expressions incrementally.
       filterFirst, filterFirstF, filterThen, filterThenF, fp,

       -- ** Expression generators
       -- | These functions generate all the expressions that have the type you provide.
       getEverything, everything, everythingM, everythingIO, unifyable, matching, getEverythingF, everythingF, unifyableF, matchingF, everyACE,

       -- ** Utility to filter out equivalent expressions
       everyF,

       -- ** Unility to get one value easily
       stripEvery,

       -- ** Pretty printers
       pprs, pprsIO, pprsIOn, lengths, lengthsIO, lengthsIOn, lengthsIOnLn, printQ,

       -- * Internal data representation
       -- | The following types are assigned to our internal data representations.
       Primitive, HValue(HV),

#ifdef PAR
       fpartialParIO, mapParIO,
#endif
       -- other stuff which will not be documented by Haddock
       unsafeCoerce#, {- unifyablePos, -} exprToTHExp, trToTHType, printAny, p1, Filtrable, zipAppend, mapIO, fpIO, fIO, fpartial, fpartialIO, ftotalIO, etup, mkCurriedDecls
      ) where

import Data.Generics(everywhere, mkT, Data)

import Data.Array.IArray
import MagicHaskeller.CoreLang
import Language.Haskell.TH as TH
#ifdef HASKELLSRC
import MagicHaskeller.ReadHsType(readHsTypeSigs)
#endif
import MagicHaskeller.TyConLib
import qualified Data.Map as Map
import Data.Char
import Control.Monad(mplus)


import MagicHaskeller.Types as Types

import MagicHaskeller.T10(mergesortWithBy)

import MagicHaskeller.ProgGen(ProgGen(PG))
import MagicHaskeller.ProgGenSF(ProgGenSF, PGSF)
import MagicHaskeller.ProgGenSFIORef(ProgGenSFIORef, PGSFIOR)
-- import MagicHaskeller.ProgGenLF(ProgGenLF)
-- import MagicHaskeller.ProgGenXF(ProgGenXF)
import MagicHaskeller.ProgramGenerator
import MagicHaskeller.Options(Opt(..), options)
import Control.Monad.Search.Combinatorial -- This should all be exposed?
import Data.Typeable as Typeable
import System.IO.Unsafe(unsafePerformIO)
import Data.IORef
import GHC.Exts(unsafeCoerce#)
-- import Maybe(fromJust)
import System.IO
#ifdef TFRANDOM
import System.Random.TF(seedTFGen,TFGen)
#else
import System.Random(mkStdGen,StdGen)
#endif
import MagicHaskeller.MHTH
import MagicHaskeller.TimeOut

import MagicHaskeller.ReadTHType
import MagicHaskeller.ReadTypeRep(trToType, trToTHType)
import MagicHaskeller.MyDynamic
import qualified MagicHaskeller.PolyDynamic as PD
import MagicHaskeller.Expression
import MagicHaskeller.Classify
import MagicHaskeller.ClassifyDM(filterDM)
import MagicHaskeller.Classification(unsafeRandomTestFilter, Filtrable)
import MagicHaskeller.Instantiate(mkRandTrie)
import MagicHaskeller.MemoToFiles(MemoType(..))

import Data.List(genericLength, transpose)

-- import Control.Concurrent.ParallelIO(parallelInterleaved)
import MagicHaskeller.DebMT(interleaveActions)
#ifdef PAR
import Control.Monad.Par.IO
import Control.Monad.Par.Class
import Control.Monad.IO.Class(liftIO)
#endif

import Control.Concurrent.MVar
import Control.Concurrent

import Debug.Trace
\end{code}

\begin{code}
mkCurriedDecls :: String -> ExpQ -> ExpQ -> DecsQ
mkCurriedDecls tag funq eq = do e <- eq
                                fun <- funq
                                case e of TupE es -> fmap concat $ mapM (mcd fun) es
                                          _       -> mcd fun e
   where mcd :: Exp -> Exp -> DecsQ
         mcd fun v@(VarE name) = let nb = nameBase name
                                 in return [ValD (VarP $ mkName $ nb++tag) (NormalB (AppE fun v)) []]
--   where mcd :: Exp -> DecsQ
--         mcd v@(VarE name) = let nb = nameBase name
--                             in [d| $(return $ VarP $ mkName $ nb++tag) = $(funq) $(return v) |]


-- "MemoDeb" name should be hidden, or maybe I could rename it.

-- | 'define' eases use of this library by automating some function definitions. For example, 
--
-- > $( define ''ProgGen "Foo" (p [| (1 :: Int, (+) :: Int -> Int -> Int) |]) )
--
-- is equivalent to 
--
-- > memoFoo :: ProgGen
-- > memoFoo = mkPG (p [| (1 :: Int, (+) :: Int -> Int -> Int) |])
-- > everyFoo :: Everything
-- > everyFoo = everything memoFoo
-- > filterFoo :: Filter
-- > filterFoo pred = filterThen pred everyFoo
--
-- If you do not think this function reduces the number of your keystrokes a lot, you can do without it.
define   :: TH.Name -> String -> TH.ExpQ -> TH.Q [TH.Dec]
define mn name pq = pq >>= \prims ->
                              return [ SigD (mkName ("memo"++name)) (ConT mn),
                                       ValD (VarP (mkName ("memo"++name))) (NormalB (AppE (VarE (mkName "mkPG")) prims -- (VarE (mkName "prims"))
                                                                                                                   )) [],
                                       SigD (mkName ("every"++name)) (ConT (mkName "Everything")),
                                       ValD (VarP (mkName ("every"++name))) (NormalB (VarE (mkName "everything") `AppE` VarE (mkName ("memo"++name)))) [],
                                       SigD (mkName ("filter"++name)) (ConT (mkName "Filter")),
                                       ValD (VarP (mkName ("filter"++name))) (NormalB ((VarE (mkName "flip")  `AppE` VarE (mkName "filterThen")) `AppE` VarE (mkName ("every"++name)))) [] ]
type Every a    = [[(TH.Exp,a)]]
type EveryIO a  = Int  -- query depth
                  -> IO [(TH.Exp, a)]
type Everything = forall a. Typeable a => Every a
type Filter     = forall a. Typeable a => (a->Bool) -> IO (Every a)

{- Because the left hand side is not TH.Exp, we cannot splice directly there.
initialize name depth prims = [d| { $(return (VarE (mkName ("memo"++name)))) = mkPG $prims;
                                    $(return (VarE (mkName ("every"++name)))) :: Everything;
                                    $(return (VarE (mkName ("every"++name)))) = everything $(return (LitE (NumL depth))) $(return (VarE (mkName ("memo"++name)))); } |]
-}

{- It is unlikely that mkMTH will ever be used, and seemingly my version of haddock dislikes TH.
-- One could write, for example, $(mkMTH $15 [| ( 0::Int, succ, nat_para, [] ) |] ),
-- but I am not sure if this style using mkMTH will ever be used.
mkMTH :: TH.ExpQ -> TH.ExpQ -> TH.ExpQ
mkMTH n leq = [| mkMD $n $(m leq) |]
-}

-- Rather, one could write, e.g.,
-- mkMD 15 $(p [|  ( 0::Int, succ::Int->Int, nat_para, [] :: [a])  |] )

-- | 'p' is used to convert your primitive component set into the internal form.
p :: TH.ExpQ -- ^ Quote a tuple of primitive components here.
     -> TH.ExpQ -- ^ This becomes @[Primitive]@ when spliced.
p eq = eq >>= \e -> case e of TupE es -> (return . ListE) =<< (mapM p1 es)
                              _       -> (return . ListE . return) =<< p1 e      -- This default pattern should also be defined, because it takes two (or more) to tuple!
p1 :: TH.Exp -> TH.ExpQ
p1 (SigE e ty) = p1' (SigE e $ useArrowT ty) e ty
p1 e@(ConE name)  = do
#if __GLASGOW_HASKELL__ < 800
                       DataConI _ ty _ _ <- reify name
#else                                            
                       DataConI _ ty _   <- reify name
#endif                                            
                       p1' e e ty
p1 e@(VarE name)  = do
#if __GLASGOW_HASKELL__ < 800
                       VarI _ ty _ _ <- reify name
#else
                       VarI _ ty _   <- reify name
#endif
                       p1' e e ty
p1 e              = [| (HV (unsafeCoerce# $(return e)), $(expToExpExp e), trToTHType (typeOf $(return e))) |]

p1' se e ty = [| (HV (unsafeCoerce# $(return se)), $(expToExpExp e), $(typeToExpType ty)) |]

useArrowT :: TH.Type -> TH.Type
useArrowT = everywhere (mkT uAT)
uAT (ConT name) | nameBase name == "(->)" = ArrowT
uAT t = t
{- 
  Strangely enough, GHC-7.10 (at least, GHCi, version 7.10.2.20150906) rejects (ConT GHC.Prim.(->)), while reading "(->)" to (ConT GHC.Prim.(->))

Prelude> :m +Language.Haskell.TH
Prelude Language.Haskell.TH> runQ [t| (->) Int Bool |] >>= print
AppT (AppT (ConT GHC.Prim.(->)) (ConT GHC.Types.Int)) (ConT GHC.Types.Bool)
Prelude Language.Haskell.TH> ((/=0) :: $([t| (->) Int Bool |])) 3

<interactive>:5:13:
    Illegal type constructor or class name: ‘(->)’
    When splicing a TH type: GHC.Prim.(->) GHC.Types.Int GHC.Types.Bool
    In the splice: $([t| (->) Int Bool |])
Prelude Language.Haskell.TH> ((/=0) :: $([t| (->) Int|]) Bool) 3

<interactive>:7:13:
    Illegal type constructor or class name: ‘(->)’
    When splicing a TH type: GHC.Prim.(->) GHC.Types.Int
    In the splice: $([t| (->) Int |])
Prelude Language.Haskell.TH> ((/=0) :: $([t| Int -> Bool |])) 3
True

  This is as opposed to the description in 
     https://downloads.haskell.org/~ghc/latest/docs/html/libraries/template-haskell-2.10.0.0/src/Language-Haskell-TH-Syntax.html#line-1414
  saying
     But if the original HsSyn used prefix application, we won't use
     these special TH constructors.  For example
       [] t              ConT "[]" `AppT` t
       (->) t            ConT "->" `AppT` t
     In this way we can faithfully represent in TH whether the original
     HsType used concrete syntax or not.
  So this may be a bug, introduced when making TH more pedantic.

  Reading "(->)" to (ConT GHC.Prim.(->)) is a good news for MagicHaskeller which abuses (->) to indicate constructor consumption.
  In the case that the distinction between prefixed (->) and the infixed -> is obsoleted, we can still use   
     type (:-->) = (->) 
  but then, we need to change more code.
-}

-- nameToExpName :: TH.Name -> TH.Exp
-- nameToExpName = strToExpName . showName
-- strToExpName str = AppE (VarE (mkName "mkName")) (LitE (StringL str))

{- not used any longer
{- This should work in theory, but Language.Haskell.TH.pprint has a bug and it does not print parentheses....
pprintType (ForallT _ _ ty) = pprint ty
pprintType ty               = pprint ty
-}
-- 'pprintType' is a workaround for the problem that @Language.Haskell.TH.pprint :: Type -> String@ does not print parentheses correctly.
-- (try @Language.Haskell.TH.runQ [t| (Int->Int)->Int |] >>= \e -> putStrLn (pprint e)@ in your copy of GHCi.)
-- The implementation here is not so pretty, but that's OK for my purposes. Also note that 'pprintType' ignores foralls.
pprintType (ForallT _ [] ty) = pprintType ty
pprintType (ForallT _ _  ty) = error "Type classes are not supported yet. Sorry...."
pprintType (VarT name)      = pprint name
pprintType (ConT name)      = pprint name
pprintType (TupleT n)       = tuplename n
pprintType ArrowT           = "(->)"
pprintType ListT            = "[]"
pprintType (AppT t u)       = '(' : pprintType t ++ ' ' : pprintType u ++ ")"
-- The problem of @Language.Haskell.TH.pprint :: Type -> String@ is now fixed at the darcs HEAD.
-}

primitivesp :: TyConLib -> [[Primitive]] -> [[Typed [CoreExpr]]]
primitivesp tcl pss = dynamicsp (map (map (primitiveToDynamic tcl)) pss)
dynamicsp :: [[PD.Dynamic]] -> [[Typed [CoreExpr]]]
dynamicsp pss
    = let ixs = scanl (+) 0 $ map genericLength pss
      in zipWith (\ix -> mergesortWithBy (\(x:::t) (y:::_) -> (x++y):::t) (\(_:::t) (_:::u) -> compare t u) .
                         zipWith (\ n d -> [if expIsAConstr $ PD.dynExp d then PrimCon n else Primitive n] ::: toCxt (numCxts $ PD.dynExp d) (PD.dynType d)) [ix..]) ixs pss






-- うまくいかん場合は map (filtTMxAEs cmn) . の部分を取り除いてやってみるべし．


filtTCEsss :: Common -> Int -> [[Typed [CoreExpr]]] -> [[Typed [CoreExpr]]]
filtTCEsss cmn depth = tMxAEsToTCEsss depth . map (filtTMxAEs cmn) . tMxCEsToTMxAEs (reducer cmn) . tCEsssToTMxCEs  -- ProgramGenerator.reducer :: Common -> CoreExpr -> Dynamic はVarLibの情報をCommonから抽出する．
-- filtTCEsss cmn depth = tMxAEsToTCEsss depth . {- map (filtTMxAEs cmn) . -} tMxCEsToTMxAEs (reducer cmn) . tCEsssToTMxCEs  -- ProgramGenerator.reducer :: Common -> CoreExpr -> Dynamic はVarLibの情報をCommonから抽出する．
-- filtTCEsss cmn depth = id -- これはさすがにうまく行く．
-- filtTCEsss cmn depth = tMxAEsToTCEsss depth . tCEsssToTMxCEs -- depthが十分ならうまく行く．
tCEsssToTMxCEs :: [[Typed [CoreExpr]]] -> [Typed (Matrix CoreExpr)]
tCEsssToTMxCEs = mergesortWithBy (\(x:::t) (y:::_) -> (x `mplus` y):::t) (\(_:::t) (_:::u) -> compare t u) . -- dynamicspにも同じ部分があるので名前をつけるべき．
                 concat .
                 zipWith (\d ts -> map (fmap (\ces -> Mx $ replicate d [] ++ ces : repeat [])) ts) [0..]
tMxCEsToTMxAEs :: (CoreExpr->Dynamic) -> [Typed (Matrix CoreExpr)] -> [Typed (Matrix AnnExpr)]
tMxCEsToTMxAEs reduce = map (fmap (fmap (toAnnExpr reduce)))
filtTMxAEs :: Common -> Typed (Matrix AnnExpr) -> Typed (Matrix AnnExpr)
filtTMxAEs cmn (m ::: ty) = fromDB (MagicHaskeller.ClassifyDM.filterDM cmn ty (fromMx m)) ::: ty
tMxAEsToTCEsss :: Expression e => Int -> [Typed (Matrix e)] -> [[Typed [CoreExpr]]]
tMxAEsToTCEsss dep tmxaes = map (filter (not . null . typee)) $ transpose [ [ map toCE aes ::: ty | aes <- take dep aess ] | Mx aess ::: ty <- tmxaes ]



-- See if the argument is a constructor expression.
expIsAConstr (ConE _)  = True
expIsAConstr (LitE _)  = True
expIsAConstr (ListE _) = True
expIsAConstr (TupE  _) = True
expIsAConstr (AppE e _) = expIsAConstr e
expIsAConstr (InfixE _ (ConE _) _) = True
expIsAConstr _ = False

numCxts (VarE nm) = case nameBase nm of 'b':'y':d:'_':_    | isDigit d -> digitToInt d
                                        '-':'-':xs@('#':_)             -> length $ takeWhile (=='#') xs
                                        _                              -> 0
numCxts _         = 0
toCxt 0 t = t
toCxt n (t :-> u) = t :=> toCxt (n-1) u

primitivesc :: TyConLib -> [Primitive] -> [Typed [CoreExpr]]
primitivesc tcl ps = dynamicsc (map (primitiveToDynamic tcl) ps)
dynamicsc :: [PD.Dynamic] -> [Typed [CoreExpr]]
dynamicsc ps = mergesortWithBy (\(x:::t) (y:::_) -> (x++y):::t) (\(_:::t) (_:::u) -> compare t u) $
                           map (\ dyn -> [Context $ Dict dyn] ::: {- toCxt (numCxts e) -} PD.dynType dyn) ps

mkPG :: ProgramGenerator pg => [Primitive] -> pg
mkPG   = mkPGX [] . (:[])
mkPGX :: ProgramGenerator pg => [Primitive] -> [[Primitive]] -> pg
mkPGX   = mkPG' True
-- ^ 'mkPG' is defined as:
--
-- > mkPG prims = mkPGSF (mkStdGen 123456) (repeat 5) prims prims

mkMemo :: ProgramGenerator pg => [Primitive] -> pg
mkMemo = mkPG' False [] . (:[])
mkPG' :: ProgramGenerator pg => Bool -> [Primitive] -> [[Primitive]] -> pg
mkPG' cont classes tups = case mkCommon options{contain=cont} totals totals depths of cmn -> mkTrie cmn (primitivesc (tcl cmn) classes) (primitivesp (tcl cmn) tups)
        where totals = concat tups ++ classes
              depths = mkDepths tups ++ map (const 0) classes

-- | 'mkPGSF' and 'mkMemoSF' are provided mainly for backward compatibility. These functions are defined only for the 'ProgramGenerator's whose names end with @SF@ (i.e., generators with synergetic filtration).
--   For such generators, they are defined as:
--
-- > mkPGSF   gen nrnds optups tups = mkPGOpt (options{primopt = Just optups, contain = True,  stdgen = gen, nrands = nrnds}) tups
-- > mkMemoSF gen nrnds optups tups = mkPGOpt (options{primopt = Just optups, contain = False, stdgen = gen, nrands = nrnds}) tups

mkPGSF,mkMemoSF :: ProgramGenerator pg =>
#ifdef TFRANDOM
           TFGen
#else
           StdGen
#endif
        -> [Int] -- ^ number of random samples at each depth, for each type.
        -> [Primitive] 
        -> [Primitive] 
        -> [Primitive] -> pg
mkPGSF   = mkPGSF' True
mkMemoSF = mkPGSF' False
mkPGSF' cont gen nrnds classes optups tups = mkPGOpt (options{primopt = Just [optups], contain = cont, stdgen = gen, nrands = nrnds}) classes tups
--   Currently only the pg==ConstrLSF case makes sense. ってのは，optupsのみに関する話で，rndsは関係ない．

mkPG075 :: ProgramGenerator pg => [Primitive] -> [Primitive] -> pg
mkPG075 = mkPGOpt (options{primopt = Nothing, contain = True, guess = True})
mkMemo075 :: ProgramGenerator pg => [Primitive] -> [Primitive] -> pg
mkMemo075 = mkPGOpt (options{primopt = Nothing, contain = False, guess = True})

mkPGOpt :: ProgramGenerator pg => Options -> [Primitive] -> [Primitive] -> pg
mkPGOpt opt classes prims = mkPGXOpt opt classes [] [prims] []
mkPGXOpt :: ProgramGenerator pg => Options -> [Primitive] -> [(Primitive,Primitive)] -> [[Primitive]] -> [[(Primitive,Primitive)]] -> pg
mkPGXOpt  = mkPGXOpts mkTrieOpt
mkPGIO    :: ProgramGeneratorIO pg => [Primitive] -> [Primitive] -> IO pg
mkPGIO classes prims = mkPGXOptIO options classes [] [prims] []
mkPGXOptIO :: ProgramGeneratorIO pg => Options -> [Primitive] -> [(Primitive,Primitive)] -> [[Primitive]] -> [[(Primitive,Primitive)]] -> IO pg
mkPGXOptIO = mkPGXOpts mkTrieOptIO

mkPGXOpts :: (Common -> [Typed [CoreExpr]] -> [[Typed [CoreExpr]]] -> [[Typed [CoreExpr]]] -> a)
          -> Options -> [Primitive] -> [(Primitive,Primitive)] -> [[Primitive]] -> [[(Primitive,Primitive)]] -> a
mkPGXOpts mkt opt classes partclasses prims partprims
    = let cmn = initCommon opt (classes ++ concat prims ++ map fst (partclasses ++ concat partprims))
          ptd = primitiveToDynamic (tcl cmn)
      in updatePGXOpts mkt (primopt opt)
                           [ ptd cl | cl <- classes ]
                           [ (ptd tot, ptd part) | (tot, part) <- partclasses ]
                           [ [ ptd p | p <- ps ] | ps <- prims ]
                           [ [ (ptd tot, ptd part) | (tot, part) <- pps ] | pps <- partprims ]
                           cmn
{-
mkPGXOpts mkt opt classes partclasses prims partprims = case mkCommon opt (concat totalss ++ totalclss) (concat partialss ++ partialclss) (mkDepths totalss ++ map (const 0) totalclss) of cmn -> mkt cmn (primitivesc (tcl cmn) totalclss) (primitivesp (tcl cmn) primsOpt) (primitivesp (tcl cmn) totalss)
    where primsOpt   = case primopt opt of Nothing -> prims
                                           Just po -> po
          (tot, part) = unzip $ map unzip partprims
          totalss     = zipAppend prims tot
          partialss   = zipAppend prims part
          (totc,partc)= unzip partclasses
          totalclss   = classes ++ totc
          partialclss = classes ++ partc
-}
updatePGXOpts :: (Common -> [Typed [CoreExpr]] -> [[Typed [CoreExpr]]] -> [[Typed [CoreExpr]]] -> a)
              -> Maybe [[Primitive]] -> [PD.Dynamic] -> [(PD.Dynamic,PD.Dynamic)] -> [[PD.Dynamic]] -> [[(PD.Dynamic,PD.Dynamic)]] -> Common -> a
updatePGXOpts = uPGXO (const dynamicsp)
updatePGXOptsFilt :: Int -> (Common -> [Typed [CoreExpr]] -> [[Typed [CoreExpr]]] -> [[Typed [CoreExpr]]] -> a)
              -> Maybe [[Primitive]] -> [PD.Dynamic] -> [(PD.Dynamic,PD.Dynamic)] -> [[PD.Dynamic]] -> [[(PD.Dynamic,PD.Dynamic)]] -> Common -> a
updatePGXOptsFilt dep = uPGXO (\cmn dynss -> -- trace ("dynamicsp dynss = "++show (dynamicsp dynss) ++ "\nand the result is "++show (filtTCEsss cmn dep $ dynamicsp dynss)) $
                                             filtTCEsss cmn dep $ dynamicsp dynss)
uPGXO :: (Common -> [[PD.Dynamic]] -> [[Typed [CoreExpr]]]) ->
               (Common -> [Typed [CoreExpr]] -> [[Typed [CoreExpr]]] -> [[Typed [CoreExpr]]] -> a)
              -> Maybe [[Primitive]] -> [PD.Dynamic] -> [(PD.Dynamic,PD.Dynamic)] -> [[PD.Dynamic]] -> [[(PD.Dynamic,PD.Dynamic)]] -> Common -> a
uPGXO dyp mkt mbpo classes partclasses prims partprims c = case updateCommon (concat totalss ++ totalclss) (concat partialss ++ partialclss) (mkDepths totalss ++ map (const 0) totalclss) c of cmn -> mkt cmn (dynamicsc totalclss) (alt cmn) (dyp cmn totalss) -- dyp c? vlをうまく同期させねば．
    where alt cmn = case mbpo of Nothing -> dyp cmn totalss -- dyp c?
                                 Just po -> primitivesp (tcl c) po
          (tot, part) = unzip $ map unzip partprims
          totalss     = zipAppend prims tot
          partialss   = zipAppend prims part
          (totc,partc)= unzip partclasses
          totalclss   = classes ++ totc
          partialclss = classes ++ partc

mkDepths :: [[a]] -> [Int]
mkDepths = concat . zipWith (\i xs -> map (const i) xs) [0..]

setPG :: ProgGen -> IO ()
setPG = writeIORef refmemodeb

-- | @setPrimitives@ creates a @ProgGen@ from the given set of primitives using the current set of options, and sets it as the current program generator. 
--   It used to be equivalent to @setPG . mkPG@ which overwrites the options with the default, but it is not now.
setPrimitives :: [Primitive] -> [Primitive] -> IO ()
setPrimitives classes tups = do PG (_,_,_,cmn) <- readIORef refmemodeb
                                setPG $ mkPGOpt ((opt cmn){primopt=Nothing}) classes tups
-- setPrimitives tups = writeIORef refmemodeb (mkPG tups) -- This definition overwrites the old configuration.

-- zipAppend is like zipWith (++), but the length of the resulting list is the same as that of the longer of the two list arguments.
zipAppend :: [[a]] -> [[a]] -> [[a]]
zipAppend []       yss      = yss
zipAppend xss      []       = xss
zipAppend (xs:xss) (ys:yss) = (xs++ys) : zipAppend xss yss

#ifdef HASKELLSRC
-- | 'load' loads a component library file.
load :: FilePath
     -> TH.ExpQ     -- ^ This becomes @[Primitive]@ when spliced.
load fp = do str <- runIO $ readFile fp
             f str
-- | f is supposed to be used by load, but not hidden.
f :: String -> TH.ExpQ
f = p . return . readHsTypeSigs
#endif


-- | 'setTimeout' sets the timeout in microseconds. Also, my implementation of timeout also catches inevitable exceptions like stack space overflow. Note that setting timeout makes the library referentially untransparent. (But currently @setTimeout 20000@ is the default!)
setTimeout :: Int -- ^ time in microseconds
              -> IO ()
setTimeout n = do pto <- newPTO n
                  PG (x,y,z,cmn) <- readIORef refmemodeb
                  writeIORef refmemodeb $ PG (x,y,z,cmn{opt = (opt cmn){timeout=Just pto}})
-- | 'unsetTimeout' disables timeout. This is the safe choice.
unsetTimeout :: IO ()
unsetTimeout = do PG (x,y,z,cmn) <- readIORef refmemodeb
                  writeIORef refmemodeb $ PG (x,y,z,cmn{opt = (opt cmn){timeout=Nothing}})

setDepth :: Int -- ^ memoization depth. (Sub)expressions within this size are memoized, while greater expressions will be recomputed (to save the heap space).
         -> IO ()
setDepth d = do PG (x,y,z,cmn) <- readIORef refmemodeb
                writeIORef refmemodeb $ PG (x,y,z,cmn{opt = (opt cmn){memodepth=d}})

-- ^ Currently the default depth is 10. You may want to lower the value if your computer often swaps, or increase it if you have a lot of memory.

{-# NOINLINE refmemodeb #-}
refmemodeb :: IORef ProgGen
refmemodeb = unsafePerformIO (newIORef defaultMD)
defaultMD = mkPG [] :: ProgGen

trsToTCL :: [TypeRep] -> TyConLib -- ReadType.extractTyConLib :: [HsDecl] -> TyConLibを参考にできる． -- この2行と
trsToTCL trs
    = (Map.fromListWith (\new old -> old) [ tup | k <- [0..7], tup <- tcsByK ! k ], tcsByK)
    where tnsByK :: Array Types.Kind [TypeName]
          tnsByK = accumArray (flip (:)) [] (0,7) ( trsToTCstrs trs )   -- ここを変えた．
          tcsByK :: Array Types.Kind [(TypeName,Types.TyCon)]
          tcsByK = listArray (0,7) [ tnsToTCs (tnsByK ! k) | k <- [0..7] ]
          tnsToTCs :: [TypeName] -> [(TypeName,Types.TyCon)]
          tnsToTCs tns = zipWith (\ i tn -> (tn, i)) [0..] tns
-- x 実際には(->)はTyCon扱いにはしないんだけど，ほんのちょっとだけ無駄になるだけなのでいいでしょ．

trsToTCstrs :: [TypeRep] -> [(Int, String)] -- Int is the arity of the TyCon. There can be duplicates.
trsToTCstrs [] = []
trsToTCstrs (tr:ts) = case splitTyConApp tr of (tc,trs) -> (length trs, tyConName tc) : trsToTCstrs (trs++ts)


-- MemoやgetEverything自体はIORefを使わずにIOなしで実装できる訳で，その意味では，IORefを使わない方がいいかも．
-- x ついでにいうと，1秒でのタイムアウトを表すPTO（のGLOBAL_VAR）もIOなしで用意できる．（unsafePerformIO使うけど）

-- | 'getEverything' uses the \'global\' values set with @set*@ functions. 'getEverythingF' is its filtered version
getEverything :: Typeable a => 
                 Bool -- ^ whether to include functions with unused arguments
                  -> IO (Every a)
getEverything withAbsents = do 
                   memodeb <- readIORef refmemodeb
                   return (everything memodeb withAbsents)
getEverythingF :: Typeable a => 
                  Bool -- ^ whether to include functions with unused arguments
                  -> IO (Every a)
getEverythingF withAbsents = do 
                   memodeb <- readIORef refmemodeb
                   return (everythingF memodeb withAbsents)
{-
getEverything = result
    where ty = typeOf $ snd $ head $ head $ unsafePerformIO result
          result = do memodeb@(trie,prims,depth,tcl) <- readIORef refmemodeb
                      return $ unMx $ toMx (fmap (\ e -> (exprToTHExp (error "unknown conlib") e, unsafeExecute e)) (matchingPrograms (trToType tcl ty) memodeb))
-}

-- | 'everything' generates all the expressions that fit the inferred type, and their representations in the 'TH.Exp' form.
--   It returns a stream of lists, which is equivalent to Spivey's @Matrix@ data type, i.e., that contains expressions consisted of n primitive components at the n-th element (n = 1,2,...).
--   'everythingF' is its filtered version
everything, everythingF :: (ProgramGenerator pg, Typeable a) =>
                     pg   -- ^ program generator
                  -> Bool -- ^ whether to include functions with unused arguments
                  -> Every a
everything  memodeb = et undefined  memodeb (mxExprToEvery   "MagicHaskeller.everything: type mismatch" memodeb)
everythingF memodeb = et undefined  memodeb (mxExprFiltEvery "MagicHaskeller.everythingF: type mismatch" memodeb)
everyACE :: (ProgramGenerator pg, Typeable a) =>
                     pg   -- ^ program generator
                  -> Bool -- ^ whether to include functions with unused arguments
                  -> [[(CoreExpr,a)]]
everyACE  memodeb = et undefined  memodeb (mxExprToACE   "MagicHaskeller.everyACE: type mismatch" memodeb)
et :: (ProgramGenerator pg, Typeable a) =>
                     a    -- ^ dummy argument
                  -> pg   -- ^ program generator
                  -> (Types.Type -> Matrix AnnExpr -> Matrix (e,a))
                  -> Bool -- ^ whether to include functions with unused arguments
                  -> [[(e,a)]]
et dmy memodeb filt withAbsents = unMx $ filt ty $ matchPs withAbsents ty memodeb
    where ty = trToType (extractTCL memodeb) (typeOf dmy)
noFilter :: ProgramGenerator pg => pg -> Types.Type -> a -> a
noFilter _m _t = id

matchPs True  = matchingPrograms
matchPs False = matchingProgramsWOAbsents 

mxExprToEvery :: (Expression e, Search m, WithCommon pg, Typeable a) => String -> pg -> Types.Type -> m e -> m (Exp, a)
mxExprToEvery   msg memodeb _  = fmap (unwrapAE (extractVL memodeb) msg memodeb . toAnnExpr (reducer $ extractCommon memodeb))
mxExprFiltEvery :: (Expression e, FiltrableBF m, WithCommon pg, Typeable a) => String -> pg -> Types.Type -> m e -> m (Exp, a)
mxExprFiltEvery msg memodeb ty = fmap (unwrapAE (extractVL memodeb) msg memodeb) . randomTestFilter memodeb ty . mxExpr memodeb
mxExpr memodeb = fmap (toAnnExpr (reducer $ extractCommon memodeb))
mxExprToACE :: (Expression e, Search m, WithCommon pg, Typeable a) => String -> pg -> Types.Type -> m e -> m (CoreExpr, a)
mxExprToACE   msg memodeb _  = fmap (unwrapToCE msg memodeb . toAnnExpr (reducer $ extractCommon memodeb))

unwrapAE :: (WithCommon pg, Typeable a) => VarLib -> String -> pg -> AnnExpr -> (Exp, a)
unwrapAE vl msg memodeb (AE e dyn) = (exprToTHExp vl e, fromDyn tcl dyn (error msg))
    where tcl = extractTCL memodeb
unwrapToCE :: (WithCommon pg, Typeable a) => String -> pg -> AnnExpr -> (CoreExpr, a)
unwrapToCE msg memodeb ae@(AE e dyn) = (e, fromDyn tcl dyn (error msg))
    where tcl = extractTCL memodeb


etup :: (ProgramGenerator pg, Typeable a) =>
                     a    -- ^ dummy argument
                  -> pg   -- ^ program generator
                  -> Bool -- ^ whether to include functions with unused arguments
                  -> [[((Exp,a), (Exp,a))]]
etup dmy memodeb withAbsents 
  = unMx 
    $ fmap (\e -> (unwrapAE (vl cmn) "MagicHaskeller.etup: type mismatch" memodeb $ toAnnExpr (execute (opt cmn) (vl cmn)) e, 
                   unwrapAE (pvl cmn) "MagicHaskeller.etup: type mismatch" memodeb $ toAnnExpr (execute (opt cmn) (pvl cmn)) $ toCE e))
    $  matchPs withAbsents ty memodeb
    where ty  = trToType (extractTCL memodeb) (typeOf dmy)
          cmn = extractCommon memodeb
{-
無限リストを使うなら，unsafeInterleaveIOが必要なはず．その場合IOに特化することになる．
-}
everythingM :: (ProgramGenerator pg, Typeable a, Monad m, Functor m) =>
                     pg   -- ^ program generator
                  -> Bool -- ^ whether to include functions with unused arguments
                  -> Int  -- ^ query depth
                  -> m [(TH.Exp, a)]
everythingM = eM undefined
eM :: (ProgramGenerator pg, Typeable a, Monad m, Functor m) =>
                     a    -- ^ dummy argument
                  -> pg   -- ^ program generator
                  -> Bool -- ^ whether to include functions with unused arguments
                  -> Int
                  -> m [(TH.Exp, a)]
eM dmy memodeb withAbsents = result
    where tcl = extractTCL memodeb
          ty  = trToType tcl $ typeOf dmy
          result = unRcT $ mxExprToEvery "MagicHaskeller.everythingM: type mismatch" memodeb undefined $ matchPs withAbsents ty memodeb
everythingIO :: (ProgramGeneratorIO pg, Typeable a) =>
                     pg   -- ^ program generator
                  -> EveryIO a
everythingIO = eIO undefined
eIO :: (ProgramGeneratorIO pg, Typeable a) =>
                     a    -- ^ dummy argument
                  -> pg   -- ^ program generator
                  -> EveryIO a
eIO dmy memodeb = result
    where tcl = extractTCL memodeb
          ty  = trToType tcl $ typeOf dmy
          result = unRcT $ mxExprToEvery "MagicHaskeller.everythingIO: type mismatch" memodeb undefined $ matchingProgramsIO ty memodeb

strip :: m (Every a) -> a
strip = undefined

stripEvery :: Every a -> a
stripEvery = head . map snd . concat

unifyable, matching, unifyableF, matchingF :: ProgramGenerator pg =>
                                              pg  -- ^ program generator
                                              -> TH.Type -- ^ query type
                                              -> [[TH.Exp]]
-- ^ Those functions are like 'everything', but take 'TH.Type' as an argument, which may be polymorphic.
--   For example, @'printQ' ([t| forall a. a->a->a |] >>= return . 'unifyable' True 10 memo)@ will print all the expressions using @memo@ whose types unify with @forall a. a->a->a@.
--   (At first I (Susumu) could not find usefulness in finding unifyable expressions, but seemingly Hoogle does something alike, and these functions might enhance it.)
unifyable memodeb tht =  unMx $ genExps noFilter unifyingPrograms  memodeb tht
matching   memodeb tht =  unMx $ genExps noFilter matchingPrograms  memodeb tht
-- unifyablePos  memodeb tht = unMx $ toMx $ fmap (\(es,subst,mx) -> (map (pprintUC . exprToTHExp (extractVL memodeb)) es, subst, mx)) $ unifyingPossibilities (thTypeToType (extractTCL memodeb) tht) memodeb
unifyableF  memodeb tht = unMx $ genExps randomTestFilter unifyingPrograms  memodeb tht
matchingF   memodeb tht = unMx $ genExps randomTestFilter matchingPrograms  memodeb tht
genExps filt rawGenProgs  memodeb tht
    = case thTypeToType (extractTCL memodeb) tht of
        ty -> fmap (exprToTHExp (extractVL memodeb) . toCE) $
              filt memodeb ty $ fmap (toAnnExpr (reducer $ extractCommon memodeb)) (rawGenProgs ty memodeb)
--   Another advantage of these functions is that you do not need to define @instance Typeable@ for user defined types.
--   と思ったけど，GHCではderiving Typeableで簡単に定義できるし，Typeableが定義できない型なんてなさそう（deriving Typeableし忘れたdata typeを含むdataがそう？）

-- specializedPossi  memodeb tht =  unMx $ toMx $ fmap show (specializedPossibleTypes (thTypeToType (extractTCL memodeb) tht) memodeb)

{-
wrappit :: (Search m, Functor m, Typeable a) => m CoreExpr -> [[(TH.Exp,a)]]
wrappit = unMx . toMx . fmap (\ e -> (exprToTHExp e, unsafeExecute e))
-}

-- | @'findOne' pred@ finds an expression 'e' that satisfies @pred e == True@, and returns it in 'TH.Exp'. 
findOne :: Typeable a => 
           Bool -- ^ whether to include functions with unused arguments
           -> (a->Bool) -> TH.Exp
findOne withAbsents pred = unsafePerformIO $ findDo (\e _ -> return e) withAbsents pred

-- | 'printOne' prints the expression found first. 
printOne :: Typeable a => 
            Bool -- ^ whether to include functions with unused arguments
            -> (a->Bool) -> IO TH.Exp
printOne withAbsents pred = do 
                   expr <- findDo (\e _ -> return e) withAbsents pred
                   putStrLn $ pprintUC expr
                   return expr
-- | 'printAll' prints all the expressions satisfying the given predicate.
printAll, printAny :: Typeable a =>
                      Bool -- ^ whether to include functions with unused arguments
                      ->  (a->Bool) -> IO ()
printAny = printAll -- provided just for backward compatibility
printAll = findDo (\e r -> putStrLn (pprintUC e) >> r)

printAllF :: (Typeable a, Filtrable a) =>
             Bool -- ^ whether to include functions with unused arguments
             ->  (a->Bool) -> IO ()
printAllF withAbsents pred = do 
                    et  <- getEverything withAbsents
                    fet <- filterThenF pred et
                    pprs fet

findDo :: Typeable a => 
          (TH.Exp -> IO b -> IO b) 
          -> Bool -- ^ whether to include functions with unused arguments
          -> (a->Bool) -> IO b
findDo op withAbsents pred = do 
                     et <- getEverything withAbsents
                     md <- readIORef refmemodeb
                     let mpto = timeout $ opt $ extractCommon md
                     fp mpto (concat et)
    where fp mpto ((e,a):ts) = do -- hPutStrLn stderr ("trying" ++ pprintUC e)
                                  result <- maybeWithTO seq mpto (return (pred a))
                                  case result of Just True  -> e `op` fp mpto ts
                                                 Just False -> fp mpto ts
                                                 Nothing    -> hPutStrLn stderr ("timeout on "++pprintUC e) >> fp mpto ts
-- x 本当はrecompのままでやった方が速いはず．

-- | 'filterFirst' is like 'printAll', but by itself it does not print anything. Instead, it creates a stream of expressions represented in tuples of 'TH.Exp' and the expressions themselves. 
filterFirst :: Typeable a =>
               Bool -- ^ whether to include functions with unused arguments
               ->  (a->Bool) -> IO (Every a)
filterFirst withAbsents pred = do 
                      et <- getEverything withAbsents
                      filterThen pred et
-- randomTestFilter should be applied after filterThen, because it's slower
filterFirstF :: (Typeable a, Filtrable a) => 
                Bool -- ^ whether to include functions with unused arguments
                -> (a->Bool) -> IO (Every a)
filterFirstF withAbsents pred = do 
                       et <- getEverything withAbsents
                       filterThenF pred et
filterThenF pred et = do
                       fd <- filterThen pred et
                       memodeb <- readIORef refmemodeb
                       let o = opt $ extractCommon memodeb
                       return $ everyF o fd
{- refmemodeb にあるものが実際に使われているものとは限らない．refmemodebを使わないという選択もあるので．
filterFirstF pred = do et <- getEverything
                       filterThenF pred et
filterThenF pred ts = do
                       fd <- filterThen pred ts
                       let x=undefined
                           _=pred x
                       memodeb <- readIORef refmemodeb
                       return $ unMx $ randomTestFilter memodeb (getType memodeb x) $ Mx et
getType :: Typeable a => a -> ProgGen -> Types.Type
getType ty memodeb = trToType (extractTCL memodeb) (typeOf ty)
-}
everyF :: (Typeable a, Filtrable a) =>
          Opt b
              -> [[(e,a)]] -> [[(e,a)]]
everyF o = unMx . unsafeRandomTestFilter (timeout o) (fcnrand o) . Mx 

-- | 'filterThen' may be used to further filter the results.
filterThen :: Typeable a => (a->Bool) -> Every a -> IO (Every a)
filterThen pred ts = do md <- readIORef refmemodeb
                        let mpto = timeout $ opt $ extractCommon md
                        return (map (fp mpto pred) ts)
fp :: Typeable a => Maybe Int -> (a->Bool) -> [(Exp, a)] -> [(Exp, a)]
fp mpto pred = filter (\ (_,a) -> unsafePerformIO (maybeWithTO seq mpto (return (pred a))) == Just True)
{-
fp _    pred []            = []
fp mpto pred (ea@(e,a):ts) = case unsafePerformIO (maybeWithTO seq mpto (return (pred a))) of
                                    Just True -> ea : fp mpto pred ts
                                    _         -> fp mpto pred ts
-}
-- fpartial :: Typeable a => Maybe Int -> (a->Bool) -> [((Exp, a),(Exp,a))] -> [(Exp, a)]
-- fpartial mpto pred tups = fp mpto pred $ map snd tups
-- The following tries the total version if the partial version fails. Not good when using the Partial class, because when using the Partial class the total and partial versions look the same. Now the Partial class is not used, so I recover this
fpartial :: Typeable a => Maybe Int -> (a->Bool) -> [((Exp, a),(Exp,a))] -> [(Exp, a)]
fpartial mpto pred ts = [ t | Just t <- map (fpart mpto pred) ts ]
fpart mpto pred (ea@(_,a),eap@(_,ap))
  = case unsafePerformIO (maybeWithTO seq mpto (return $! (pred ap))) of
                                    Just True  -> Just eap
                                    Just False -> Nothing
                                    Nothing -> case unsafePerformIO (maybeWithTO seq mpto (return  $!(pred a))) of 
                                      Just True -> Just ea
                                      _         -> Nothing

{-
fpartial _    pred []            = []
fpartial mpto pred ((ea@(_,a),eap@(_,ap)):ts) 
  = case unsafePerformIO (maybeWithTO seq mpto (return (pred ap))) of
                                    Just True  -> eap : fpartial mpto pred ts
                                    Just False -> fpartial mpto pred ts
                                    Nothing    -> case unsafePerformIO (maybeWithTO seq mpto (return (pred a))) of
                                                     Just True  -> ea : fpartial mpto pred ts
                                                     _          -> fpartial mpto pred ts
-}
fpartialIO :: Typeable a => Maybe Int -> (a->Bool) -> [((e, a),(e,a))] -> IO [(e, a)]
fpartialIO mpto pred ts = filterIO (fpartIO mpto pred) ts
filterIO :: Typeable a => (t -> IO (Maybe (e,a))) -> [t] -> IO [(e,a)]
filterIO filt ts = do mbs <- interleaveActions {- parallelInterleaved -} $ map filt ts
--filterIO filt ts = do mbs <- mapIO filt ts
                      return [ tup | Just tup <- mbs ]
#ifdef PAR
fpartialParIO :: Typeable a => Maybe Int -> (a->Bool) -> [((e, a),(e,a))] -> ParIO [(e, a)]
fpartialParIO mpto pred ts = do mbs <- mapParIO (liftIO . fpartIO mpto pred) ts
                                return [ tup | Just tup <- mbs ]
#endif
fpartIO :: Typeable a => Maybe Int -> (a->Bool) -> ((e, a),(e,a)) -> IO (Maybe (e, a))
fpartIO mpto pred (ea, eap@(_,ap))
  = do mbb <- maybeWithTO seq mpto $ return $! pred ap 
       case mbb of
         Just True  -> return $ Just eap
         Just False -> return Nothing
         Nothing    -> ftotIO mpto pred ea
{- これだとinterleaveできない．
fpartialIO _    pred []            = return []
fpartialIO mpto pred ((ea@(_,a),eap@(_,ap)):ts) 
  = do mbb <- (maybeWithTO seq mpto (return $! pred ap)) 
       case mbb of
         Just True  -> fmap (eap :) $ fpartialIO mpto pred ts
         Just False -> fpartialIO mpto pred ts
         Nothing    -> do mbb2 <- maybeWithTO seq mpto (return (pred a)) 
                          case mbb2 of
                                                     Just True  -> fmap (ea :) $ fpartialIO mpto pred ts
                                                     _          -> fpartialIO mpto pred ts

-}



ftotalIO :: Typeable a => Maybe Int -> (a->Bool) -> [(e, a)] -> IO [(e, a)]
ftotalIO mpto pred ts = filterIO (ftotIO mpto pred) ts
ftotIO :: Typeable a => Maybe Int -> (a->Bool) -> (e,a) -> IO (Maybe (e, a))
ftotIO mpto pred (ea@(_,a))
  = do mbb <- maybeWithTO seq mpto $ return $! pred a 
       case mbb of
         Just True  -> return $ Just ea
         _          -> return Nothing





fpIO :: Typeable a => Maybe Int -> (a->Bool) -> [((Exp, a),(Exp,a))] -> IO [(Exp, a)]
fpIO mpto pred ts = do mbs <- {-interleaveActions -}sequence {- parallelInterleaved -} $ {- take 19 $ drop 6550 $ -} zipWith (fIO mpto pred) ts [0..]
--fpIO mpto pred ts = do mbs <- runParIO $ mapParIO (liftIO $ fIO mpto pred) $ zip ts [0..]
                       return [ tup | Just tup <- mbs ]
fIO :: Typeable a => Maybe Int -> (a->Bool) -> ((Exp, a),(Exp,a)) -> Int -> IO (Maybe (Exp, a))
fIO mpto pred (ea@(e,a),eap@(_,ap)) i
  = do hPutStrLn stderr (shows i " trying "++pprint e) 
       mbb <- maybeWithTO seq mpto $ return $! pred a
       case mbb of
         Just True  -> return $ Just ea
         _          -> return Nothing


mapIO :: (a -> IO b) -> [a] -> IO [b]
mapIO f xs = mapM (spawnIO . f) xs >>= mapM takeMVar
spawnIO :: IO a -> IO (MVar a)
spawnIO a = do
      mv <- newEmptyMVar
      forkIO (a >>= \v -> v `seq` putMVar mv v)
      return mv

#ifdef PAR
-- ホントはspawnを使ったほうが良さそうだが，NFData定義するのが面倒なので．
mapParIO :: (a -> ParIO b) -> [a] -> ParIO [b]
mapParIO f as = mapM (spawn_ . f) as >>= mapM get
#endif

-- | @io2pred@ converts a specification given as a set of I/O pairs to the predicate form which other functions accept.
io2pred :: Eq b => [(a,b)] -> ((a->b)->Bool)
io2pred ios f = all (\(a,b) -> f a == b) ios

-- utility functions to pretty print the results
-- | 'pprs' pretty prints the results to the console, using 'pprintUC'
pprs :: Every a -> IO ()
pprs = mapM_ (putStrLn . pprintUC . fst) . concat
-- | 'pprsIO' is the 'EveryIO' version of pprs
pprsIO  ::        EveryIO a -> IO ()
pprsIO        eio = mapM_ (\d -> eio d >>= mapM_ (putStrLn . pprintUC . fst)) [0..]
-- | @pprsIOn depth eio@ is the counterpart of @pprs (take depth eio)@, while @pprsIO eio@ is the counterpart of @pprs eio@. 
--   Example: @pprsIOn 5 (everythingIO (mlist::ProgGen) :: EveryIO ([Char]->[Char]))@
pprsIOn :: Int -> EveryIO a -> IO ()
pprsIOn depth eio = mapM_ (\d -> eio d >>= mapM_ (putStrLn . pprintUC . fst)) [0..depth-1]
-- | 'pprintUC' is like 'Language.Haskell.TH.pprint', but unqualifies (:) before pprinting in order to avoid printing "GHC.Types.:" which GHCi does not accept and sometimes annoys when doing some demo.
pprintUC :: (Ppr a, Data a) => a -> String
pprintUC =  pprint . everywhere (mkT unqCons)
unqCons :: Name -> Name
unqCons n | show n == show '(:) = mkName ":" -- NB: n == '(:) would not work due to the definition of Eq Name.
          | otherwise           = n

lengths   :: Every   a -> IO ()
lengths   = print . map length
lengthsIO :: EveryIO a -> IO ()
lengthsIO eio = mapM_ (\d -> eio d >>= putStr . (' ':) . show . length) [0..]
lengthsIOn, lengthsIOnLn :: Int -> EveryIO a -> IO ()
lengthsIOn depth eio = mapM_ (\d -> eio d >>= putStr . (' ':) . show . length) [0..depth-1]
lengthsIOnLn depth eio = lengthsIOn depth eio >> putStrLn ""

printQ :: (Ppr a, Data a) => Q a -> IO ()
printQ q = runQ q >>= putStrLn . pprintUC

\end{code}
