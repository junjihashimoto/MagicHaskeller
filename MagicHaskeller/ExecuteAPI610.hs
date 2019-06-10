-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE TemplateHaskell, MagicHash, CPP #-}
-- compile with  -package ghc
module MagicHaskeller.ExecuteAPI610  {- (loadObj, prepareAPI, executeAPI, unsafeExecuteAPI) -} where
import qualified HscMain
import GHC
import GHC.Exts
import GHC.Paths(libdir) -- as instructed in http://haskell.org/haskellwiki/GHC/As_a_library
import DynFlags         -- (DynFlag, defaultDynFlags, PackageFlag(ExposePackage)) -- , glasgowExtsFlags) はexportされていないらしい.
import SrcLoc           (SrcSpan(..), noSrcSpan, noSrcLoc, interactiveSrcLoc, noLoc)

-- import MyCorePrep( corePrepExpr )
import CorePrep(corePrepExpr) -- コンパイルが通らないのでオリジナルにしてみる

import FastString
import ByteCodeGen      ( coreExprToBCOs )

-- import MyLink                -- ( HValue, linkExpr, initDynLinker )
import Linker -- コンパイルが通らないのでオリジナルにしてみる

-- import Flattening
import HscTypes        -- ( HscEnv(..), Session(..), withSession, InteractiveContext(..), mkTypeEnv ) -- also import instance MonadIO Ghc
import SimplCore
-- import SimplOnce -- コンパイルが通らないのでコメントアウト
import VarEnv           ( emptyTidyEnv )
import CoreSyn          ( CoreExpr, Expr(..), Bind(..) )     -- compiler/coreSyn/CoreSyn.lhs
import CoreTidy         ( tidyExpr )


import Parser           (parseStmt)
import Lexer
import TcRnDriver        ( tcRnStmt, tcRnExpr, tcRnType )
import Desugar          (deSugarExpr)
#if __GLASGOW_HASKELL__ < 708
import PrelNames        ( iNTERACTIVE )
#else
import PrelNames        (mkInteractiveModule)
#endif
import ErrUtils
import StringBuffer     (stringToStringBuffer)
import Outputable       (ppr, pprPanic, showSDocDebug, showSDoc)
import Type             (pprType, Type)

import CoreLint         (lintUnfolding)
import VarSet           (varSetElems)
import Panic            (panic)

import Var              -- (Var(..))

import System.IO
import System.IO.Unsafe

import Data.IORef

import System.Exit
import Control.Monad(when)
-- import Control.Monad.Trans(liftIO)

import MagicHaskeller.MyDynamic
import qualified MagicHaskeller.CoreLang as CoreLang
import Language.Haskell.TH as TH hiding (ppr)

import Data.List(isSuffixOf)

#ifdef GHC6
-- prelude/TysPrim.
import TysPrim(anyPrimTy)
#endif

import Bag
import RdrName
import OccName
import Convert
import HsUtils
import HsExpr

-- 最後のCoreExpr ---> CoreExprで要るもの．
import IdInfo
import Data.Char(ord,chr)
import qualified Data.Map as Map
import qualified MagicHaskeller.Types as Types
import Data.List
import Unique
import Id

import UniqSupply

import ByteCodeLink(linkBCO,extendClosureEnv)
#ifdef PRELINK
# if __GLASGOW_HASKELL__ >= 800
import ByteCodeTypes(UnlinkedBCO(unlinkedBCOName))
# else
import ByteCodeAsm(UnlinkedBCO(unlinkedBCOName))
# endif
#endif
# if __GLASGOW_HASKELL__ >= 800
import GHCi(wormhole)
#endif

import Data.Array

-- #define PRELINK

pathToGHC :: FilePath    -- path to GHC, e.g. "/usr/lib/ghc-6.10.4". 'libdir' can be used instead.
pathToGHC = libdir

loadObj :: [String] -- ^ visible modules (including package modules). You may omit the Prelude.
           -> IO (CoreLang.VarLib -> CoreLang.CoreExpr -> Dynamic)
loadObj fss = fmap unsafeExecuteAPI $ prepareAPI [] fss

-- Just follow http://haskell.org/haskellwiki/GHC/As_a_library
-- 問題は，すでに読まれているmoduleはどうするかってことだけど，:loadコマンド同様再読み込み
-- addNonPackageTargetってのを定義したので，分ける必要はなくなったはず．
prepareAPI :: [FilePath] -- ^ modules to be loaded (except package modules)
           -> [FilePath] -- ^ visible modules (including package modules)
           -> IO HscEnv
prepareAPI loadfss visfss
{-
prepareAPI :: [String] -- ^ visible modules (including package modules). 
                       --   Supplying @[]@ here works without any problems within GHCi, and currently @prepareAPI@ does not work without --interactive, 
                       --   so this argument is actually of no use:(
           -> IO HscEnv
prepareAPI fss
-}
#if __GLASGOW_HASKELL__ >= 700
# if __GLASGOW_HASKELL__ >= 706
    = defaultErrorHandler defaultFatalMessager defaultFlushOut $
# else
    = defaultErrorHandler defaultLogAction $
# endif
#else
    = defaultErrorHandler defaultDynFlags $
#endif
      runGhc (Just pathToGHC) $ do
          -- liftIO $ hPutStrLn stderr "setting up flags"

          dfs     <- getSessionDynFlags
--          when (flags dfs /= flags defaultDynFlags) $ error "flags are different"
          let newf = dfs{ -- opt_P = "-DTEMPLATE_HASKELL" : "-DCLASSIFY" : "-DCHTO" : opt_P dfs,           -- defaultDynFlagsのソースが結構参考になったり．
                         packageFlags = [ packageNameToFlag "ghc", packageNameToFlag "old-time", packageNameToFlag "ghc-paths" ] -- , packageNameToFlag "MagicHaskeller" ]
                         {-
                         flags = Opt_TemplateHaskell  : Opt_Cpp : -- Opt_FlexibleInstances : Opt_ExistentialQuantification : Opt_PolymorphicComponents : Opt_RelaxedPolyRec :
                                 Opt_MagicHash :
                                 Opt_RankNTypes :
                                 filter (/=Opt_MonomorphismRestriction) (flags dfs) -}
                        } -- Was: Opt_TH   --  てゆーか，LibTHをここで読むにはいろんなフラグが....
          setSessionDynFlags newf   -- result abandoned
          -- ソースによると結果はDynamic linkingの時に必要ってことだけど，ま，基本的にはDynamic linkingはunsupportedってことか．
          -- http://hackage.haskell.org/trac/ghc/wiki/DynamicLinking
          -- ...違う．そのdynamic linkingではない．

          -- liftIO $ hPutStrLn stderr "loading modules" -- This IS necessary.
          ts <- mapM (\fs -> guessTarget fs Nothing) loadfss
          setTargets ts
          sf <- defaultCleanupHandler newf (load LoadAllTargets)
          case sf of Succeeded -> return ()
                     Failed    -> error "failed to load modules"

          -- liftIO $ hPutStrLn stderr "setting up modules"
#if __GLASGOW_HASKELL__ >= 700
          modules <- mapM (\fs -> fmap (\x -> (x,Nothing)) $ findModule (mkModuleName fs) Nothing) ("Prelude":visfss)
#else
          modules <- mapM (\fs -> findModule (mkModuleName fs) Nothing) ("Prelude":visfss)
#endif
#if __GLASGOW_HASKELL__ >= 700
          setContext [ IIDecl $ (simpleImportDecl . mkModuleName $ moduleName){GHC.ideclQualified = False} | moduleName <- "Prelude":visfss ] -- GHC 7.4
#else
          setContext [] modules
#endif

#ifdef PRELINK
          -- prelink!
          newdfs     <- getSessionDynFlags
          initDynLinker newdfs
#endif

          getSession

packageNameToFlag :: String -> PackageFlag
#if __GLASGOW_HASKELL__ < 710
packageNameToFlag = ExposePackage
#else
# if __GLASGOW_HASKELL__ < 800
packageNameToFlag name = ExposePackage (PackageArg name) (ModRenaming False []) -- I am not sure this is the correct conversion, because I could not find any documentation on the change.
# else
packageNameToFlag name = ExposePackage ("-package "++name) (PackageArg name) (ModRenaming False []) -- I am not sure this is the correct conversion, because I could not find any documentation on the change.
# endif
#endif

{-
-- | @addNonPackageTarget@ adds a target only if the target is not a package module.
--   This function assumes there is no package module in the target set of the session.
addNonPackageTarget :: Target -> IO ()
addNonPackageTarget target@(Target targetid _)
    = catchDyn (addTarget target >> depanal [] False >> return ())
               (\str -> if "is a package module" `isSuffixOf` str then removeTarget targetid else throwDyn str)
-- depanalがNothingを返す場合，結局後のloadがfailする訳だが，面倒なのでこの段階では放置プレイってことで．
-}

-- At least I should use a customized version of toString....
unsafeExecuteAPI :: HscEnv -> CoreLang.VarLib -> CoreLang.CoreExpr -> Dynamic
unsafeExecuteAPI session vl cece = unsafeToDyn undefined undefined (unsafeCoerce# $ unsafePerformIO $ executeAPI session vl cece) undefined -- unsafeCoerce# is necessary to convert from Dynamic.HValue to HValue.
executeAPI :: HscEnv -> CoreLang.VarLib -> CoreLang.CoreExpr -> IO a
executeAPI session vl cece = executeTHExp session (CoreLang.exprToTHExp vl cece)
executeTHExp :: HscEnv -> TH.Exp -> IO a
executeTHExp session the = unwrapCore session =<< compileCoreExpr session the


compileCoreExpr ::  HscEnv -> TH.Exp -> IO CoreSyn.CoreExpr 
compileCoreExpr hscEnv the
    = -- defaultErrorHandler defaultDynFlags $ -- thread killed を表示させたい場合はこっち．
{-
       do res <- compileExpr session $ TH.pprint $ CoreLang.exprToTHExp cece
          case res of Nothing -> hPutStrLn stderr "Could not execute" >> error "could not execute"
                      Just hv -> return hv
-}


--       do mbt <- strToCore hscEnv ("let __cmCompileExpr = " ++ TH.pprint the)

       do mbt <- stmtToCore hscEnv $ thExpToStmt hscEnv the
          case mbt of Nothing -> error ("could not compile " ++ TH.pprint the ++ " to core.")
                      Just ([i ], ce) -> return ce


-- unwrapCore, unwrapCore' の両方が正しく動く．unwrapCoreはghc6.8で動いていたのを持ってきたもので，compileExprHscMainの方をコメントアウトしてrunCoreExprにすると色々はしょる代わりに正しく動かない．
unwrapCore :: HscEnv -> CoreSyn.CoreExpr -> IO a
unwrapCore hscEnv ce =                  do -- iohvs <- runCoreExpr hscEnv ce -- (removeIdInfo ce)
                                           iohvs <- unsafeCoerce# $ compileExprHscMain hscEnv ce
                                           [hv] <- iohvs
                                           return hv

-- unwrapCore' hscEnv ce = fmap head $ unsafeCoerce# =<< HscMain.compileExpr hscEnv (srcLocSpan interactiveSrcLoc) ce

#if __GLASGOW_HASKELL__ >= 800
ce2b hscEnv pe = coreExprToBCOs hscEnv undefined pe
#else
# if __GLASGOW_HASKELL__ >= 700
ce2b hscEnv pe = coreExprToBCOs (hsc_dflags hscEnv) undefined pe
# else
ce2b hscEnv pe = coreExprToBCOs (hsc_dflags hscEnv) pe
# endif
#endif

runCoreExpr, runPrepedCoreExpr :: HscEnv -> CoreExpr -> IO a
runCoreExpr hscEnv ce
    = -- repeatIO 10 $
      do
         let dfs = hsc_dflags hscEnv
#if __GLASGOW_HASKELL__ >= 706
         pe <- corePrepExpr dfs hscEnv ce -- runPrepedCoreExprとの違いはこのcorePrepExprがあるかどうかだけ
#else
         pe <- corePrepExpr dfs ce -- runPrepedCoreExprとの違いはこのcorePrepExprがあるかどうかだけ
#endif
         bcos <- -- repeatIO 10 $
                 ce2b hscEnv pe
#ifdef PRELINK
         hv <- linkTheExpr bcos
#else
         hv <-linkExpr hscEnv noSrcSpan bcos
#endif
         return $ unsafeCoerce# hv

runPrepedCoreExpr hscEnv ce
    = -- repeatIO 10 $
      do
         bcos <- ce2b hscEnv ce
         -- repeatIO 10 $
#ifdef PRELINK
         hv <- linkTheExpr bcos
#else
         hv <-linkExpr hscEnv noSrcSpan bcos
#endif
         return $ unsafeCoerce# hv

#ifdef PRELINK
-- | If already prelinked linkTheExpr can be used in place of linkExpr.
linkTheExpr :: UnlinkedBCO -> IO HValue
linkTheExpr ulbco
    = do pls <- readIORef v_PersistentLinkerState
         let ie = itbl_env pls
             ce = closure_env pls
             nm = unlinkedBCOName ulbco
         fixIO (\hv -> linkBCO ie (extendClosureEnv ce [(nm,hv)]) ulbco)
#endif

-- The type of LStmt has changed during move to GHC 7.8.1.
-- stmtToCore :: HscEnv -> HsExpr.LStmt RdrName.RdrName -> IO (Maybe ([Id], CoreExpr))
stmtToCore hscEnv pst = do let dfs  = hsc_dflags hscEnv
                               icxt = hsc_IC     hscEnv
#if __GLASGOW_HASKELL__ >= 708
                           (tcmsgs, mbtc) <- tcRnStmt hscEnv pst
#else                
                           (tcmsgs, mbtc) <- tcRnStmt hscEnv icxt pst
#endif
                           case mbtc of Nothing             -> perror dfs tcmsgs
#if __GLASGOW_HASKELL__ >= 706
                                        Just (ids, tc_expr, _fixtyenv) -> do -- desugar
#else
                                        Just (ids, tc_expr) -> do -- desugar
#endif
#if __GLASGOW_HASKELL__ >= 708
                                          (desmsgs, mbds) <- deSugarExpr hscEnv tc_expr
#else
# if __GLASGOW_HASKELL__ >= 700
                                          let typeEnv = mkTypeEnv (ic_tythings icxt)
# else
                                          let typeEnv = mkTypeEnv (map AnId (ic_tmp_ids icxt))
# endif
                                          (desmsgs, mbds) <- deSugarExpr hscEnv iNTERACTIVE (ic_rn_gbl_env icxt) typeEnv tc_expr
#endif
                                          case mbds of Nothing -> perror dfs desmsgs
                                                       Just ds -> return (Just (ids, ds))
#if __GLASGOW_HASKELL__ >= 706
perror dfs (wmsg,emsg) = printBagOfErrors dfs wmsg >> printBagOfErrors dfs emsg >> return Nothing
#else
# if __GLASGOW_HASKELL__ >= 700
perror dfs (wmsg,emsg) = let sdocs = pprErrMsgBag wmsg ++ pprErrMsgBag emsg in mapM_ (printError noSrcSpan) sdocs >> return Nothing
# else
perror dfs msg = printErrorsAndWarnings dfs msg >> return Nothing
# endif
#endif

-- thExpToStmt :: HscEnv -> TH.Exp -> HsExpr.LStmt RdrName.RdrName
thExpToStmt hscEnv = wrapLHsExpr . thExpToLHsExpr hscEnv
-- wrapLHsExpr ::  HsExpr.LHsExpr RdrName.RdrName -> HsExpr.LStmt RdrName.RdrName
wrapLHsExpr expr =
  noLoc $ LetStmt $ 
#if __GLASGOW_HASKELL__ >= 800
  noLoc $ 
#endif
  HsValBinds (ValBindsIn (Bag.unitBag (HsUtils.mk_easy_FunBind noSrcSpan (Unqual $ mkOccName OccName.varName "__cmCompileExpr") [] expr)) [])
thExpToLHsExpr :: HscEnv -> TH.Exp -> HsExpr.LHsExpr RdrName.RdrName
thExpToLHsExpr hscEnv e = case Convert.convertToHsExpr noSrcSpan e of
#if __GLASGOW_HASKELL__ >= 706
                    Left  msg -> error $ showSDoc (hsc_dflags hscEnv) msg
#else
                    Left  msg -> error $ showSDoc msg
#endif
                    Right expr -> expr

-- unused, but may be useful in future
#if __GLASGOW_HASKELL__ < 706
instance Show b => Show (Expr b) where
    showsPrec p (Var var) = ("Var "++) . (showSDocDebug (ppr var) ++)
    showsPrec _ (Lit l)   = ("Lit "++) . shows l
    showsPrec _ (App e0@(App _ _) e1) = shows e0 . (" `App` "++) . showParen True (shows e1)
    showsPrec _ (App e0 e1)           = showParen True (shows e0) . (" `App` "++) . showParen True (shows e1)
    showsPrec _ (Lam v e)             = ('\\':) . shows v . shows e
    showsPrec _ (Let bs e)            = ("let"++) . shows bs . (" in "++) . shows e
    showsPrec _ (Case _ _ _ _) = ("case"++)
    showsPrec _ (Cast e t)     = ("Cast "++) . showParen True (shows e) . ("<Coercion>"++)
--    showsPrec _ (Note _ _)     = ("Note"++)
    showsPrec _ (Type t)       = (showSDoc (pprType t) ++)
instance Show b => Show (Bind b) where
    showsPrec _ (NonRec b e) = (' ':) . shows b . (" = "++) . shows e
    showsPrec _ (Rec ts )    = ("rec { "++) . foldr (.) id (map hoge ts) . (" } "++)
hoge :: Show b => (b, Expr b) -> ShowS
hoge (b, e) = shows b . (" = "++) . shows e . (" ; "++)
#endif

{- unused. also, anyPrimTy does not appear in ghc-7.* any longer
-- remove the type info to see if they are necessary even when there is no ad-hoc polymorphism
removeTInfo :: Expr b -> Expr b
removeTInfo (App e0 e1) = App (removeTInfo e0) (removeTInfo e1)
removeTInfo (Lam v e)   = Lam v (removeTInfo e)
removeTInfo (Let bs e)  = Let (rtis bs) (removeTInfo e)
removeTInfo (Type t)    = Type anyPrimTy
removeTInfo (Cast e t)  = Cast (removeTInfo e) t
removeTInfo e           = e

rtis (NonRec b e) = NonRec b (removeTInfo e)
rtis (Rec    ts)  = Rec [ (b, removeTInfo e) | (b,e) <- ts ]
-}

compileExprHscMain :: HscEnv -> CoreExpr -> IO HValue
compileExprHscMain hscEnv ce
  =  do let dflags  = hsc_dflags hscEnv
        smpl <- simplifyExpr   dflags ce
#if __GLASGOW_HASKELL__ >= 706
        prep <- corePrepExpr dflags hscEnv smpl
#else
        prep <- corePrepExpr   dflags smpl
#endif
        bcos <- ce2b hscEnv prep
        linkExpr hscEnv noSrcSpan bcos
#if __GLASGOW_HASKELL__ >= 800
            >>= wormhole dflags
#endif


#ifdef GHC6
{-
directLoadObj :: [String] -- ^ visible modules (including package modules). You may omit the Prelude.
           -> [(a, TH.Exp, TH.Type)]
           -> IO (CoreLang.CoreExpr -> Dynamic)
directLoadObj fss tups
    = defaultErrorHandler defaultDynFlags $ do
        hscEnv <- prepareAPI [] fss

#ifdef PRELINK
        hPutStrLn stderr "prelink! (temporarily)"
        compileExpr hscEnv "([], (:), list_para)"
--        compileExpr session "([]::[a], (:)::a->[a]->[a], list_para::[b]->a->(b->[b]->a->a)->a)"
--          compileExpr "([]::[Char], (:)::Char->[Char]->[Char], list_para::[Char]->Int->
#endif

        gm <- mkGlobalAr hscEnv tups
        return $ unsafeDirectExecuteAPI hscEnv gm
-}
unsafeDirectExecuteAPI hscEnv gm ce = unsafePerformIO $ directExecuteAPI hscEnv gm ce
directExecuteAPI :: HscEnv -> GlobalAr -> CoreLang.CoreExpr -> IO a
directExecuteAPI hscEnv gm ce
    = runCoreExpr hscEnv $ ceToCSCE gm ce


-- Note: MagicHaskeller.Primitive = (HValue, TH.Exp, TH.Type)
-- Use
--  typeToTHType :: TyConLib -> Types.Type -> TH.Type
-- if necessary. TyConLib can be undefined here.
compileVar :: HscEnv -> (a, TH.Exp, TH.Type) -> IO CoreSyn.CoreExpr
compileVar hscEnv (_, the, ty)
    = do csce <- compileCoreExpr hscEnv the -- これだと，[| (==)::Char->Char->Bool |]みたいな場合にtheが単にVarE '(==)になってうまくいかない．(ad hocなtyvarがinstantiateされない)
         -- Just (_,csce) <- strToCore session ("let __compileExpr = ("++TH.pprint the ++")::"++TH.pprint (unforall ty))
         let unr = unwrap csce
         putStrLn ("csce = "++show unr)
         case ty of TH.ForallT tvs [] _ -> do let dfs = hsc_dflags hscEnv
                                              simplifyExpr dfs $ foldl CoreSyn.App unr $ replicate (length tvs) $ CoreSyn.Type anyPrimTy
                                              -- CorePrep は 不要なはずではあるが，どうするよ？
                    _                   -> return unr
unwrap (Let (Rec ((_,e):_)) _) = e
-- unwrap (Let (Rec [(_,e)]) _) = e -- こっちだとなぜかダメで，その辺にバグのにほひが....
unwrap st                    = error (show st)
unforall (TH.ForallT _ _ t) = t
unforall t = t

type GlobalMap = Map.Map String CoreSyn.CoreExpr -- Stringの代わりにTH.Nameなどにしようとすると，ちゃんとequivalenceが思い通りの結果になってくれない．．
mkGlobalMap :: HscEnv -> [(a, TH.Exp, TH.Type)] -> IO GlobalMap
-- てゆーか，CoreLang.CoreExprのPrimitiveがCoreSyn.CoreExprの情報を持つのが速い．
-- data CoreExpr a = ... みたいにして，CoreExpr CoreSyn.CoreExprみたいに使う．
mkGlobalMap hscEnv tups =  do ces <- mapM (compileVar hscEnv) tups
                              return $ Map.fromList $ zip (map (\(_,b,_) -> thToBaseString b) tups) ces


{-
-- See Linker.linkDependencies
linkDeps :: Session -> [Module] -> IO Bool
linkDeps session mods = 

てゆーか最初に"([],(:),list_para,lines,take)"みたいなのをcompileExprしてしまえばprelinkされるのでは？


-- obtain the set of modules required to be linked
cscesToNeededModules :: [CoreSyn.CoreExpr] -> [Module]
cscesToNeededModules csces = [ GHC.nameModule n | csce <- csces,
                                                  var  <- csceToVars' csce [],
                                                  let n = Var.varName n,
                                                  isExternalName n,
                                                  not (isWiredInName n) ]

-- Should I define instance Generic (Expr b)?
csceToVars' :: CoreSyn.CoreExpr -> [Var.Var] -> [Var.Var]
csceToVars' (Var var)   = (var:)
csceToVars' (App e0 e1) = csceToVars' e0 . csceToVars' e1
csceToVars' (Lam _ e)   = csceToVars' e
csceToVars' (Let (NonRec _ e0) e1) = csceToVars' e0 . csceToVars' e1
csceToVars' (Let (Rec tups) e)     = foldr (.) (csceToVars' e) [ csceToVars' a | (_,a) <- tups ]
csceToVars' (Case e _ _ tups)      = foldr (.) (csceToVars' e) [ csceToVars' a | (_,_,a) <- tups ]
csceToVars' (Cast e _)             = csceToVars' e
csceToVars' (Note _ e)             = csceToVars' e
csceToVars' _                      = id -- Lit case and Type case

-}


thExpToCSCE :: GlobalMap -> TH.Exp -> CoreSyn.CoreExpr
thExpToCSCE gm ce = ctc [] ce
    where ctc pvs (TH.LamE pvars e)       = foldr CoreSyn.Lam (ctc (pvars++pvs) e) (map (mkStrVar . show . unVarP) pvars)
          ctc pvs (e0 `TH.AppE` e1)       = ctc pvs e0 `CoreSyn.App` ctc pvs e1
          ctc pvs (InfixE (Just e0) e (Just e1)) = lup e `CoreSyn.App` ctc pvs e0 `CoreSyn.App` ctc pvs e1 
          ctc pvs (TH.VarE name) | VarP name `elem` pvs = CoreSyn.Var $ mkStrVar $ show name
          -- VarEの場合，lambda boundの場合と，globalの場合とで扱いが異なる．
          -- スコープをまじめに考えると，lambda boundかどうかをチェックしてからglobalにあるかどうかをみることになる． 
          ctc pvs e                       = lup e
          lup e = case Map.lookup (thToBaseString e) gm of Nothing   -> error (show e ++ ", i.e.,\n" ++ TH.pprint e ++ " : could not convert to CoreSyn.CoreExpr")
                                                           Just csce -> csce
thToBaseString (ConE name) = nameBase name
thToBaseString (VarE name) = nameBase name

unVarP (TH.VarP n) = n
mkIntVar i   = Id.mkUserLocal (mkVarOcc [chr i]) (Unique.getUnique i) anyPrimTy noSrcSpan
mkStrVar str = Id.mkUserLocal (mkVarOcc str) (Unique.getUnique $ mkFastString str) anyPrimTy noSrcSpan


type GlobalAr = Array Int CoreSyn.CoreExpr
mkGlobalAr :: HscEnv -> [(a, TH.Exp, TH.Type)] -> IO GlobalAr
mkGlobalAr hscEnv tups = do ces <- mapM (compileVar hscEnv) tups
                            return $ listArray (0, length tups - 1) ces

ceToCSCE :: GlobalAr -> CoreLang.CoreExpr -> CoreSyn.CoreExpr
ceToCSCE ga ce = ctc (ord 'a'-1) ce
    where ctc dep (CoreLang.Lambda e)       = CoreSyn.Lam  (mkIntVar (dep+1)) $ ctc (dep+1) e
          ctc dep (CoreLang.X n)            = CoreSyn.Var $ mkIntVar (dep-n)
          ctc dep (CoreLang.Primitive n _)    = ga ! n
          ctc dep (e0 CoreLang.:$ e1)       = ctc dep e0 `CoreSyn.App` ctc dep e1




es = map mkIntVar [ord 'e'..]
as = map mkIntVar [128..] -- 無理がある?
xs = map mkIntVar [192..]
hd = mkIntVar (ord 'a')   -- これは引数にしても良い

mkTV :: Int -> Types.Type
mkTV = Types.TV
tvrs = map mkTV [1..]
tvas = map mkTV [2000..]
tvr  = mkTV 0

-- ({} \ hd e1..em a1..an -> {hd e1..em a1..an} let x1 = {e1 a1..an} e1 a1..an in {hd x1 e2..em a1..an} let x2 = {e2 a1..an} e2 a1..an in .. {hd x1..xm-1 em a1..an} let xm = {em a1..an} em a1..an in {hd x1..xm} hd x1..xm
-- てか，一番上がemptyVarSetであることを除けば，あとはundefinedでいいはず．... と思ったけど，schemeEの定義を見た感じlet bindingsの右辺の一番外側に関しては必要みたい．see notes on Aug. 12, 2008
-- ({} \ hd e1..em a1..an -> let x1 = {e1 a1..an} e1 a1..an in let x2 = {e2 a1..an} e2 a1..an in .. let xm = {em a1..an} em a1..an in hd x1..xm
-- という程度の情報があれば十分．

-- (\hd e1..em a1..an -> let x1 = e1 a1..an in .. let xm = em a1..an in hd x1..xm) :: (r1->..->rm->r) -> (a1->..->an->r1)->..->(a1->..->an->rm) -> a1->..->an -> r
hdmnPreped :: Int -> Int -> CoreSyn.CoreExpr
hdmnPreped m 0 = hdmn m 0 -- 要はidを生成するってこと．
hdmnPreped m n = lambdas $ lets $ foldl CoreSyn.App (CoreSyn.Var hd) (map CoreSyn.Var mxs)
    where
       mes = take m es
       mxs = take m xs
       nas = take n as
       lambdas = flip (foldr ($)) (map CoreSyn.Lam (hd : mes ++ nas))
       lets = flip (foldr CoreSyn.Let) binds 
           where binds = zipWith CoreSyn.NonRec mxs $ map appa1an mes
                     where appa1an var = foldl CoreSyn.App (CoreSyn.Var var) $ map CoreSyn.Var nas
-- CorePrep 前のものを生成する場合
-- (\hd e1..em a1..an -> hd (e1 a1..an) .. (em a1..an)) :: (r1->..->rm->r) -> (a1->..->an->r1)->..->(a1->..->an->rm) -> a1->..->an -> r
hdmn m n = lambdas $ foldl CoreSyn.App (CoreSyn.Var hd) $ map appa1an mes
 where appa1an var = foldl CoreSyn.App (CoreSyn.Var var) $ map CoreSyn.Var nas
       mes = take m es
       nas = take n as
       lambdas = flip (foldr ($)) (map CoreSyn.Lam (hd : mes ++ nas))

hdmnty :: Int -> Int -> Types.Type
hdmnty m n = hdty Types.:-> foldr (Types.:->) (foldr (Types.:->) tvr nas) (map (\r -> foldr (Types.:->) r nas) mrs)
    where hdty = foldr (Types.:->) tvr mrs
          mrs  = take m tvrs
          nas  = take n tvas


-- (\e1..em a1..an -> let x1 = e1 a1..an in .. let xm = em a1..an in ai x1 .. xm) -- more exactly, not ai but ai-1 because (!!) counts starting 0
--   :: (a1->..->(r1->..->rm->r)->..->an->r1)->..->(a1->..->(r1->..->rm->r)->..->an->rm) ->
--       a1->..->(r1->..->rm->r)->..->an -> r
-- aimnPreped i m 0 = aimn i m 0 -- これはありえないケース
aimnPreped i m n = lambdas $ foldl CoreSyn.App (CoreSyn.Var (as!!i)) (map CoreSyn.Var mxs)
 where mes = take m es
       mxs = take m xs
       nas = take n as
       lambdas = flip (foldr ($)) (map CoreSyn.Lam (mes ++ nas))
       lets = flip (foldr CoreSyn.Let) binds 
           where binds = zipWith CoreSyn.NonRec mxs $ map appa1an mes
                     where appa1an var = foldl CoreSyn.App (CoreSyn.Var var) $ map CoreSyn.Var nas
-- CorePrep前のものを生成する場合
-- (\e1..em a1..an -> ai (e1 a1..an) .. (em a1..an)) -- more exactly, not ai but ai-1 because (!!) counts starting 0
--   :: (a1->..->(r1->..->rm->r)->..->an->r1)->..->(a1->..->(r1->..->rm->r)->..->an->rm) ->
--       a1->..->(r1->..->rm->r)->..->an -> r
aimn i m n = lambdas $ foldl CoreSyn.App (CoreSyn.Var (as!!i)) $ map appa1an mes
 where appa1an var = foldl CoreSyn.App (CoreSyn.Var var) $ map CoreSyn.Var nas
       mes = take m es
       nas = take n as
       lambdas = flip (foldr ($)) (map CoreSyn.Lam (mes ++ nas))

aimnty :: Int -> Int -> Int -> Types.Type
aimnty i m n = foldr (Types.:->) (foldr (Types.:->) tvr nas) (map (\r -> foldr (Types.:->) r nas) mrs)
    where hdty = foldr (Types.:->) tvr mrs
          mrs  = take m tvrs
          nas  = case splitAt i tvas of (tk,_:dr) -> tk ++ hdty : take (n-i-1) dr -- hdmntyとの違いはここだけ

mkHdmn :: HscEnv -> Int -> Int -> IO Dynamic
mkHdmn hscEnv m n =  do let ce = hdmn m n
                        val <- runCoreExpr hscEnv ce
                        return $ unsafeToDyn undefined (hdmnty m n) val undefined -- (CoreLang.exprToTHExp undefined ce) CoreLangではなくてCoreSynから
mkAimn :: HscEnv -> Int -> Int -> Int -> IO Dynamic
mkAimn hscEnv i m n =  do let ce = aimn i m n
                          val <- runCoreExpr hscEnv ce
                          return $ unsafeToDyn undefined (aimnty i m n) val undefined -- (CoreLang.exprToTHExp undefined ce)
#endif
-- ifdef GHC6

-- こっからプロファイル用


repeatN  n f x = force $ map f $ replicate n x
repeatIO n act = fmap force $ sequence $ replicate n act

-- force (x:xs) = all (x==) xs `seq` x
force = foldr1 seq

instance Eq (Expr a) where
    Var i == Var j = True -- i==j
    Lit l == Lit m = l==m
    App f e == App g i = g==f && e==i
    Lam b e == Lam c f = {- b==c && -} e==f
    Let b e == Let c f = {- b==c && -} e==f
    Case e b t ab == Case f c u bc = e==f {- && b==c && t==u && ab == bc -}
    Cast e c      == Cast f d = e==f {- && c==d -}
--    Note n e == Note m f = {- n==m && -} e==f
    Type t == Type u = True -- t==u



