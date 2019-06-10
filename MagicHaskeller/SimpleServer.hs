-- Do not forget -threaded!
--
module MagicHaskeller.SimpleServer(main') where

import MagicHaskeller.LibTH
import MagicHaskeller.LibExcel
import MagicHaskeller.Individual(availableNames, prioritizedNamesToPg)

import GHC hiding (language)
import HscTypes(HscEnv(hsc_IC), InteractiveContext(..))
#if __GLASGOW_HASKELL__ < 706
import DynFlags hiding (Option, language)
#else
import DynFlags hiding (Option, Language, language)
#endif
import qualified MonadUtils as MU -- clearly distinguish MU.liftIO from Control.Monad.IO.Class.liftIO
--  import Panic            (panic)
import Outputable(showPpr)
import Type

import Language.Haskell.TH as TH
import GHC.Paths(libdir)
import Control.Concurrent
import Network
import System.IO
import System.IO.Error(isEOFError)
import Control.Exception
import Data.Char(isAlphaNum, isSpace)
import Text.Html(stringToHtmlString)

import MagicHaskeller.ExpToHtml(QueryOptions(..), defaultQO, expToPlainString, expSigToString, Language(..))

import Unsafe.Coerce

import MagicHaskeller.GetTime
-- import System.Time
import Data.Time

import System.Console.GetOpt
import System.Environment
import System.Exit

import Control.Monad

-- These are for reporting resource usage.
#if __GLASGOW_HASKELL__ >= 700
import GHC.Stats
#endif
import System.Process(system)
import System.Mem(performGC)

import Control.Monad.Par.Class
import Control.Monad.Par.IO
import Control.Monad.IO.Class(liftIO)

-- import Control.Concurrent.ParallelIO(stopGlobalPool)

-- import Data.Map

#ifdef UNIX
-- as suggested by /usr/share/doc/libghc6-network-doc/html/Network.html
import System.Posix hiding (Default)
#endif

#ifdef CABAL
import Paths_MagicHaskeller(getDataFileName)
#endif

-- file:///usr/share/doc/libghc6-network-doc/html/Network.html#t%3APortID
--portID = UnixSocket "mhserver"
portID = PortNumber 55443

trainers = "predicates"

defaultDefault = "(Int,Integer, Double, Ratio Int, Char,(),String)" -- I guess in most cases Int will do.

queryOut = "query.out"

data Flag = Port PortNumber | Socket FilePath | Interactive | RunPSCommand | JustTraining 
          | Depth Int
          | WithDoubleRatio | WithRatio | RatioOnly | WithDouble | Individual FilePath
          | WithAbsents
          | Default (Maybe String)
          | MemoSize (Maybe Int)
          | HTML | PlainText
          | NoTraining | SequentialTraining FilePath | ParallelTraining FilePath
          | PostProcessor String
          | Excel
          | DumpPrimitives

cmdOpts :: [OptDescr Flag]
cmdOpts = [ Option ['p'] ["port-number"]          (ReqArg (Port . toEnum . readOrErr msgp) "PORT_NUMBER")   "use port number PORT_NUMBER (default, using -p 55443)"
          , Option ['u'] ["unix-socket"]          (ReqArg Socket "SOCKET_FILEPATH")      "use socket file SOCKET_FILEPATH"
          , Option ['i'] ["interactive","stdio"]  (NoArg  Interactive)                   "use the standard I/O for query and printing results"
          , Option ['r'] ["run-ps-command"]       (NoArg  RunPSCommand)                  "(after training) run the ps command and exit"
          , Option ['j'] ["just-training"]        (NoArg  JustTraining)                  "just training (usually for benchmarking)" 
          , Option ['d'] ["depth"]                (ReqArg (Depth . readOrErr msgd) "SEARCH_DEPTH") $ 
                                                                                         "search depth (" ++ shows (depth defaultQO) "by default)"
          , Option ['q'] ["query-limit"]          (OptArg (MemoSize . fmap (readOrErr msgd)) "QUERY_TYPE_SIZE_LIMIT") $ 
                                                                                         "only look up the memo entries when types with size less than this value are queried. Values for other types are recomputed every time. If no value is given (default), this means there is not limit and  all entry types are looked up when queried. Setting this value does not affect the time for looking up already substantiated entries. However, setting it to about 8 dramatically reduces the heap space usage, while increasing the time for training."
          , Option ['b'] ["with-double-ratio"]              (NoArg  WithDoubleRatio)                  "use the library with Double-related and (Ratio Int)-related functions. This requires more memory, but fractional numbers become available. This overrides --individual, -w, --ratio-only, and -2."
          , Option ['w'] ["with-ratio"]              (NoArg  WithRatio)                  "use the library with (Ratio Int)-related functions. This requires more memory, but fractional numbers become available. This overrides -b, --individual, --ratio-only, and -2."
          , Option [] ["ratio-only"]              (NoArg  RatioOnly)                  "use the library only including (Ratio Int)-related functions. This is introduced for debugging, but there may be other uses. This overrides -b, -w, --individual, and -2."
          , Option ['2'] ["with-double"]              (NoArg  WithDouble)                  "use the library with Double-related functions. This requires more memory, but fractional numbers become available. This overrides -b, -w, --ratio-only, and --individual."
          , Option [] ["individual"]              (ReqArg Individual "FILEPATH")         "itemize library functions and their priorities in FILEPATH. This overrides -b, -w, --ratio-only, and -2. Note that only functions (and non-functions) appearing in the bundled primitives.txt can be used unless you hack the source."
          , Option [] ["dump-primitives"]         (NoArg DumpPrimitives)                 "dump a sample primitive file (to be used with --dump-primitives=...) to stdout and exit. The bundled primitives.txt is more user-friendly, but this option is useful if you hack the source and add some primitives."
          , Option ['a'] ["absents"]              (NoArg  WithAbsents)                   "generate functions with unused arguments in addition to other useful ones" 
#if __GLASGOW_HASKELL__ >= 706
          , Option []    ["default"]              (OptArg Default "DEFAULT_TYPES")       "default declaration for type defaulting (--default='(Int,Integer,Double, Ratio Int, Char,(),String)' by default). The outermost parens can be omitted."
#endif
          , Option ['h'] ["html"]                 (NoArg  HTML)                          "force printing in HTML even in the interactive mode"
          , Option []    ["plain-text"]           (NoArg  PlainText)                     "force printing in plain text"
          , Option ['n'] ["no-training"]          (NoArg  NoTraining)                    "start service without training beforehand"
          , Option ['s'] ["sequential-training"]  (ReqArg SequentialTraining "PREDICATES_FILEPATH") 
                       "substantiate the memo table using the predicates in PREDICATES_FILEPATH. (Just setting this option would not disable parallel training. If you want to use only sequential training, use `-n -s PREDICATES_FILEPATH'.)"
          , Option ['t'] ["threaded-training",
                          "parallel-training"]    (ReqArg ParallelTraining   "PREDICATES_FILEPATH")
                       "substantiate the memo table using the predicates in PREDICATES_FILEPATH in parallel  (default, using -t 'predicates'). This option can be set along with -s, then sequential training will be done after parallel training."
          , Option []    ["postprocessor"]        (ReqArg PostProcessor "POSTPROCESSOR") "use POSTPROCESSOR as the postprocessor (default, using --postprocessor=postprocess). You can use --postprocessor=id to see the internal representation."
          , Option ['x'] ["excel"]                (NoArg Excel) "use the library for Excel synthesis, disable defaulting to integral numbers, and ppExcel as the postprocessor. You can specify `--excel --postprocessor=blah' in order to use a different postprocessor."
          ]
    where readOrErr msg xs = case reads xs of [(i,"")] | i>=0 -> i
                                              _        -> error msg
          msgp = "--port-number (or -p) takes a non-negative integral value specifying the port number."
          msgd = "--depth (or -d) takes a non-negative integral value specifying the depth bound."
          msgq = "--query-limit (or -q) takes a non-negative integral value specifying the type size bound for memoization."
readOpts :: IO ([Flag], [String])
readOpts = do argv     <- getArgs
              case (getOpt Permute cmdOpts argv) of
                            (o,n,[]  ) -> return (o,n)
                            (_,_,errs) -> do hPutStrLn stderr (concat errs)
                                             usage
                                             exitFailure
usage :: IO ()
usage = do progname <- getProgName
           hPutStrLn stderr $ usageInfo ("Usage: "++progname++" [OPTION...]") cmdOpts

data HowToServe = Network PortID | STDIO | PS | NoService
data Format     = DefaultFormat | ForceHTML | ForcePlain deriving Eq
data FunctionSet = PGFull | PGWithDoubleRatio | PGWithRatio | PGRatio | PGWithDouble | PGExcel | PGIndividual FilePath
data ServerOptions = SO {howToServe :: HowToServe, queryOptions :: QueryOptions, functionSet :: FunctionSet, memoSize :: Maybe Int, defaultTypes :: Maybe String, format :: Format, sequentialTraining :: Maybe FilePath, parallelTraining :: Maybe FilePath, postprocessor :: String, language :: Language, dumpPrimitives :: Bool}
defaultSO = SO {howToServe = Network portID, queryOptions = defaultQO, functionSet = PGFull, memoSize = Nothing, defaultTypes = Just defaultDefault, format = DefaultFormat, sequentialTraining = Nothing, parallelTraining = Just trainers, postprocessor = "postprocess", language = LHaskell, dumpPrimitives = False}

procFlags :: [Flag] -> ServerOptions
procFlags = foldl procFlag defaultSO
procFlag :: ServerOptions -> Flag -> ServerOptions
procFlag st (Port   i)   = st{howToServe = Network (PortNumber i)}
#ifdef UNIX
procFlag st (Socket fp)  = st{howToServe = Network (UnixSocket fp)}
#endif
procFlag st Interactive  = st{howToServe = STDIO}
procFlag st RunPSCommand = st{howToServe = PS}
procFlag st JustTraining = st{howToServe = NoService}
procFlag st (Depth d)    = st{queryOptions = (queryOptions st){depth = d}}
procFlag st (MemoSize m) = st{memoSize = m}
procFlag st WithDoubleRatio = st{functionSet = PGWithDoubleRatio}
procFlag st WithRatio    = st{functionSet = PGWithRatio}
procFlag st RatioOnly    = st{functionSet = PGRatio}
procFlag st WithDouble   = st{functionSet = PGWithDouble}
procFlag st (Individual file) = st{functionSet = PGIndividual file}
procFlag st WithAbsents  = st{queryOptions = (queryOptions st){absents = True}}
#if __GLASGOW_HASKELL__ >= 706
procFlag st (Default ms) = st{defaultTypes = ms}
procFlag st Excel        = st{defaultTypes = Just "Int,Double", postprocessor = "ppExcel", functionSet = PGExcel, language = LExcel}
#else
procFlag st (Default ms) = error "The --default option is not available. Please rebuild with GHC >= 7.6."
procFlag st Excel        = st{postprocessor = "ppExcel", functionSet = PGExcel, language = LExcel}
#endif
procFlag st HTML         = st{format = ForceHTML}
procFlag st PlainText    = st{format = ForcePlain}
procFlag st NoTraining   = st{sequentialTraining = Nothing, parallelTraining = Nothing}
procFlag st (SequentialTraining fp) = st{sequentialTraining = Just fp}
procFlag st (ParallelTraining   fp) = st{parallelTraining   = Just fp}
procFlag st (PostProcessor pp)      = st{postprocessor = pp}
procFlag st DumpPrimitives = st{dumpPrimitives = True}

main' :: String -> IO ()
main' versionString = do
  (flags, _args) <- readOpts
  let so = procFlags flags
  if dumpPrimitives so then dump else main'' versionString so

dump = putStrLn $ unlines $ "## Lines starting with # will be ignored, so you can exclude individual functions by commenting them out. The number at the beginning of each line represents the priority, where 0 means the most prioritized." : map ("0 "++) availableNames

main'' versionString so = do
  hPutStrLn stderr versionString
  qhandle <- openFile queryOut AppendMode
  beginCT <- getCurrentTime
  hPutStrLn stderr ("started at " ++ show beginCT)

  pgf <- case (functionSet so, memoSize so) of 
                                      (PGFull,      Nothing) -> liftIO mkPgFull
                                      (PGFull,      Just sz) -> return $ pgfulls !! sz
                                      (PGWithDoubleRatio, Nothing) -> return $ pgWithDoubleRatio
                                      (PGWithDoubleRatio, Just sz) -> return $ pgWithDoubleRatios !! sz
                                      (PGWithRatio, Nothing) -> return $ pgWithRatio
                                      (PGWithRatio, Just sz) -> return $ pgWithRatios !! sz
                                      (PGRatio,     Nothing) -> return $ pgRatio
                                      (PGRatio,     Just sz) -> return $ pgRatios !! sz
                                      (PGWithDouble, Nothing) -> liftIO mkPgWithDouble
                                      (PGWithDouble, Just sz) -> return $ pgWithDoubles !! sz
                                      (PGExcel,      Nothing) -> liftIO mkPgExcel
                                      (PGExcel,      Just sz) -> liftIO $ mkPgExcels sz
                                      (PGIndividual file, mb) -> do cs <- readFile file
                                                                    prioritizedNamesToPg mb $ map parsePrioritizedName $ filter ((/='#').head) $ filter (not.null) $ lines cs

  hscEnv <- prepareGHCAPI ["MagicHaskeller.Minimal","MagicHaskeller.FastRatio"] -- (Fast)Ratio must be here if Ratio is referred by the default declaration.
#if __GLASGOW_HASKELL__ >= 706
  hscEnv <- case defaultTypes so of Nothing  -> return hscEnv
                                    Just def -> declareDefaults hscEnv def
#endif
  let stat = (versionString, qhandle, so, pgf, hscEnv)
  case (parallelTraining so, sequentialTraining so) of
    (Just fp, Just fs) -> do -- In this case, we make sure sequantial training starts after all the parallel training processes have finished. (The sequential training will be done for testing and benchmarking purposes.)
         trainPara stat fp
         trainSeq stat fs
    (Just fp, Nothing) -> do -- In this case, every synthesis should be done in parallel. The service is started while training, but we prefer to be notified when all the training processes finish.
         forkIO $ trainPara stat fp
         return ()
    (Nothing, Just fs) -> trainSeq stat fs
    (Nothing, Nothing) -> return ()
  hSetBuffering qhandle LineBuffering
  case howToServe so of
    Network pid ->
      withSocketsDo $ do
#ifdef UNIX
          installHandler sigPIPE Ignore Nothing -- as suggested by /usr/share/doc/libghc6-network-doc/html/Network.html
#endif
          socket <- listenOn pid
          loop stat socket
    STDIO       -> interactive stat
    PS          -> do pgn <- getProgName
                      system $ "ps u -C "++pgn
                      return () -- stopGlobalPool
    NoService   -> return () -- stopGlobalPool

parsePrioritizedName :: String -> (Int,String)
parsePrioritizedName str = case reads str of [] -> error "error while parsing the primitives file."
                                             [(i,s)] -> (i, dropWhile isSpace s)

#if __GLASGOW_HASKELL__ >= 706
declareDefaults hscEnv str
  = runGhc (Just libdir) $ do
    setSession hscEnv
    tupTy <- exprType $ "undefined :: (" ++ str ++ ")"
    case splitTyConApp_maybe tupTy of 
      Nothing                     -> error $ str ++ " : invalid default type sequence"
      Just (_tuptc, defaultTypes) -> setSession hscEnv{hsc_IC = (hsc_IC hscEnv){ic_default = Just defaultTypes}} >> getSession

#endif

waitUntil0 :: MVar Int -> IO Int
waitUntil0 mv = do i <- readMVar mv
                   yield
                   if (i>0) then waitUntil0 mv else return i

loop stat socket = do
                 (handle, hostname, _portnum) <- accept socket
                 hPutStr stderr $ "Connection from " ++  hostname ++ ".\n"
                 tid <- forkIO $ do hSetBuffering handle LineBuffering
                                    answerHIO stat handle handle
                                    hPutStrLn stderr "closing"
                                    hClose handle
                 loop stat socket

{- pgfの計算を入れんといかん．
-- same as main, with option `--interactive --no-training'
mainstd = do hscEnv <- prepareGHCAPI ["MagicHaskeller.Minimal"]
             qhandle <- openFile queryOut AppendMode
             hSetBuffering qhandle LineBuffering
             interactive qhandle defaultSO pgf hscEnv
-}

interactive stat = sequence_ $ repeat $ hPutStrLn stderr "\\f -> ?" >> answerHIO stat stdin stdout

tryOpening fp onException onSuccess = do
  r <- try $ openFile fp ReadMode
  case r :: Either IOException Handle of
    Left e -> do
#ifdef CABAL
         fn <- getDataFileName ("MagicHaskeller/"++fp)
         s <- try $ openFile fn ReadMode
         either onException onSuccess (s :: Either IOException Handle)
#else
         onException e
#endif
    Right h -> onSuccess h

trainSeq stat fp = do
  tryOpening fp (\e -> hPutStrLn stderr ("An exception occurred while opening `"++fp++"'. The learner has not been trained sequentially beforehand."))
                (\h -> do time $ do
                            processTrainers (preferPlain stat) h
                            hPutStrLn stderr "In total,"
                          return ())
  hPutStrLn stderr "performing GC..."
  performGC
  hPutStrLn stderr "done.\a"
#if __GLASGOW_HASKELL__ >= 706
  gcStatsAvailable <- getGCStatsEnabled
  when gcStatsAvailable $ getGCStats >>= print
#endif
processTrainers stat h = do
  (r,t) <- time $ try (answerHIO stat h stdout)
  case r of Left e | isEOFError e -> do hClose h
                                        return t
                   | otherwise    -> error ("While training:\n" ++ show e)
            Right () -> fmap (+t) $ processTrainers stat h

trainPara stat fp =
  tryOpening fp (\e -> hPutStrLn stderr ("An exception occurred while opening `"++fp++"'. The learner has not been trained in parallel beforehand."))
                (\h -> do  
                   cs <- hGetContents h
                   beginCT <- getCurrentTime
                   runParIO $ trainParaPar (preferPlain stat) $ lines cs
--                   trainParaIO (preferPlain so) pgf hscEnv $ lines cs
                   endParaCT <- getCurrentTime
                   hPutStrLn stderr "All the training processes have finished."
                   hPutStrLn stderr $ show (diffUTCTime endParaCT beginCT) ++ " have passed since the training started.")
trainParaIO stat css = do
                   numUnfinished <- newMVar (length css)
                   mapM_ (processTrainerPara (preferPlain stat) numUnfinished) css
                   waitUntil0 numUnfinished
processTrainerPara stat numUnfinished line = do
  mid <- myThreadId
  forkIO $ ((answerSIO stat line >>= \(_,k) -> k `seq` modifyMVar_ numUnfinished (return . pred))
             `Control.Exception.catch` \exception -> throwTo mid (exception::SomeException)
           )
  return ()
preferPlain (vs, qh, so, pgf, he) = (vs, qh, preferPlain' so, pgf, he)
preferPlain' so = case format so of DefaultFormat -> so{format=ForcePlain}
                                    _             -> so

trainParaPar :: (String, Handle, ServerOptions, ProgGenSF, HscEnv) -> [String] -> ParIO ()
trainParaPar stat css = do ivks <- mapM (\line -> spawn $ liftIO $ fmap snd $ answerSIO stat line) css
                           ks <- mapM get ivks
                           sum ks `seq` return ()

filterCompile :: GhcMonad m => String -> String -> m (ProgGenSF -> Bool -> [[Exp]])
filterCompile postprocessor predStr = fmap unsafeCoerce (compileExpr ("f1EF " ++ postprocessor ++ " (\\f -> "++predStr++")")) --  :: m GHC.HValue)

-- InteractiveEval.exprTypeで明示的に型推論するってことは，IntegerでなくIntでdefaultしたりしやすいってことか．めんどくさければとりあえずはエラーにしてmonomorphicなのを要求してもよい．

-- package ghcのType.Typeもそんなにややこしい型じゃないし，exprTypeから変換するのが確実でいいか．
-- exprTypeやってcompileExprするのは二度手間ではあるが．


-- てゆーか，もしpackage MagicHaskellerを毎回読み込まなければならないとすればそっちの方がtime consuming.

filterCompileIO :: GhcMonad m => String -> String -> m (ProgGenSF -> Bool -> IO [[Exp]])
filterCompileIO postprocessor predStr = fmap unsafeCoerce (compileExpr ("MagicHaskeller.Minimal.f1EFIO " ++ postprocessor ++ " (\\f -> (("++predStr++") :: Bool))"))

{- 使わんかも．
ghcTypeToType :: TyConLib -> GHC.Type -> MagicHaskeller.Types.Type
ghcTypeToType _      (TyVarTy var)    = strToVarType $ show var
ghcTypeToType tcl    (AppTy t0 t1)    = ghcTypeToType tcl t0 `TA` ghcTypeToType tcl t1
ghcTypeToType tcl    (TyConApp tc ts) = let nstr = showSDoc (pprParenSymName tc)
                                            tc'  = case Data.Map.lookup nstr (fst tcl) of 
                                              Nothing -> TC $ (-1 - bakaHash nstr) -- error "nameToTyCon: unknown TyCon"
                                              Just c  -> TC c
                                        in foldl TA tc' $ map (thcTypeToType tcl) ts
ghcTypeToType tcl    (FunTy t0 t1)    = ghcTypeToType tcl t0 :-> ghcTypeToType tcl t1
ghcTypeToType tcl    (ForAllTy v ty)  = panic "Please make it monomorphic by giving a type signature."
-}


-- stdinとstdoutで動作確認できるように，inとoutを分ける．
answerHIO :: (String, Handle, ServerOptions, ProgGenSF, HscEnv) -> Handle -> Handle -> IO ()
answerHIO (versionString, qhandle, so, pgf, hscEnv) ihandle ohandle = do
  inp <- hGetLine ihandle -- hGetContents ihandleだと，最後に改行文字を入れちゃった時面倒．あと，hGetContentsの方がだいぶ遅いみたい．
  case lex inp of [(":",rest)] -> if filter (not . isSpace) rest == "version" then hPutStrLn ohandle versionString else hPutStrLn ohandle $ inp ++ " : command unknown"
                  _            -> do
                                let (so', pred) = case reads inp of [(qo, pred)] -> (so{queryOptions=qo}, pred)
                                                                    []           -> (so, inp)
                                putStrLn ("the predicate is "++pred)
                                hPutStrLn qhandle pred
                                (out,_) <- answerSIO (versionString, qhandle, so', pgf, hscEnv) pred
                                hPutStrLn ohandle out

answerSIO :: (a, b, ServerOptions, ProgGenSF, HscEnv) -> String -> IO (String, Int)
answerSIO (_, _, so, pgf, hscEnv) pred = do
  cmpd <- runGhc (Just libdir) $ setSession hscEnv >> compileOrFail (postprocessor so) pred
  case cmpd of Left (funIO, sig) -> do
                          let e2s   = case howToServe so of
                                              STDIO | not $ format so == ForceHTML -> expToPlainString
                                              _     | format so == ForcePlain      -> expToPlainString
                                                    | otherwise  -> expSigToString (language so) pred sig
                          result <- funIO pgf $ absents $ queryOptions so
                          let ess = take (depth $ queryOptions so) result
                                    
--                          let ess = take (depth $ queryOptions so) $ fun pgf $ absents $ queryOptions so
                          
                          return  (unlines $ map (concat . map e2s) ess,  length $ last ess)
               Right errstr -> return ('!' : encodeBR (stringToHtmlString errstr), length errstr) -- 本当はこれもhowToServeにあわせるべき

compileOrFail :: String -> String -> Ghc (Either (ProgGenSF -> Bool -> IO [[Exp]], String) String)
compileOrFail postproc predStr = handleSourceError (return . Right . show) $ do
                          funIO <- filterCompileIO postproc predStr 
#if __GLASGOW_HASKELL__ >= 706
    -- In this case, the type obtained by exprType is polymorphic, so there is no point in adding the type signature.
                          let sig = ""
#else
                          ty  <- exprType $ "\\f->("++predStr++")`asTypeOf`True" -- `asTypeOf` True をいれないと、 predStr = "f True True" のときにserverがpanic!になる。
                          let sig   = " :: " ++ removeQuantification (map crlfToSpace $ showPpr $ extractArgTy ty)
#endif
                          return $ Left (funIO, sig)

-- Note that the following causes a type mismatch with ghc>=8.0 because mkForAllTys takes TyBinder (which includes visibility info).
#if __GLASGOW_HASKELL__ < 706
-- assumes rank-1 types
extractArgTy ty = case splitForAllTys ty of (tvs, fty) -> case splitFunTys fty of (args, _bool) -> mkForAllTys tvs $ mkFunTys (Prelude.init args) $ last args
#endif

crlfToSpace '\n' = ' '
crlfToSpace c    = c

--  エラーコード中にもし\nがあった場合，<br>で置き換え．なぜかstringToHtmlStringはやってくれない．
encodeBR = concat . map (++"<br>") . lines



-- exprType quantifies each Primitive type with `GHC.Types.' and `GHC.Bool., but mueval does not like this kind of quantification.
-- There exist quicker algorithms, but anyway the time for quantification removal should be ignorable.
removeQuantification "" = ""
removeQuantification xs@(y:ys) = case span (/='.') xs of (tk,'.':dr) | all isAlphaNum tk -> removeQuantification dr
                                                                     | otherwise         -> reverse (dropWhile isAlphaNum $ reverse tk) ++ removeQuantification dr
                                                         (tk,"")     -> tk

prepareGHCAPI :: [FilePath] -> IO HscEnv
prepareGHCAPI allfss = runGhc (Just libdir) $ do
          dfs     <- getSessionDynFlags
#if __GLASGOW_HASKELL__ >= 700
-- x # if __GLASGOW_HASKELL__ >= 708
-- x           let newf = xopt_set dfs{packageFlags = [ packageNameToFlag "MagicHaskeller" ], optLevel=2, parMakeCount=Nothing} Opt_ExtendedDefaultRules -- parMakeCount=Nothing corresponds to -j. See http://downloads.haskell.org/~ghc/7.10.2/docs/html/libraries/ghc-7.10.2/DynFlags.html -- but seemingly this does not make the code faster, so is commented out.
-- x # else
          let newf = xopt_set dfs{packageFlags = [ packageNameToFlag "MagicHaskeller" ], optLevel=2}
# if __GLASGOW_HASKELL__ >= 800
                ExtendedDefaultRules
# else
                Opt_ExtendedDefaultRules
# endif
-- x # endif
#else
          let newf = dfs{packageFlags = [ packageNameToFlag "MagicHaskeller" ], optLevel=2}
#endif
          setSessionDynFlags newf   -- result abandoned

#if __GLASGOW_HASKELL__ >= 700
          modules <- mapM (\fs -> fmap (\x -> (x,Nothing)) $ findModule (mkModuleName fs) Nothing) ("Prelude":allfss)
#else
          modules <- mapM (\fs -> findModule (mkModuleName fs) Nothing) ("Prelude":allfss)
#endif
#if __GLASGOW_HASKELL__ >= 700
          setContext [ IIDecl $ (simpleImportDecl . mkModuleName $ moduleName){GHC.ideclQualified = False} | moduleName <- "Prelude":allfss ] -- GHC 7.4
#else
          setContext [] modules
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
