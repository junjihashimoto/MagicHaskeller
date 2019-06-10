-- 
-- (C) Susumu Katayama
--

module MagicHaskeller.RunAnalytical(
  -- | This module provides analytically-generate-and-test synthesis, i.e. synthesis by filtration of analytically generated (many) expressions.
  --   Actions whose name ends with F use random testing filter (like 'MagicHaskeller.filterThenF') in order to reduce the number of expressions.
  --
  --   ATTENTION: This module is supposed to be used under GHCi environment. Currently it is known not to work when executed as an a.out.
  --   Also, this module is tested only on Linux, and does not work with Windows. Another point is that currently functions in this module only
  --   work with known types appearing in 'MagicHaskeller.CoreLang.defaultPrimitives'.
  
  -- ** Re-exported modules
  module MagicHaskeller, module MagicHaskeller.ExecuteAPI610, module MagicHaskeller.Analytical, 
  {-
  -- ** Synthesizers which will be able to be used with any types but currently do not work with unknown types.
  -- *** All in one actions
  quickStartC, quickStartCF, 
  -- | 'filterGet1' and its friends can be used to synthesize one expression satisfying the given condition. For example,
  -- >>> session <- prepareAPI []
  -- >>> filterGet1_ session $(c [d| f [] = 0; f [a] = 1; f [a,b] = 2 |]) (\f -> f "foobar" == 6)
  -- > \a -> let fa (b@([])) = 0
  -- >           fa (b@(_ : d)) = succ (fa d)
  -- >       in fa a
  filterGet1_, filterGet1, filterGet1BK, 
  -- | Unlike 'filterGet1' and its friends, the following three functions do not print anything but only return results silently.
  getFilt, getFiltF, getAll,  
  -}
  
  {- -- ** Synthesizers which are easier to use that can be used only with types appearing in 'MagicHaskeller.CoreLang.defaultPrimitives' -}
  -- | All in one actions
  quickStart, quickStartF, 
  -- | 'filterGet1' and its friends can be used to synthesize one expression satisfying the given condition. For example,
  {- -- *** counterparts to 'filterGet1_', 'filterGet1', and 'filterGet1BK' -}
  filterGetOne_, filterGetOne, filterGetOneBK, 
  -- | Unlike 'filterGetOne' and its friends, the following three functions do not print anything but only return results silently.
  {- -- *** counterparts to 'getFilt', 'getFiltF', and 'getAll' -}
  synthFilt, synthFiltF, synthAll,
  {- -- *** counterpart to 'noBK' -}
  -- | 'noBKQ' can be used as the background knowledge for showing that no background knowledge functions are used.
  noBKQ
  ) where
import MagicHaskeller
import MagicHaskeller.ExecuteAPI610 -- use ExecuteAPI for GHC 6.8.* and below
import MagicHaskeller.Analytical
import Language.Haskell.TH
import HscTypes(HscEnv)
import MagicHaskeller.Classification(Filtrable)
import System.IO.Unsafe
import MagicHaskeller.GetTime
import System.IO


prepare = prepareAPI [] ["MagicHaskeller.RunAnalytical"]

quickStartC :: (Typeable a) =>
                     SplicedPrims -- ^ target I/O pairs
                     -> SplicedPrims -- ^ I/O pairs for background knowledge functions
                     -> (a -> Bool)  -- ^ test function
                     -> IO ()
quickStartC tgt bk pred = do session <- prepare 
                             tss     <- getFilt session tgt bk pred
                             pprs tss
quickStartCF :: (Filtrable a, Typeable a) =>
                     SplicedPrims -- ^ target I/O pairs
                     -> SplicedPrims -- ^ I/O pairs for background knowledge functions
                     -> (a -> Bool)  -- ^ test function
                     -> IO ()
quickStartCF tgt bk pred = do session <- prepare 
                              tss <- getFiltF session tgt bk pred
                              pprs tss
filterGet1_ :: (Typeable a) => 
               HscEnv               -- ^ session in which synthesized expressions are run 
               -> SplicedPrims      -- ^ target I/O pairs
               -> (a -> Bool)       -- ^ test function
               -> IO ()
filterGet1_ s t p = filterGet1 s t p >> return ()
filterGet1  :: (Typeable a) => 
               HscEnv               -- ^ session in which synthesized expressions are run 
               -> SplicedPrims      -- ^ target I/O pairs
               -> (a -> Bool)       -- ^ test function
               -> IO (Every a)
filterGet1 session tgt = filterGet1BK session tgt noBK
filterGet1BK :: (Typeable a) => 
                HscEnv               -- ^ session in which synthesized expressions are run 
                -> SplicedPrims      -- ^ target I/O pairs
                -> SplicedPrims      -- ^ I/O pairs for background knowledge functions
                -> (a -> Bool)       -- ^ test function
                -> IO (Every a)
filterGet1BK session tgt bk predicate = do tss <- getFilt session tgt bk predicate
                                           putStrLn $ pprint $ fst $ head $ concat tss
                                           return tss

getFilt  :: (Typeable a) =>
                     HscEnv          -- ^ session in which synthesized expressions are run 
                     -> SplicedPrims -- ^ target I/O pairs
                     -> SplicedPrims -- ^ I/O pairs for background knowledge functions
                     -> (a -> Bool)  -- ^ test function
                     -> IO (Every a)
getFilt  session tgt bk pred = filterThen  pred =<< getAll session tgt bk
getFiltF :: (Filtrable a, Typeable a) =>
                     HscEnv          -- ^ session in which synthesized expressions are run 
                     -> SplicedPrims -- ^ target I/O pairs
                     -> SplicedPrims -- ^ I/O pairs for background knowledge functions
                     -> (a -> Bool)  -- ^ test function
                     -> IO (Every a)
getFiltF session tgt bk pred = filterThenF pred =<< getAll session tgt bk
getAll :: (Typeable a) => 
          HscEnv           -- ^ session in which synthesized expressions are run 
          -> SplicedPrims  -- ^ target I/O pairs
          -> SplicedPrims  -- ^ I/O pairs for background knowledge functions
          -> IO (Every a)
getAll  session tgt bk = thExpssToEvery session (getManyTyped tgt bk)


-- Functions appearing from here are easier to use, but they work only for limited types, included in 'defaultPrimitives'.

noBKQ :: Q [Dec]
noBKQ = return []

-- main = quickStart (return [rev]) noBKQ (\f -> f "abcdef" == "fedcba")
{-
main = quickStart [d| f :: Int->Int; f 0 = 0; f 1 = 3; f 2 = 6 |] noBKQ (\f -> f (10::Int) == (30::Int))
-}
{-
main = quickStart [d| f::[a] -> Int; f [] = 0; f [a] = 3; f [a,b] = 6 |] noBKQ (\f -> f "hogehoge" == (24::Int))
-}
{-
main = quickStart [d| f::[a] -> a; f [a] = a; f [a,b] = b; f [a,b,c] = c |] noBKQ (\f -> f "hogehoge" == 'e')
-}
-- | Example of 'quickStart'
--
-- >>> quickStart [d| f [] = 0; f [a] = 1 |] noBKQ (\f -> f "12345" == 5)
-- > \a -> let fa (b@([])) = 0
-- >           fa (b@(c : d)) = succ (fa d)
-- >       in fa a :: forall t2 . [t2] -> Int
-- > ^CInterrupted.
quickStart :: (Typeable a) => 
              Q [Dec]        -- ^ target I/O pairs
              -> Q [Dec]     -- ^ I/O pairs for background knowledge functions
              -> (a -> Bool) -- ^ test function
              -> IO ()
quickStart iops bk pred = do session <- prepare
                             tss <- synthFilt session iops bk pred
                             pprs tss
quickStartF :: (Filtrable a, Typeable a) => 
               Q [Dec]         -- ^ target I/O pairs
               -> Q [Dec]      -- ^ I/O pairs for background knowledge functions
               -> (a -> Bool)  -- ^ test function
               -> IO ()
quickStartF iops bk pred = do session <- prepare
                              tss <- synthFiltF session iops bk pred
                              pprs tss

batchExample = do session <- prepare
                  let f = filterGetOne_ session
                  batchWrite "example.dat" [ f [d| reverse [] = []; reverse [a] = [a]; reverse [a,b] = [b,a]; reverse [a,b,c] = [c,b,a] |] (\r -> r "abcd" == "dcba")
                                           , f [d| switch [] = []; switch [a] = [a]; switch [a,b] = [b,a]; switch [a,b,c] = [c,b,a]; switch [a,b,c,d] = [d,b,c,a]; |] (\s -> s "abcde" == "ebcda")
                                           ]
filterGetOne_ s t p = filterGetOne s t p >> return ()
filterGetOne  :: (Typeable a) => 
                 HscEnv            -- ^ session in which synthesized expressions are run
                 -> Q [Dec]        -- ^ target I/O pairs
                 -> (a -> Bool)    -- ^ test function
                 -> IO (Every a)
filterGetOne session tgt = filterGetOneBK session tgt [d| {} |]
filterGetOneBK :: (Typeable a) => 
                  HscEnv           -- ^ session in which synthesized expressions are run
                  -> Q [Dec]       -- ^ target I/O pairs
                  -> Q [Dec]       -- ^ I/O pairs for background knowledge functions
                  -> (a -> Bool)   -- ^ test function
                  -> IO (Every a)
filterGetOneBK session tgt bk predicate = do tss <- synthFilt session tgt bk predicate
                                             putStrLn $ pprint $ fst $ head $ concat tss
                                             return tss

synthFilt  :: (Typeable a) => 
              HscEnv            -- ^ session in which synthesized expressions are run
              -> Q [Dec]        -- ^ target I/O pairs
              -> Q [Dec]        -- ^ I/O pairs for background knowledge functions
              -> (a -> Bool)    -- ^ test function
              -> IO (Every a)
synthFilt  session tgt bk pred = filterThen  pred =<< synthAll session tgt bk
synthFiltF :: (Filtrable a, Typeable a) => 
              HscEnv             -- ^ session in which synthesized expressions are run
              -> Q [Dec]         -- ^ target I/O pairs
              -> Q [Dec]         -- ^ I/O pairs for background knowledge functions
              -> (a -> Bool)     -- ^ test function
              -> IO (Every a)
synthFiltF session tgt bk pred = filterThenF pred =<< synthAll session tgt bk
synthAll :: (Typeable a) => 
            HscEnv              -- ^ session in which synthesized expressions are run
            -> Q [Dec]          -- ^ target I/O pairs
            -> Q [Dec]          -- ^ I/O pairs for background knowledge functions
            -> IO (Every a)
synthAll  session tgt bk = do tgtdecs <- runQ tgt
                              bkdecs  <- runQ bk
                              thExpssToEvery session (synthTyped tgtdecs bkdecs)
thExpssToEvery :: HscEnv -> [[Exp]] -> IO (Every a)
thExpssToEvery session ess = return $ map (map (\e -> (e, unsafePerformIO $ executeTHExp session e))) ess
-- thExpssToEvery session ess = mapM (mapM (\e -> fmap ((,) e) $ executeTHExp session e)) ess -- これだとダメ. unsafeInterleaveIOをうまく使う手もあるのかも．
