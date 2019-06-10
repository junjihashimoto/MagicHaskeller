-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE CPP, ScopedTypeVariables #-}
module MagicHaskeller.TimeOut where

import Control.Concurrent(forkIO, killThread, myThreadId, ThreadId, threadDelay, yield)
import Control.Concurrent.MVar
import Control.Exception -- (catch, Exception(..))
-- import System.Posix.Unistd(getSysVar, SysVar(..))
-- import System.Posix.Process(getProcessTimes, ProcessTimes(..))
-- import System.Posix.Types(ClockTick)
import System.CPUTime
import System.IO.Unsafe(unsafePerformIO)
#if __GLASGOW_HASKELL__ >=702
import System.IO.Unsafe(unsafeDupablePerformIO)
#endif
import Control.Monad(when)

import System.IO

import Debug.Trace -- This IS necessary to monitor errors in the subprocs.

import qualified System.Timeout

import MagicHaskeller.Options(Opt(..))
#ifdef FORCIBLETO
import qualified MagicHaskeller.ForcibleTO as ForcibleTO

unsafeWithPTOOpt :: ForcibleTO.Byte a => Opt b -> a -> Maybe a
unsafeWithPTOOpt opt = let pto = timeout opt
                       in if forcibleTimeout opt then ForcibleTO.unsafeWithPTO pto else unsafeWithPTO pto
maybeWithTOOpt opt = let pto = timeout opt
                     in if forcibleTimeout opt then ForcibleTO.maybeWithTO pto else maybeWithTO seq pto
#else
unsafeWithPTOOpt opt = let pto = timeout opt
                       in unsafeWithPTO pto
maybeWithTOOpt opt = let pto = timeout opt
                     in maybeWithTO seq pto
#endif

unsafeWithPTO :: Maybe Int -> a -> Maybe a
#if 0
-- x #if __GLASGOW_HASKELL__ >= 702
unsafeWithPTO pto a = unsafeDupablePerformIO $ wrapExecution (
#else
unsafeWithPTO pto a = unsafePerformIO $ wrapExecution (
#endif
                                                       maybeWithTO seq pto (return $! a)
                                                      )
maybeWithTO :: (a -> IO () -> IO ()) -- ^ seq or deepSeq(=Control.Parallel.Strategies.sforce). For our purposes seq is enough, because @a@ is either 'Bool' or 'Ordering'.
            -> Maybe Int -> IO a -> IO (Maybe a)
maybeWithTO sq mbt action = maybeWithTO' sq mbt (const action)
newPTO t = return t
{- x
-- x #else
unsafeWithPTO _ = Just
maybeWithTO :: c -> b -> IO a -> IO (Maybe a)
maybeWithTO _ _ action = do a <- action
                            return (Just a)
newPTO = error "not implemented on this platform."
-- x #endif
-}
unsafeOpWithPTO :: Maybe Int -> (a->b->c) -> a -> b -> Maybe c
unsafeOpWithPTO mto op l r = unsafeWithPTO mto (op l r)

-- ソースをみた感じ，MVarやMSampleVarを作るoverheadは無視できそう．
-- data CHTO a = CHTO {timeInMicroSecs :: Int, sv :: MSampleVar (Maybe a)}

{-
unsafeEvaluate :: Int -> a -> Maybe a
unsafeEvaluate t e = unsafePerformIO (withTO t (return e)) -- Should I use Control.OldException.evaluate? I do not want to evaluate long lists deeply. 
-}

maybeWithTO' :: (a -> IO () -> IO ()) -> Maybe Int -> ((IO b -> IO b) -> IO a) -> IO (Maybe a)
maybeWithTO' _   Nothing  action = do a <- action id
                                      return (Just a)
--maybeWithTO' dsq (Just t) action = withTO' dsq t action -- 古いやつ
{-
maybeWithTO' dsq (Just t) action = System.Timeout.timeout t (action undefined) -- System.Timeout.timeoutを使うと速くなる．
                                        `catch` \(e :: SomeException) -> -- trace ("within maybeWithTO': " ++ show e) $
                                                                         return Nothing
-}

maybeWithTO' dsq (Just t) action = do tid <- myThreadId
                                      bracket (forkIO (threadDelay t >> -- hPutStrLn stderr "throwing Timeout" >>
                                                                        throwTo tid (ErrorCall "Timeout")))
                                              (\th -> {- block $ -} killThread th)
                                              (\_ -> fmap Just $ action (yield>>))
                                        `Control.Exception.catch` \(e :: SomeException) -> -- trace ("within maybeWithTO': " ++ show e) $
                                                                         return Nothing

--  'withTO' creates CHTO every time it is called. Currently unused.
-- withTO :: DeepSeq a => Int -> IO a -> IO (Maybe a)
-- withTO timeInMicroSecs action = withTO' deepSeq timeInMicroSecs (const action)
withTO' :: (a -> IO () -> IO ()) -> Int -> ((IO b -> IO b) -> IO a) -> IO (Maybe a)
withTO' dsq timeInMicroSecs action
    = do -- clk_tck <- getSysVar ClockTick
         -- let ticks = fromInteger (clk_tck * toInteger timeInMicroSecs `div` 1000000)
         resMV <- newEmptyMVar
         do
           (catchIt resMV (do
                                   tid <- myThreadId
                                   chtid <- forkIO (do threadDelay timeInMicroSecs
                                                       -- wait deadline -- this line makes sure that timeInMicroSecs has really passed in the process time, but I guess this has no sense, because userTime is shared among Concurrent Haskell threads.
                                                       hPutStrLn stderr "writing Nothing"
                                                       putMVar resMV Nothing
                                                       hPutStrLn stderr "killing the main"
                                                       killThread tid)
                                   -- res <- action (catchYield tid resMV)
                                   res <- action (yield>>)
                                   hPutStrLn stderr "writing Just"
                                   res `dsq` putMVar resMV (Just res)
                                   hPutStrLn stderr "killing the thread for timeout"
                                   killThread chtid))
           hPutStrLn stderr "reading MV"
           readMVar resMV

wrapExecution = id
--wrapExecution = measureExecutionTime

measureExecutionTime act
    = do begin <- getCPUTime
         res <- act
         end <- getCPUTime
         hPutStrLn stderr (show (end - begin))
         return res

-- Catch exceptions such as stack space overflow
catchIt :: (MVar (Maybe a)) -> IO () -> IO ()
#ifdef REALDYNAMIC
catchIt sv act = act -- disable
#else
catchIt sv act = Control.Exception.catch act (handler sv)
#endif

handler sv err = Control.Exception.catch (realHandler sv (err::SomeException)) (handler sv)
-- realHandler sv (AsyncException ThreadKilled) = return () -- If the thread is killed by ^C (i.e. not by another thread), sv is left empty. So, the parent thread can catch ^C while waiting.
{-
#ifdef REALDYNAMIC
-- realHandler sv err = trace (show err) $ putMVar sv Nothing
realHandler sv (ErrorCall str) = trace str $ putMVar sv Nothing
#endif
-}
realHandler sv err = putMVar sv Nothing

catchYield       tid sv action = Control.Exception.catch (yield >> action) (childHandler tid sv)
childHandler     tid sv err    = Control.Exception.catch (realChildHandler tid sv (err::SomeException)) (childHandler tid sv)
realChildHandler tid sv err    = do putMVar sv Nothing
                                    killThread tid
                                    error "This thread must have been killed...."
{-
wait deadline = do ticksNow <- getProcessTimes
                   let tickNow = userTime ticksNow
                   when (tickNow < deadline) $ do threadDelay 20000
                                                  wait deadline
-}
