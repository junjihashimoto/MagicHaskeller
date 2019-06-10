-- 
-- (c) Susumu Katayama
--
module MagicHaskeller.GetTime where
import System.CPUTime
-- import System.Time -- better than Time in Haskell98 Library in that the former supports pretty printing TimeDiff.
import Data.Time
import System.IO
import Control.Monad(liftM2)

batchWrite :: FilePath -> [IO a] -> IO ()
batchWrite filename ios = do is <- batchRun ios
                             hPutStrLn stderr (showCPUTime (sum is) ++ " seconds in total.")
                             writeFile filename $ unlines $ map showCPUTime is 
batchRun :: [IO a] -> IO [Integer]
batchRun []       = return []
batchRun (io:ios) = liftM2 (:) (fmap snd $ time io) (batchRun ios)

time :: IO a -> IO (a, Integer)
time act = do beginCT <- getCurrentTime
              begin <- getCPUTime
              result <- act
              end <- getCPUTime
              endCT <- getCurrentTime
              hPutStrLn stderr (show (diffUTCTime endCT beginCT) ++ " in real,")
--          hPutStrLn stderr (shows (end-begin) " plusminus " ++ shows cpuTimePrecision " picoseconds spent.")
              hPutStrLn stderr (showCPUTime (end-begin) ++ " seconds in CPU time spent.")
              return (result, end-begin)

showZero "" = "0 secs"
showZero s  = s

showCPUTime :: Integer -> String
showCPUTime t = let s     = show t
                    l     = length s
                    (p,f) = splitAt (l - 12) s
                in case compare l 12 of GT -> p ++ '.' : take (13 - lenPrec) f
                                        EQ -> "0." ++ take (13 - lenPrec) f
                                        LT -> "0." ++ replicate (12-l) '0' ++ take (12 - lenPrec) s
lenPrec = length (show cpuTimePrecision)
