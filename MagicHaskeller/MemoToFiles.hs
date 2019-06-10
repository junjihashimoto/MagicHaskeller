-- 
-- (c) Susumu Katayama
--
module MagicHaskeller.MemoToFiles where
import System.IO
import System.Directory(doesFileExist, createDirectoryIfMissing)
import MagicHaskeller.ShortString
import Data.ByteString.Char8      as C
import Data.ByteString.Lazy.Char8 as LC

import Control.Monad.Search.Combinatorial
import MagicHaskeller.DebMT
import MagicHaskeller.Types

import MagicHaskeller.PriorSubsts
import Data.Monoid
import Data.Ix



-- copied from ProgGen.lhs. toMemo削って型変えた．てゆーかそれ以前に，散らばってるfreezePSをProgramGenerator辺りにまとめたい気も
freezePS :: Search m => Type -> PriorSubsts m (Bag e) -> m (Possibility e)
freezePS ty ps
    = let mxty = maxVarID ty -- `max` maximum (map maxVarID avail)
      -- in toMemo $ mergesortDepthWithBy (\(xs,k,i) (ys,_,_) -> (xs `mappend` ys, k, i)) (\(_,k,_) (_,l,_) -> k `compare` l) $ unPS ps emptySubst (mxty+1)
      in mergesortDepthWithBy (\(xs,k,i) (ys,_,_) -> (xs `mappend` ys, k, i)) (\(_,k,_) (_,l,_) -> k `compare` l) $ fps mxty ps
      -- in toMemo $ mergesortDepthWithBy (\(xs,k,i) (ys,_,_) -> (xs `mappend` ys, k, i)) (\ (_,k,_) (_,l,_) -> normalize (apply k ty) `compare` normalize (apply l ty)) $ fps mxty ps
fps :: Search m => TyVar -> PriorSubsts m es -> m (es,[(TyVar, Type)],TyVar)
fps mxty (PS f) = do (exprs, sub, m) <- f emptySubst (mxty+1)
                     return (exprs, filterSubst sub mxty, m)
    where filterSubst :: Subst -> TyVar -> [(TyVar, Type)]
          filterSubst sub  mx = [ t | t@(i,_) <- sub, inRange (0,mx) i ] -- note that the assoc list is NOT sorted.

-- これってProgGen限定か
memoPSRTIO :: ShortString b =>
             MemoCond
                 -> MapType (Matrix (Possibility b))
                 -> (Type -> PriorSubsts (RecompT IO) [b]) -- ^ This will be used instead if the entry is not found.
                 -> Type -> PriorSubsts (RecompT IO) [b]
memoPSRTIO policy mt f t = PS $ \subst mx ->
              let (tn, decoder) = encode t mx
              in (fmap (\ (exprs, sub, m) -> (exprs, retrieve decoder sub `plusSubst` subst, mx+m)) $ (memoRTIO policy (\ty depth -> return $ unMx (lookupMT mt ty) !! depth) (\u ->  freezePS u (f u)) tn))


memoRTIO :: ShortString b =>
             MemoCond
                 -> (Type -> Int -> IO [b]) -- ^ look up the memoization table in the RAM.
                 -> (Type -> RecompT IO b) -- ^ This will be used instead if the entry is not found.
                 -> Type -> RecompT IO b
memoRTIO policy lor f t = RcT $ memoer policy lor (\ty -> unRcT (f ty)) t
memoer :: ShortString b =>
          MemoCond
          -> (Type -> Int -> IO [b])
          -> (Type -> Int -> IO [b])
          -> Type -> Int -> IO [b]
memoer policy lor f ty depth
    = do memotype <- policy ty depth
         case memotype of Recompute -> compute
                          Ram       -> lor ty depth
                          Disk   fp | Prelude.length filepath < 250 -> do -- If I remember correctly, UNIX does not permit filenames longer than 255 letters.
                                             -- System.IO.putStrLn "Hit!"
                                             -- System.IO.putStrLn ("Directory name: "++directory)
                                             -- System.IO.putStrLn ("FilePath: "++ filepath)
                                             createDirectoryIfMissing True directory
                                             memoToFile readBriefly showBriefly filepath compute
                                    | otherwise -> compute -- This is safer than Ram. Still this behavior can be overridden by specifying the MemoCond accordingly
                                                           -- (though that can be unsafe).
                              where
                                directory = fp++shows depth "/" -- care about Windows later....
                                filepath  = directory ++ show ty
      where compute = f ty depth
data MemoType = Recompute -- ^ Recompute instead of memoizing.
              | Ram       -- ^ Use the memoization table based on lazy evaluation, like in older versions.
              | Disk FilePath -- ^ Use the directory specified by @FilePath@ as the persistent memoization table.
type MemoCond = Type -> Int -> IO MemoType -- IOを返す．つまり，メモリやハードディスクの空きによっても変えられるようにする．


-- | General-purposed memoizer (This could be put in a different module.)
memoToFile :: (C.ByteString -> Maybe a) -- ^ parser
           -> (a -> LC.ByteString)      -- ^ printer
           -> FilePath -- ^ where to memoize
           -> IO a     -- ^ invoked if there is no such file
           -> IO a
memoToFile parser printer filepath compute
    = let write = do result <- compute
                     LC.writeFile filepath (printer result)
                     return result
      in do there <- doesFileExist filepath
            if there then do cs <- C.readFile filepath -- Read strictly, and close (not semi-close) it. System.IO.readFile cannot achieve this behavior. 
                             case parser cs of Just x -> return x
                                               _      -> do -- If the file is broken, just fix it. でも誰かが書き込み中だと困る?
                                                              System.IO.hPutStrLn stderr ("File " ++ filepath ++ " was broken.")
                                                              write
                     else write
