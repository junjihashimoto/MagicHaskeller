-- 
-- (c) Susumu Katayama
--
module MagicHaskeller.ShortString where
import Data.ByteString.Char8      as C -- This seems quicker, except that C.cons requires O(n).
import Data.ByteString.Lazy.Char8 as LC
import Data.Char
import MagicHaskeller.CoreLang
import MagicHaskeller.Types
import Data.Int
import Data.Word

-- LC.cons' だと多分ダメ

showBriefly :: ShortString a => a -> LC.ByteString
showBriefly = flip showsBriefly LC.empty
readBriefly :: ShortString a => C.ByteString -> Maybe a
readBriefly = fmap fst . readsBriefly

class ShortString a where
    showsBriefly :: a -> LC.ByteString -> LC.ByteString
    readsBriefly :: C.ByteString -> Maybe (a,C.ByteString)  --  ReadS a -- Maybe の方が速い? てゆーか，parse errorの割合はすごく少ないはずなのでerrorとしてcatchした方が速いはず．と思ったけど，lazyなデータなので正しくcatchできないか．

instance ShortString a => ShortString [a] where
    showsBriefly []     = LC.cons ']'
    showsBriefly (x:xs) = showsBriefly x . showsBriefly xs
    readsBriefly cs = case C.uncons cs of Nothing       -> fail "parse error"
                                          Just (']',ds) -> return ([],ds)
                                          _             -> do (x, ds) <- readsBriefly cs
                                                              (xs,es) <- readsBriefly ds
                                                              return (x:xs, es)
instance ShortString Bool where
    showsBriefly True   = LC.cons 'T'
    showsBriefly False  = LC.cons 'F'
instance ShortString CoreExpr where
    showsBriefly (Lambda ce)   = (LC.cons '\\') . showsBriefly ce
    showsBriefly (X i)         = (LC.cons 'X')  . showsBriefly i
    showsBriefly (Primitive i) = (LC.cons 'p')  . showsBriefly i
    showsBriefly (PrimCon   i) = (LC.cons 'P')  . showsBriefly i
    showsBriefly (Context _) = LC.cons 'C'
    showsBriefly (c :$ e)      = (LC.cons '$')  . showsBriefly c . showsBriefly e
    readsBriefly cs = case C.uncons cs of -- Int(Nat)と1文字め一緒に1バイトにできないか?あと，lambdaは続くのでまとめられそう．
                                          Just ('\\',xs) -> do (ce,ys) <- readsBriefly xs
                                                               return (Lambda ce, ys)
                                          Just ('X', xs) -> do (i, ys) <- readsBriefly xs
                                                               return (X i, ys)
                                          Just ('p', xs) -> do (i, ys) <- readsBriefly xs
                                                               return (Primitive i, ys)
                                          Just ('P', xs) -> do (i, ys) <- readsBriefly xs
                                                               return (PrimCon   i, ys)
                                          Just ('$', xs) -> do (c, ys) <- readsBriefly xs
                                                               (e, zs) <- readsBriefly ys
                                                               return (c :$ e, zs)
                                          Just ('C', xs) -> fail "readsBriefly for classes has not been implemented. (BTW, they should be reconstructed in the implementation.)"
                                          _              -> fail "parse error"
-- Only small ints are used, if I remember correctly.
instance ShortString Int where
    showsBriefly i = LC.cons (chr (i + 128)) -- other safer options are Numeric.showHex and Numeric.showIntAtBase
    readsBriefly xs = case C.uncons xs of Nothing     -> fail "parse error"
                                          Just (c,cs) -> return (ord c - 128, cs)
instance ShortString Int16 where -- Int8 to mattaku onaji
    showsBriefly i  = LC.cons (chr (fromIntegral i + 128))
    readsBriefly xs = case C.uncons xs of Nothing     -> fail "parse error"
                                          Just (c,cs) -> return (fromIntegral (ord c - 128), cs)
instance ShortString Int8 where
    showsBriefly i  = LC.cons (chr (fromIntegral i + 128))
    readsBriefly xs = case C.uncons xs of Nothing     -> fail "parse error"
                                          Just (c,cs) -> return (fromIntegral (ord c - 128), cs)
instance ShortString Word8 where
    showsBriefly i  = LC.cons (chr (fromIntegral i))
    readsBriefly xs = case C.uncons xs of Nothing     -> fail "parse error"
                                          Just (c,cs) -> return (fromIntegral (ord c), cs)
instance (ShortString a, ShortString b, ShortString c) => ShortString (a,b,c) where
    showsBriefly (a,b,c) = showsBriefly a . showsBriefly b . showsBriefly c
    readsBriefly cs = do (a,ds) <- readsBriefly cs
                         (b,es) <- readsBriefly ds
                         (c,fs) <- readsBriefly es
                         return ((a,b,c),fs)
instance (ShortString a, ShortString b) => ShortString (a,b) where
    showsBriefly (a,b) = showsBriefly a . showsBriefly b
    readsBriefly cs = do (a,ds) <- readsBriefly cs
                         (b,es) <- readsBriefly ds
                         return ((a,b),es)
instance ShortString () where
    showsBriefly () = id
    readsBriefly cs = return ((),cs)
instance ShortString Type where
    showsBriefly (TV i)    = LC.cons 'V' . showsBriefly i
    showsBriefly (TC i)    = LC.cons 'C' . showsBriefly i
    showsBriefly (TA f x)  = LC.cons 'A' . showsBriefly f . showsBriefly x
    showsBriefly (a :-> r) = LC.cons '>' . showsBriefly a . showsBriefly r
    readsBriefly cs = case C.uncons cs of Just ('V',ds) -> do (i, es) <- readsBriefly ds
                                                              return (TV i, es)
                                          Just ('C',ds) -> do (i, es) <- readsBriefly ds
                                                              return (TC i, es)
                                          Just ('A',ds) -> do (f, es) <- readsBriefly ds
                                                              (x, fs) <- readsBriefly es
                                                              return (TA f x, fs)
                                          Just ('>',ds) -> do (a, es) <- readsBriefly ds
                                                              (r, fs) <- readsBriefly es
                                                              return (a:->r, fs)
                                          _             -> fail "parse error"
