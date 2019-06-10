-- 
-- (C) Susumu Katayama
--
-- (Typed)IOPairs上でデータをとる．ghci上で :cmd を使いまくる感じ．
{-# LANGUAGE RankNTypes, CPP, TemplateHaskell #-}
module ExperimIOP(module ExperimIOP, module MagicHaskeller.RunAnalytical) where

import MagicHaskeller.Analytical
#ifdef DEBUG
                                 hiding (rev)
#endif
import MagicHaskeller.Classification(Filtrable)
import MagicHaskeller.RunAnalytical
#ifdef DEBUG
                                 hiding (main)
#endif
import MagicHaskeller.GetTime(batchWrite)

main = do iop <- runQ andL
          let e = getOne iop []
          putStrLn $ pprint e


-- Eg.   :cmd prepare
prepare :: IO String
prepare  = run [":set +s",":m +Language.Haskell.TH","session <- prepareAPI []"]

run :: [String] -> IO String
run = return . unlines . echoOn

-- set of lightweight experiments
batchWriteFile filename = do 
                         session <- prepareAPI []
                         let f :: forall a. (Filtrable a, Typeable a) => Q [Dec] -> (a -> Bool) -> IO ()
                             f = filterGetOne_ session
                         batchWrite filename [ f addN longAddNPred 
                                             , f andL andLPred
                                             , f heaD headPred
                                             , f incr incrPred
                                             , f append appendPred
--            , f allOdd'21 (\\allodd -> allodd [3,3] && not (allodd [2,3]) && allodd [1,3,5] && not (allodd [1,2,4]))
--            , f concat12 (\\concat -> concat [\"abc\",\"\",\"de\",\"fghi\"] == \"abcdefghi\")
                                             , f drop'9 dropPred
                                             , f eq9 eqPred
                                             , f evenpos7 evenposPred
--            , f evens21 (\\evens -> evens [4,6,9,2,3,8,8] == [4,6,2,8,8])
--            , f fib6 (\\fib -> fib 1 == 1 && fib 2 == 1 && fib 4 == 3 && fib 6 == 8 && fib 8 == 21)
                                             , f iniT initPred
                                             , f oddpos6 oddposPred
                                             , f lasT lastPred
                                             , f lasts lastsPred
                                             , f lens lengthsPred
                                             , f multFst multFstPred
                                             , f multLst multLstPred
                                             , f negateall negateAllPred
                                             , f reversE revPred
                                             , f shiftl shiftlPred
                                             , f shiftr shiftrPred
                                             , f snoc snocPred
                                               --            , f suM (\\sum     -> sum   [7,3,8,5] == 23)
                                             , f swap swapPred
                                             , f switch switchPred            
                                             , f takE takePred            
                                             , f weave weavePred
                                             ]


-- :cmd batch
batch :: IO String
batch = run  $ filtGetOne "addN" "longAddNPred" ++
               filtGetOne "andL" "andLPred"
            ++ filtGetOne "heaD" "headPred"
            ++ filtGetOne "incr" "incrPred"
            ++ filtGetOne "append" "appendPred"
--            ++ filtGetOne "allOdd'21" "(\\allodd -> allodd [3,3] && not (allodd [2,3]) && allodd [1,3,5] && not (allodd [1,2,4]))"
--            ++ filtGetOne "concat12" "(\\concat -> concat [\"abc\",\"\",\"de\",\"fghi\"] == \"abcdefghi\")"
            ++ filtGetOne "drop'9" "dropPred"
            ++ filtGetOne "eq9" "eqPred"
            ++ filtGetOne "evenpos7" "evenposPred"
--            ++ filtGetOne "evens21" "(\\evens -> evens [4,6,9,2,3,8,8] == [4,6,2,8,8])"
--            ++ filtGetOneBK "fib6" "add''" "(\\fib -> fib 1 == 1 && fib 2 == 1 && fib 4 == 3 && fib 6 == 8 && fib 8 == 21)"
            ++ filtGetOne "iniT" "initPred"
            ++ filtGetOne "oddpos6" "oddposPred"
            ++ filtGetOne "lasT" "lastPred"
            ++ filtGetOne "lasts" "lastsPred"
            ++ filtGetOne "lens" "lengthsPred"
            ++ filtGetOne "multFst" "multFstPred"
            ++ filtGetOne "multLst" "multLstPred"
            ++ filtGetOne "negateall" "negateAllPred"
            ++ filtGetOne "reversE" "revPred"
            ++ filtGetOne "shiftl" "shiftlPred"
            ++ filtGetOne "shiftr" "shiftrPred"
            ++ filtGetOne "snoc" "snocPred"
--            ++ filtGetOne "suM" "(\\sum     -> sum   [7,3,8,5] == 23)"
            ++ filtGetOne "swap" "swapPred"
            ++ filtGetOne "switch" "switchPred"            
            ++ filtGetOne "takE" "takePred"            
            ++ filtGetOne "weave" "weavePred"

untype :: Functor m => m [a] -> m [a]
untype = fmap tail

-- E.g. :cmd run $ tryGetOne "add6"
tryGetOne :: String -> [String]
tryGetOne str = ["iop <- runQ $ "++str, "let e = getOne iop []", "putStrLn $ pprint e"]

-- E.g. :cmd run $ tryGetOneBK "add6" []
--      :cmd run $ tryGetOneBK "fib6" ["add6"]
tryGetOneBK :: String -> String -> [String]
tryGetOneBK str bk = ["iop <- runQ $ "++str, "bk <- runQ $ "++bk, "let e = getOne iop bk", "putStrLn $ pprint e"]
-- E.g. :cmd run $ testGetOne "add6" addArgss
testGetOne :: String -> [String] -> [String]
testGetOne str argss = tryGetOne str ++ map ("$(return e) "++) argss

-- E.g. :cmd run $ filtGetOne "reversE" "(\\f -> f \"abcdef\" == \"fedcba\")"
filtGetOne :: String -> String -> [String]
filtGetOne str predicate = ["filterGetOne session ("++str++") ("++predicate++")"]
filtGetOneBK :: String -> String -> String -> [String]
filtGetOneBK str bk predicate = ["filterGetOneBK session ("++str++") ("++bk++") ("++predicate++")"]

emptyBK = [d| {} |]

-- :cmd run $ filtGetOne "add''" "(\\(+) -> 3+5==8)"
add6  = [d| f :: Int->Int->Int; f 0 0 = 0; f 0 1 = 1; f 1 0 = 1; f 2 0 = 2; f 1 1 = 2; f 0 2 = 2 |]
add'7 = [d| f :: Int->Int->Int; f 0 x = x; f x 0 = x; f 1 1 = 2; f 1 2 = 3; f 2 1 = 3; f 2 2 = 4; f 2 3 = 5 |] -- dame. でも，IgorではOK.
add'6 = [d| f :: Int->Int->Int; f 0 x = x; f x 0 = x; f 1 1 = 2; f 1 2 = 3; f 2 1 = 3; f 2 2 = 4 |] -- dame
add'5 = [d| f :: Int->Int->Int; f 0 x = x; f x 0 = x; f 1 1 = 2; f 1 2 = 3; f 2 1 = 3 |] -- dame
add'3 = [d| f :: Int->Int->Int; f 0 x = x; f x 0 = x; f 1 1 = 2 |] -- dame
add'2 = [d| f :: Int->Int->Int; f 0 x = x; f x 0 = x |] -- dame どうもoverlapしているのがまずいのでは? 自動的にcase分けするようにすればよい．
add'1 = [d| f :: Int->Int->Int; f 0 x = x |]
add'' = [d| f :: Int->Int->Int; f 0 x = x; f 1 0 = 1; f 2 0 = 2; f 1 1 = 2; f 1 2 = 3; f 2 1 = 3; f 2 2 = 4; f 2 3 = 5 |]
add'''= [d| f :: Int->Int->Int; f 0 0 = 0; f 0 1 = 1; f 0 2 = 2; f 1 0 = 1; f 2 0 = 2; f 1 1 = 2; f 1 2 = 3; f 2 1 = 3; f 2 2 = 4; f 2 3 = 5 |]
addArgss = ["3 5"]

-- :cmd run $ filtGetOne "addN" "longAddNPred"
addN = [d|
        addN :: Int -> [Int] -> [Int]
        addN 0 [] = []
        addN 1 [] = []
        addN 2 [] = []
        addN 0 [0] = [0]
        addN 0 [1] = [1]
        addN 0 [2] = [2]
        addN 0 [0,1] = [0,1]
        addN 0 [1,0] = [1,0]
        addN 1 [0,1] = [1,2]
        addN 1 [1,0] = [2,1]
        addN 1 [0] = [1]
        addN 1 [1] = [2]
        addN 1 [2] = [3]
        addN 2 [0] = [2]
        addN 2 [1] = [3]
        addN 2 [2] = [4]
        addN 2 [0,1] = [2,3]
        addN 2 [2,0] = [4,2]
       |]
--batchAddN = do session <- prepareAPI ["MagicHaskeller"]
--               batchWrite "addN.dat" $ map (\n -> filterGetOne session (tunedAddN n) addNPred) [5..22] -- こう書いては見たものの，タイムアウトは？
testAddN = [d|
        addN :: Int -> [Int] -> [Int]
        addN 0 [] = []
        addN 1 [] = []
        addN 2 [] = []
       |]

takeFunD n (FunD name clauses : xs) = FunD name (take n clauses) : takeFunD n xs
takeFunD n (x:xs) = x : takeFunD n xs
takeFunD _ [] = []

-- 22まで．実際には，[3,6..21]で実行するだけで面白い感じ．(3と21以外はうまくいく．)
tunedAddN n = fmap (takeFunD n) [d|
        addN :: Int -> [Int] -> [Int]
        addN 0 [] = []
        addN 1 [] = []
        addN 2 [] = []
        addN 0 [0] = [0]
        addN 0 [1] = [1]
        addN 0 [2] = [2]
        addN 0 [0,0] = [0,0]
        addN 0 [0,1] = [0,1]
        addN 0 [1,0] = [1,0]
        addN 1 [0] = [1]
        addN 1 [1] = [2]
        addN 1 [2] = [3]
        addN 1 [0,0] = [1,1]
        addN 1 [0,1] = [1,2]
        addN 1 [1,0] = [2,1]
        addN 2 [0] = [2]
        addN 2 [1] = [3]
        addN 2 [2] = [4]
        addN 2 [0,0] = [2,2]
        addN 2 [0,1] = [2,3]
        addN 2 [1,0] = [3,2]
        addN 2 [2,0] = [4,2]
       |]
addNPred, longAddNPred :: (Int -> [Int] -> [Int]) -> Bool
addNPred addN = addN 3 [5,7] == [8,10]
longAddNPred addN = addN 3 [5,7,2] == [8,10,5]
-- :cmd run $ filtGetOne "andL" "(\\and -> not (and [True,False]) && and [True,True] && and [True,True,True] && not (and [False,True,True]))"
andL = tunedAndL 15
-- [1,3,7,15,31]
tunedAndL n = fmap (takeFunD n) [d|
        andL :: [Bool] -> Bool
        andL [] = True
        andL [True] = True
        andL [False] = False
        andL [True,True] = True
        andL [True,False] = False
        andL [False,True] = False
        andL [False,False] = False
        andL [True,True,True] = True
        andL [False,True,True] = False
        andL [True,False,True] = False
        andL [True,True,False] = False
        andL [True,False,False] = False
        andL [False,True,False] = False
        andL [False,False,True] = False
        andL [False,False,False] = False
        andL [True,True,True,True] = True
        andL [True,False,True,True] = False
        andL [True,True,False,True] = False
        andL [True,True,True,False] = False
        andL [True,True,False,False] = False
        andL [True,False,True,False] = False
        andL [True,False,False,True] = False
        andL [True,False,False,False] = False
        andL [False,True,True,True] = True
        andL [False,False,True,True] = False
        andL [False,True,False,True] = False
        andL [False,True,True,False] = False
        andL [False,True,False,False] = False
        andL [False,False,True,False] = False
        andL [False,False,False,True] = False
        andL [False,False,False,False] = False
       |]

andLPred and = not (and [True,False]) && and [True,True] && and [True,True,True] && not (and [False,True,True])

allOdd4 = [d| f :: [Int]->Bool; f [] = True; f [x] = odd x; f [x,y] = odd x && odd y; f [x,y,z] = odd x && (odd y && odd z) |]

--  :cmd run $ filtGetOne "allOdd'21" "longAlloddPred"
allOdd'21 = [d| f :: [Int]->Bool; f [] = True; f [0] = False;   f [1] = True;    f [2] = False;   f [3] = True;
                                                                 f [0,0] = False; f [0,1] = False; f [0,2] = False; f [0,3] = False;
                                                                 f [1,0] = False; f [1,1] = True;  f [1,2] = False; f [1,3] = True;
                                                                 f [2,0] = False; f [2,1] = False; f [2,2] = False; f [2,3] = False;
                                                                 f [3,0] = False; f [3,1] = True;  f [3,2] = False; f [3,3] = True |]
-- [1,3,6,10,15] あと，allOdd'21はこれらを包含する．
tunedAllOdd n = fmap (takeFunD n)
             [d| f :: [Int]->Bool; f []  = True; f [0] = False; f [0,0] = False;
                                                 f [1] = True;  f [0,1] = False; f [1,0] = False;
                                                 f [2] = False; f [0,2] = False; f [1,1] = True;  f [2,0] = False;
                                                 f [3] = True;  f [0,3] = False; f [1,2] = False; f [2,1] = False; f [3,0] = False |] -- dame

-- Igorでもcatamorphism extensionなしではできないのでいいや．
alloddPred allodd = allodd [3,3] && not (allodd [2,3]) && allodd [1,3,5] && not (allodd [1,2,4])
longAlloddPred allodd = allodd [3,3] && not (allodd [2,3]) && allodd [1,3,5] && not (allodd [3,7,5,1,2])

-- Example.hsそのまま
--  :cmd run $ filtGetOne "append" "appendPred"
append = [d|
          appenD  :: [a] -> [a] -> [a]
          appenD [] x = x
          --appenD [][]        = []
          appenD [a][]       = [a]
--appenD [][c]       = [c]
--appenD [][c,d]     = [c,d]
          appenD [a][c]      = [a,c]
          appenD [a,b][]     = [a,b]
--appenD [] [a,b,c]  = [a,b,c]
          appenD [a][c,d]    = [a,c,d]
          appenD [a,b][d]    = [a,b,d]
          appenD [a,c,d][]   = [a,c,d]
--appenD [][a,b,c,d] = [a,b,c,d]
          appenD [a,b][c,d]  = [a,b,c,d]
          appenD [a,b,c][d]  = [a,b,c,d]
          appenD [a,b,c,d][] = [a,b,c,d]
         |] -- いける
-- [2,4,7,11,16]
tunedAppend n = fmap (takeFunD n) [d|
          appenD  :: [a] -> [a] -> [a]
          appenD [] x = x
          --appenD [][]        = []
          appenD [a][]       = [a]
--appenD [][c]       = [c]
--appenD [][c,d]     = [c,d]
          appenD [a][c]      = [a,c]
          appenD [a,b][]     = [a,b]
--appenD [] [a,b,c]  = [a,b,c]
          appenD [a][c,d]    = [a,c,d]
          appenD [a,b][d]    = [a,b,d]
          appenD [a,c,d][]   = [a,c,d]
          appenD [a][b,c,d]  = [a,b,c,d]
          appenD [a,b][c,d]  = [a,b,c,d]
          appenD [a,b,c][d]  = [a,b,c,d]
          appenD [a,b,c,d][] = [a,b,c,d]
          appenD [a][b,c,d,e]  = [a,b,c,d,e]
          appenD [a,b][c,d,e]  = [a,b,c,d,e]
          appenD [a,b,c][d,e]  = [a,b,c,d,e]
          appenD [a,b,c,d][e]  = [a,b,c,d,e]
          appenD [a,b,c,d,e][] = [a,b,c,d,e]
         |] -- いける
{-
take 2: 0
take 4: 0
take 7: 0
take 11:0.39
take 16: >300
-}
appendPred (++) = "foo" ++ "bar" == "foobar"
--  :cmd run $ filtGetOne "concat12" "(\\concat -> concat [\"abc\",\"\",\"de\",\"fghi\"] == \"abcdefghi\")"
concat12 = [d|
            concaT :: [[a]] -> [a]
            concaT [] = []
            concaT [[]] = []
            concaT [[a]] = [a]
            concaT [[],[a]] = [a]
            concaT [[a],[]] = [a]
            concaT [[a],[b]] = [a,b]
            concaT [[c,d]]= [c,d]
            concaT [[a,b,c]] = [a,b,c]
            concaT [[a,b],[c]] = [a,b,c]
            concaT [[a],[c,d]] = [a,c,d]
            concaT [[a],[b],[c]] = [a,b,c]
            concaT [[a,b],[c,d]] = [a,b,c,d]
            |] -- dame. igorでもダメ．MHだと一瞬．
-- てゆーか，要素数3つの場合に空リストがなかったりする訳で，その辺系統的な例とはいえないので，何とも言えない．
tunedConcat n = fmap (takeFunD n) [d|
            concaT :: [[a]] -> [a]
            concaT [] = []
            concaT [[]] = []
            concaT [[a]] = [a]
            concaT [[],[]] = []
            concaT [[],[a]] = [a]
            concaT [[a],[]] = [a]
            concaT [[a],[b]] = [a,b]
            concaT [[c,d]]= [c,d]
            concaT [[a,b,c]] = [a,b,c]
            concaT [[],[a,b,c]] = [a,b,c]
            concaT [[a,b,c],[]] = [a,b,c]
            concaT [[a,b],[c]] = [a,b,c]
            concaT [[a],[c,d]] = [a,c,d]
--            concaT [[a,b],[c,d]] = [a,b,c,d]
--            concaT [[a],[b],[c]] = [a,b,c]
            |]

concatPred concat = concat ["abc","","de","fghi"] == "abcdefghi"

allOddArgss = ["[3,1,5]", "[1,3,2]"]

-- こっちがtuned
tunedDrop12 = [d| 
             droP :: Int -> [a] -> [a]
             droP 0 []      = []
             droP 0 [a]     = [a]
             droP 0 [a,b]   = [a,b]
             droP 0 [a,b,c] = [a,b,c]
             droP 1 []      = []
             droP 1 [a]     = []
             droP 1 [a,b]   = [b]
             droP 1 [a,b,c] = [b,c]
             droP 2 []      = []
             droP 2 [a]     = []
             droP 2 [a,b]   = []
             droP 2 [a,b,c] = [c]
          |] -- 0.20sec
tunedDrop9 = [d|
             droP :: Int -> [a] -> [a]
             droP 0 []      = []
             droP 0 [a]     = [a]
             droP 0 [a,b]   = [a,b]
             droP 1 []      = []
             droP 1 [a]     = []
             droP 1 [a,b]   = [b]
             droP 2 []      = []
             droP 2 [a]     = []
             droP 2 [a,b]   = []
          |] -- 0.08sec
tunedDrop6 = [d|
             droP :: Int -> [a] -> [a]
             droP 0 []      = []
             droP 0 [a]     = [a]
             droP 0 [a,b]   = [a,b]
             droP 1 []      = []
             droP 1 [a]     = []
             droP 1 [a,b]   = [b]
          |] -- 0.07sec
tunedDrop4 = [d|
             droP :: Int -> [a] -> [a]
             droP 0 []      = []
             droP 0 [a]     = [a]
             droP 1 []      = []
             droP 1 [a]     = []
          |] -- 0.10 sec
-- :cmd run $ filtGetOne "drop'9" "dropPred"
drop'9 = [d| droP :: Int -> [a] -> [a]
             droP 0 x = x
             --droP 0             []      = []
             --droP 0             [a]     = [a]

             --droP x [] = []
             droP 1 []      = []
             droP 2 []      = []

             --droP 0             [a,b]   = [a,b]
             --droP 0             [a,b,c] = [a,b,c]
             droP 1         [a]     = []
             droP 1         [a,b]   = [b]
             droP 1         [a,b,c] = [b,c]
             droP 2     [a]     = []
             droP 2     [a,b]   = []
             droP 2     [a,b,c] = [c]
          --droP (S (S 1)) []      = []
          --droP (S (S 1)) [a]     = []
          --droP (S (S 1)) [a,b]   = []
          --droP (S (S 1)) [a,b,c] = []
          |] -- いける．ちなみに，drop12の場合とはべつの解が先頭に来るが，どちらも正解．なお，drop'9がExample.hsと同じもの．
dropPred :: (Int -> String -> String) -> Bool
dropPred drop = drop 3 "abcde" == "de"

dropArgss = ["3 [4,5,6,7,8]"]

even6 = [d| f :: Int -> Bool; f 0 = True; f 1 = False; f 2 = True; f 3 = False; f 4 = True; f 5 = False |]
evenArgss = ["8", "9"]

tunedEvenpos n = fmap (takeFunD n) evenpos7
{-
take 2 : >300 sec
take 3 : 0.03 sec
take 4 : 0.02 sec
take 5 : 0.01 sec
take 6 : 0.01 sec
take 7 : 0.04 sec
-}
--  :cmd run $ filtGetOne "evenpos7" "evenposPred"
evenpos7 = [d| evenpos :: [a] -> [a]
               evenpos [] = []
               evenpos [a] = []
               evenpos [a,b] = [b]
               evenpos [a,b,c] = [b]
               evenpos [a,b,c,d] = [b,d]
               evenpos [a,b,c,d,e] = [b,d]
               evenpos [a,b,c,d,e,f] = [b,d,f]
            |] -- Examples.hsと同じもの．
evenposPred evenpos = evenpos "abcdefg" == "bdf"
-- :cmd run $ filtGetOne "evens21" "evensPred"
evens21 = [d|
            evens :: [Int] -> [Int]
            evens []  = []
            evens [0] = [0]
            evens [1] = []
            evens [2] = [2]
            evens [3] = []
            evens [0,0] = [0,0]
            evens [0,1] = [0]
            evens [0,2] = [0,2]
            evens [0,3] = [0]
            evens [1, 0] = [0]
            evens [1, 1] = []
            evens [1, 2] = [2]
            evens [1, 3] = []
            evens [2, 0] = [2,0]
            evens [2, 1] = [2]
            evens [2, 2] = [2,2]
            evens [2, 3] = [2]
            evens [3, 0] = [0]
            evens [3, 1] = []
            evens [3, 2] = [2]
            evens [3, 3] = []
         |] -- >300
evens13 = [d|
            evens :: [Int] -> [Int]
            evens []  = []
            evens [0] = [0]
            evens [1] = []
            evens [2] = [2]
            evens [0,0] = [0,0]
            evens [0,1] = [0]
            evens [0,2] = [0,2]
            evens [1, 0] = [0]
            evens [1, 1] = []
            evens [1, 2] = [2]
            evens [2, 0] = [2,0]
            evens [2, 1] = [2]
            evens [2, 2] = [2,2]
         |] -- >300
evens10 = [d|
            evens :: [Int] -> [Int]
            evens []  = []
            evens [0] = [0]
            evens [1] = []
            evens [2] = [2]
            evens [0,0] = [0,0]
            evens [0,1] = [0]
            evens [0,2] = [0,2]
            evens [1, 0] = [0]
            evens [1, 1] = []
            evens [1, 2] = [2]
          |] -- >300
evens7 = [d|
            evens :: [Int] -> [Int]
            evens []  = []
            evens [0] = [0]
            evens [1] = []
            evens [0,0] = [0,0]
            evens [0,1] = [0]
            evens [1, 0] = [0]
            evens [1, 1] = []
          |] -- >300
evensArgss = ["[1,2,3,4,5]"]
evensPred evens = evens [4,6,9,2,3,8,8] == [4,6,2,8,8]

--  :cmd run $ filtGetOne "eq9" "eqPred"
eq9 = [d| f :: Int->Int->Bool; f 0 0 = True; f 0 1 = False; f 0 2 = False; f 1 0 = False; f 1 1 = True; f 1 2 = False; f 2 0 = False; f 2 1 = False; f 2 2 = True |] -- Examples.hsと同じもの 0.04sec

eq6 = fmap (takeFunD 6) eq9 -- 0.07 sec
eq4 = [d| f :: Int->Int->Bool; f 0 0 = True; f 0 1 = False; f 1 0 = False; f 1 1 = True |] -- 0.08 sec
eq3 = fmap (takeFunD 3) eq4

eq16 = [d| f :: Int->Int->Bool; f 0 0 = True; f 0 1 = False; f 0 2 = False; f 0 3 = False; f 1 0 = False; f 1 1 = True; f 1 2 = False; f 1 3 = False; f 2 0 = False; f 2 1 = False; f 2 2 = True; f 2 3 = False; f 3 0 = False; f 3 1 = False; f 3 2 = False; f 3 3 = True |] -- >300
eqArgss = ["4 4", "5 7"]
eqPred :: (Int->Int->Bool) -> Bool
eqPred (==) = 3==3 && not (4==6) && 0==0 && not (2==0) && not (0==2) && not (3==5)

tryFib :: [String]
tryFib = ["iop <- runQ $ fib6", "let e = getOne iop []", "putStrLn $ pprint e"]
-- note that this starts with 0 rather than 1. Also, more examples should be given.
-- :cmd run $ filtGetOne "fib6" "(\\fib -> fib 1 == 1 && fib 2 == 1 && fib 4 == 3 && fib 6 == 8 && fib 8 == 21)"
fib6 = [d| fib :: Int->Int
           fib 0 = 0
           fib 1 = 1
           fib 2 = 1
           fib 3 = 2
           fib 4 = 3
           fib 5 = 5
        |] -- Examples.hsとおなじもの
-- :cmd run $ filtGetOne "fib8" "(\\fib -> fib 1 == 1 && fib 2 == 1 && fib 4 == 3 && fib 6 == 8 && fib 8 == 21)"
fib8 = [d| fib :: Int->Int
           fib 0 = 0
           fib 1 = 1
           fib 2 = 1
           fib 3 = 2
           fib 4 = 3
           fib 5 = 5
           fib 6 = 8
           fib 7 = 13
        |]
fib9 = [d| fib :: Int->Int
           fib 0 = 0
           fib 1 = 1
           fib 2 = 1
           fib 3 = 2
           fib 4 = 3
           fib 5 = 5
           fib 6 = 8
           fib 7 = 13
           fib 8 = 21
        |]
fib10 = [d| fib :: Int->Int
            fib 0 = 0
            fib 1 = 1
            fib 2 = 1
            fib 3 = 2
            fib 4 = 3
            fib 5 = 5
            fib 6 = 8
            fib 7 = 13
            fib 8 = 21
            fib 9 = 34
        |]

tunedFib n = fmap (takeFunD n) fib10
-- add'''を使う場合，実際にはfib6が限界

fibPred fib = fib 1 == 1 && fib 2 == 1 && fib 4 == 3 && fib 6 == 8 && fib 8 == 21
-- :cmd run $ filtGetOne "heaD" "headPred"
heaD = [d|
        heaD :: [a] -> a
        heaD [a] = a
        heaD [a,b] = a
        heaD [a,b,c] = a
        heaD [a,b,c,d] = a
       |]
tunedHead n = fmap (takeFunD n) heaD -- 1から4全て0.01 sec
headPred head   = head "abcde" == 'a'
-- :cmd run $ filtGetOne "incr" "incrPred"
incr = [d|
        incr :: [Int] -> [Int]
        incr []       = []
        incr [0]      = [1]
        incr [1]      = [2]
--incr [2]   = [3]
        incr [0,1]    = [1,2]
--incr [0,2] = [1,3]
        incr [1,0]    = [2,1]
       |] -- Examples.hsと同じもの．長さが足りず，filterが有効な例．`mplus`でも(+/)でも．でも，Igorだとうまくいく．

incrPred :: ([Int] -> [Int]) -> Bool
incrPred f = f [0,1,1,2] == [1,2,2,3]
incr' = [d|
        incr :: [Int] -> [Int]
        incr []       = []
        incr [0]      = [1]
        incr [1]      = [2]
--incr [2]   = [3]
        incr [0,1]    = [1,2]
--incr [0,2] = [1,3]
        incr [1,0]    = [2,1]
--        incr [0,0,0]  = [1,1,1]
        incr [1,0,0]  = [2,1,1]
        incr [0,1,0]  = [1,2,1]
        incr [0,0,1]  = [1,1,2]
        incr [1,0,0,0]  = [2,1,1,1]
        incr [0,1,0,0]  = [1,2,1,1]
        incr [0,0,1,0]  = [1,1,2,1]
        incr [0,0,0,1]  = [1,1,1,2]
       |] -- こうやってもダメ．
-- :cmd run $ filtGetOne "iniT" "initPred"
iniT = [d|
        iniT:: [a] -> [a]
        iniT [a] = []
        iniT [a,b] = [a]
        iniT [a,b,c] = [a,b]
        iniT [a,b,c,d] = [a,b,c]
       |] -- おなじやつ
tunedInit n = fmap (takeFunD n) iniT
{-
take 4: 0.01 sec
take 3: 0.01 sec
take 2: 0.02 sec
take 1: >300
-}
initPred init = init "foobar" == "fooba"

-- taken from Examples.hs in igor2-0.7.1.3, but equivalence over Ints has to be defined in order to work with igor2, because equivalence over Ints are not defined.
-- These (with eq9 as the BK) should not work when anti-unification is forced. なぜなら，succが導入されてintroBKが阻害されるから．1からでなく0から始めるべき．
mem15 = [d|
         mem :: Int -> [Int] -> Bool
         mem 1 [] = False
         mem 2 [] = False
         mem 3 [] = False
         mem 1 [1] = True
         mem 2 [1] = False
         mem 3 [1] = False
         mem 1 [2] = False
         mem 2 [2] = True
         mem 3 [2] = False
         mem 1 [3] = False
         mem 2 [3] = False
         mem 3 [3] = True

         mem 1 [2,1] = True
         mem 2 [2,1] = True
         --member 1 [3,1,2] = [1,2]
         --member 1 [1,2,3] = [1,2,3]
         mem 1 [3,2,1] = True
         |]
mem8 = [d|
         mem :: Int -> [Int] -> Bool
         mem 1 [] = False
         mem 2 [] = False
         mem 1 [1] = True
         mem 2 [1] = False
         mem 1 [2] = False
         mem 2 [2] = True
         mem 1 [2,1] = True
         mem 2 [2,1] = True
         |]
mem6 = [d|
         mem :: Int -> [Int] -> Bool
         mem 1 [] = False
         mem 2 [] = False
         mem 1 [1] = True
         mem 2 [1] = False
         mem 1 [2] = False
         mem 2 [2] = True
         |]
mem'15 = [d|
         mem :: Int -> [Int] -> Bool
         mem 0 [] = False
         mem 1 [] = False
         mem 2 [] = False
         mem 0 [0] = True
         mem 1 [0] = False
         mem 2 [0] = False
         mem 0 [1] = False
         mem 1 [1] = True
         mem 2 [1] = False
         mem 0 [2] = False
         mem 1 [2] = False
         mem 2 [2] = True

         mem 0 [1,0] = True
         mem 1 [1,0] = True
         --member 0 [2,0,1] = [0,1]
         --member 0 [0,1,2] = [0,1,2]
         mem 0 [2,1,0] = True
         |]

mem'6 = [d|
         mem :: Int -> [Int] -> Bool
         mem 0 [] = False
         mem 1 [] = False
         mem 0 [0] = True
         mem 1 [0] = False
         mem 0 [1] = False
         mem 1 [1] = True
         |]

mem'8 = [d|
         mem :: Int -> [Int] -> Bool
         mem 0 [] = False
         mem 1 [] = False
         mem 0 [0] = True
         mem 1 [0] = False
         mem 0 [1] = False
         mem 1 [1] = True
         mem 0 [0,1] = True
         mem 1 [0,1] = True
         |]

-- rev n = fmap (take (n+1)) [d| f :: [a]->[a];      f [] = []; f [a] = [a]; f [a,b] = [b,a]; f [a,b,c] = [c,b,a]; f [a,b,c,d] = [d,c,b,a] |]
-- :cmd run $ filtGetOne "oddpos6" "oddposPred"
oddpos6 = [d|
           oddpos :: [a] -> [a]
           oddpos [] = []
           oddpos [a] = [a]
           oddpos [a,b] = [a]
           oddpos [a,b,c] = [a,c]
           oddpos [a,b,c,d] = [a,c]
           oddpos [a,b,c,d,e] = [a,c,e]
          |]
oddposPred oddpos = oddpos "abcdef" == "ace" && oddpos "abc" == "ac"
{-
take 6: 0 sec
take 5: 0 sec
take 4: 0 sec
take 3: 0 sec
take 2: >300
take 1: 
-}
tunedOddpos n = fmap (takeFunD n) oddpos6 -- 1から4全て0.01 sec

-- :cmd run $ filtGetOne "lasT" "lastPred"
lasT = [d|
        lasT :: [a] -> a
        lasT [a] = a
        lasT [a,b] = b
        lasT [a,b,c] = c
        lasT [a,b,c,d] = d
       |]
{-
take 4: 0.04 sec
take 3: 0.01 sec
take 2: 0.01 sec
take 1: >300
-}
tunedLast  n = fmap (takeFunD n) lasT
lastPred last = last "abcde"  == 'e'

lastM = [d|
         lastM :: [a] -> Maybe a
         lastM [] = Nothing
         lastM [a] = Just a
         lastM [a,b] = Just b
         lastM [a,b,c] = Just c
         lastM [a,b,c,d] = Just d
        |] -- Maybeやってなかった．
-- :cmd run $ filtGetOne "lasts" "lastsPred"
lasts = [d|
        lasts :: [[a]] -> [a]
        lasts [] = []
        lasts [[a]] = [a]
        lasts [[a,b]] = [b]
        lasts [[a,b,c]] = [c]
        lasts [[b],[a]] = [b,a]
        lasts [[c],[a,b]] = [c,b]
        lasts [[a,b],[c,d]] = [b,d]
        lasts [[c,d],[b]] = [d,b]
        lasts [[c],[d,e],[f]] = [c,e,f]
        lasts [[c,d],[e,f],[g]] = [d,f,g]
        |]
-- not actually tuned
tunedLasts n = fmap (takeFunD n) lasts
{- 
take 1: >300
take 4: 0.06
take 8: 0.10
take 10: 1.2 sec -- 論文だと四捨五入で0秒だけど，あの時はbatchWriteFileでやったのでオーバヘッドがなかった．
-}
lasts' = [d|
        lasts :: [[a]] -> [a]
        lasts [] = []
        lasts [[a]] = [a]
        lasts [[a,b]] = [b]
--        lasts [[a,b,c]] = [c]
        lasts [[b],[a]] = [b,a]
        lasts [[c],[a,b]] = [c,b]
        lasts [[a,b],[c,d]] = [b,d]
        lasts [[c,d],[b]] = [d,b]
--        lasts [[c],[e],[f]] = [c,e,f]
  --      lasts [[c],[d,e],[f]] = [c,e,f]
    --    lasts [[c,d],[e,f],[g]] = [d,f,g]
      --  lasts [[c,d],[e,f],[h,g]] = [d,f,g]
        |]
lastsPred lasts = lasts  ["abcdef", "abc", "abcde"] == "fce"

-- :cmd run $ filtGetOne "lens" "lengthsPred"
lens = [d|
   lengths :: [[a]] -> [Int]
   lengths []   = []
   lengths [[]] = [0]
   lengths [[a]] = [1]
   lengths [[b,a]] = [2]
--lengths [[c,b,a]] = [S(S(1)]
   lengths [[],[]] = [0, 0]
   lengths [[],[a]] = [0,1]
   lengths [[],[b,a]] = [0,2]
 |]
tunedLens n = fmap (takeFunD n) [d|
   lengths :: [[a]] -> [Int]
   lengths []   = []
   lengths [[]] = [0]
   lengths [[a]] = [1]
   lengths [[b,a]] = [2]
   lengths [[],[]] = [0, 0]
   lengths [[],[a]] = [0,1]
   lengths [[],[b,a]] = [0,2]
   lengths [[x],[]] = [1, 0]
   lengths [[x],[a]] = [1,1]
   lengths [[x],[b,a]] = [1,2]
   lengths [[x,y],[]] = [2, 0]
   lengths [[x,y],[a]] = [2,1]
   lengths [[x,y],[b,a]] = [2,2]
   lengths [[],[],[]] = [0,0,0]
 |]
lengthsPred :: ([String] -> [Int]) -> Bool
lengthsPred lengths = lengths ["abcdef", "abc", "abcde"] == [6,3,5]
{-
take 4:  0.02
take 7:  0.03
take 10: 0.15 secs
take 13: 6.60 secs
take 14: 17.15 secs
-}
-- しかし，IgorIIHでこれを全部タイムアウトまでやると考えると気が遠くなる．たとえば，上記のlengthsの例では，提案手法ですべてうまくいっているのだから，1つの例でIgorIIHに生成できなければ提案手法が優っているのは明白なのでやめてしまっていいのではなかろうか？

--  :cmd run $ filtGetOne "multFst" "multFstPred"
multFst = [d|
  multfst :: [a] -> [a]
  multfst [] = []
  multfst [a] = [a]
  multfst [a,b] = [a,a]
  multfst [a,b,c] = [a,a,a]
  multfst [a,b,c,d] = [a,a,a,a]
--multfst [a,b,c,d,e] = [a,a,a,a,a]
--multfst [a,b,c,d,e,f] = [a,a,a,a,a,a]
 |]
{-
take 2: >300
take 3: 0
take 4: 0
take 5: 0
-}
multFstPred multfst = multfst "abcdef" == "aaaaaa"
tunedMultFst n = fmap (takeFunD n) multFst

--  :cmd run $ filtGetOne "multLst" "multLstPred"
multLst = [d|
  multlst :: [a] -> [a]
  multlst [] = []
  multlst [a] = [a]
  multlst [a,b] = [b,b]
  multlst [a,b,c] = [c,c,c]
  multlst [a,b,c,d] = [d,d,d,d]
--multlst [a,b,c,d,e] = [e,e,e,e,e]
--multlst [a,b,c,d,e,f] = [f,f,f,f,f,f]
 |]
multLstPred multlst = multlst "abcdef" == "ffffff"
tunedMultLst n = fmap (takeFunD n) multLst

--  :cmd run $ filtGetOne "negateall" "negateAllPred"
negateall = [d|
  negateAll :: [Bool] -> [Bool]
  negateAll []            = []
  negateAll [True]        = [False]
  negateAll [False]       = [True]
  negateAll [False,False] = [True,True]
  negateAll [False,True]  = [True,False]
  negateAll [True,False]  = [False,True]
  negateAll [True,True]   = [False,False]
 |]
negateAllPred f = f [True,False,False,True] == [False,True,True,False] && f [False,True,False] == [True,False,True]

--  :cmd run $ filtGetOne "powset" "(\\powset -> powset \"abcd\" == [\"abcd\",\"abc\",\"abd\",\"ab\",\"acd\",\"ac\",\"ad\",\"a\",\"bcd\",\"bc\",\"bd\",\"b\",\"cd\",\"c\",\"d\",\"\"])"
powset = [d|
        powset :: [a] -> [[a]]
        powset [] = [[]]
        powset [a] = [[a],[]]
        powset [a,b] = [[a,b],[a],[b],[]]
        powset [a,b,c] = [[a,b,c],[a,b],[a,c],[a],[b,c],[b],[c],[]]
        --powset [a,b,c,d] = [[a,b,c,d],[a,b,c],[a,b,d],[a,b],[a,c,d],[a,c],[a,d],[a],[b,c,d],[b,c],[b,d],[b],[c,d],[c],[d],[]]  
      |]

odD = [d|
  odD :: Int -> Bool
  odD 0                     = False
  odD 1                 = True
  odD 2             = False
  odD 3         = True
  odD 4     = False
  odD 5 = True
 |]
-- :cmd run $ filtGetOne "reversE" "(\\rev -> rev \"abcde\" == \"edcba\")"
reversE = [d|
  reversE :: [a] -> [a]
  reversE [] = []
  reversE [a] =[a]
  reversE [a,b] = [b,a]
  reversE [a,b,c] = [c,b,a]
  reversE [a,b,c,d] = [d,c,b,a]
--reversE [a,b,c,d,e] = [e,d,c,b,a]
--reversE [a,b,c,d,e,f] = [f,e,d,c,b,a]
 |]
revPred rev = rev "abcdef" == "fedcba"
--  :cmd run $ filtGetOne "shiftl" "shiftlPred"
shiftl = [d|
  shiftl :: [a] -> [a]
  shiftl [] = []
  shiftl [a] = [a]
  shiftl [a,b] = [b,a]
  shiftl [a,b,c] = [b,c,a]
  shiftl [a,b,c,d] = [b,c,d,a]
--shiftl [a,b,c,d,e] = [b,c,d,e,a]
--shiftl [a,b,c,d,e,f] = [b,c,d,e,f,a]
--shiftl [a,b,c,d,e,f,g] = [b,c,d,e,f,g,a]
--shiftl [a,b,c,d,e,f,g,h] = [b,c,d,e,f,g,h,a]
 |]
shiftlPred shiftl = shiftl "abcde" == "bcdea"

--  :cmd run $ filtGetOne "shiftr" "shiftrPred"
shiftr = [d|
  shiftr :: [a] -> [a]
  shiftr [] = []
  shiftr [a] = [a]
  shiftr [a,b] = [b,a]
  shiftr [a,b,c] = [c,a,b]
  shiftr [a,b,c,d] = [d,a,b,c]
-- shiftr [a,b,c,d,e] = [e,a,b,c,d]
 |]
shiftrPred shiftr = shiftr "abcde" == "eabcd"

--  :cmd run $ filtGetOne "snoc" "snocPred"
snoc = [d|
  snoc :: a -> [a] -> [a]
  snoc a []            = [a]
  snoc b [a]           = [a,b]
  snoc c [a,b]         = [a,b,c]
  snoc d [a,b,c]       = [a,b,c,d]
--snoc e [a,b,c,d]   = [a,b,c,d,e]
--snoc f [a,b,c,d,e] = [a,b,c,d,e,f]
 |]
snocPred snoc = snoc 'f' "abcde" == "abcdef"

--  :cmd run $ filtGetOne "suM" "(\\sum     -> sum   [7,3,8,5] == 23)"
suM = [d|
  suM :: [Int] -> Int
  suM [] = 0
  suM [0] = 0
  suM [1] = 1
  suM [2] = 2
  suM [0,0] = 0
  suM [0,1] = 1
  suM [0,2] = 2
  suM [1,0] = 1
  suM [1,1] = 2
  suM [1,2] = 3
  suM [2,0] = 2
  suM [2,1] = 3
  suM [2,2] = 4
  suM [2,1, 2] = 5  -- without this line this is easily synthesizable.
 |]

sumL = [d| sum [] = 0; sum [x] = x; sum [x,y] = x+y; sum [x,y,z] = x+y+z; sum [x,y,z,w] = x+y+z+w |]
sumR = [d| sum [] = 0; sum [x] = x; sum [x,y] = x+y; sum [x,y,z] = x+(y+z); sum [x,y,z,w] = x+(y+(z+w)) |]

tunedSum n = fmap (takeFunD n) suM
sumPred sum = sum [7,3,8,5] == 23

--  :cmd run $ filtGetOne "swap" "swapPred"
swap = [d|
  swap:: [a] -> [a]
  swap [] = []
  swap [a] = [a]
  swap [a,b] = [b,a]
  swap [a,b,c] = [b,a,c]
  swap [a,b,c,d] = [b,a,d,c]
  swap [a,b,c,d,e] = [b,a,d,c,e]
  swap [a,b,c,d,e,f] = [b,a,d,c,f,e]
 |]
swapPred swap = swap "abcde" == "badce"

--  :cmd run $ filtGetOne "switch" "switchPred"
switch = [d|
  switch :: [a] -> [a]
  switch [] = []
  switch [a] = [a]
  switch [a,b] = [b,a]
  switch [a,b,c] = [c,b,a]
  switch [a,b,c,d] = [d,b,c,a]
--switch [a,b,c,d,e] = [e,b,c,d,a]
--switch [a,b,c,d,e,f] = [f,b,c,d,e,a]
 |]
switchPred switch = switch "abcde" == "ebcda"

--  :cmd run $ filtGetOne "takE" "takePred"
takE = [d|
  takE :: Int -> [a] -> [a]
  takE 0             []      = []
  takE 0             [a]     = []
  takE 0             [a,b]   = []
--takE 0             [a,b,c] = []
  takE 1         []      = []
  takE 1         [a]     = [a]
  takE 1         [a,b]   = [a]
--takE 1         [a,b,c] = [a]
  takE 2     []      = []
  takE 2     [a]     = [a]
  takE 2     [a,b]   = [a,b]
--takE 2     [a,b,c] = [a,b]
  takE 3 []      = []
  takE 3 [a]     = [a]
  takE 3 [a,b]   = [a,b]
--takE 3 [a,b,c] = [a,b,c]
 |]
takePred :: (Int->String->String) -> Bool
takePred take = take 3 "abcde" == "abc"

--  :cmd run $ filtGetOne "weave" "weavePred"
weave = [d|
  weave :: [a] -> [a] -> [a]
  weave [] [] = []
  weave [a][] = [a]
  weave [][c] = [c]
  weave [a][c] = [a,c]
  weave [a,b][] = [a,b]
  weave [][c,d] = [c,d]
  weave [a,b][c] = [a,c,b]
  weave [a][c,d] = [a,c,d]
  weave [a,b][c,d] = [a,c,b,d]
 |]
weavePred weave = weave "abc" "def" == "adbecf"

{-
zeros = [d|
  zeros :: [Int] -> [Int]
  zeros [] = []
  zeros [0] = [0]
  zeros [S x] = []
  zeros [0,S x] = [0]
  zeros [S x,0] = [0]
  zeros [S x,S y] = []
  zeros [0,0] = [0,0]
--zeros [0,S x,S y] = [0]
--zeros [S x,0,S y] = [0]
--zeros [S y,S x,0] = [0]
--zeros [0,0,S x] = [0,0]
--zeros [0,S x,0] = [0,0]
--zeros [S x,0,0] = [0,0]
--zeros [0,0,0] = [0,0,0]
 |]
-}
zeros'7 = [d|
  zeros :: [Int] -> [Int]
  zeros [] = []
  zeros [0] = [0]
  zeros [1] = []
  zeros [0,1] = [0]
  zeros [1,0] = [0]
  zeros [1,1] = []
  zeros [0,0] = [0,0]
 |] -- dame
zeros'14 = [d|
  zeros :: [Int] -> [Int]
  zeros [] = []
  zeros [0] = [0]
  zeros [1] = []
  zeros [0,1] = [0]
  zeros [1,0] = [0]
  zeros [1,1] = []
  zeros [0,0] = [0,0]
  zeros [1,1,1] = []
  zeros [0,1,1] = [0]
  zeros [1,0,1] = [0]
  zeros [1,1,0] = [0]
  zeros [0,0,1] = [0,0]
  zeros [0,1,0] = [0,0]
  zeros [1,0,0] = [0,0]
  zeros [0,0,0] = [0,0,0]
 |] -- dame
zeros'31 = [d|
  zeros :: [Int] -> [Int]
  zeros [] = []
  zeros [0] = [0]
  zeros [1] = []
  zeros [0,1] = [0]
  zeros [1,0] = [0]
  zeros [1,1] = []
  zeros [0,0] = [0,0]
  zeros [1,1,1] = []
  zeros [0,1,1] = [0]
  zeros [1,0,1] = [0]
  zeros [1,1,0] = [0]
  zeros [0,0,1] = [0,0]
  zeros [0,1,0] = [0,0]
  zeros [1,0,0] = [0,0]
  zeros [0,0,0] = [0,0,0]
  zeros [1,1,1,1] = []
  zeros [0,1,1,1] = [0]
  zeros [1,0,1,1] = [0]
  zeros [1,1,0,1] = [0]
  zeros [0,0,1,1] = [0,0]
  zeros [0,1,0,1] = [0,0]
  zeros [1,0,0,1] = [0,0]
  zeros [0,0,0,1] = [0,0,0]
  zeros [1,1,1,0] = []
  zeros [0,1,1,0] = [0,0]
  zeros [1,0,1,0] = [0,0]
  zeros [1,1,0,0] = [0,0]
  zeros [0,0,1,0] = [0,0,0]
  zeros [0,1,0,0] = [0,0,0]
  zeros [1,0,0,0] = [0,0,0]
  zeros [0,0,0,0] = [0,0,0,0]
 |] -- dame

echoOn :: [String] -> [String]
echoOn [] = []
echoOn (x:xs) = ("putStrLn "++ show x) : x : echoOn xs

withEcho :: String -> String
withEcho str = show str ++ '\n' : str ++ "\n"


ins21 = [d|
    ins 0 [] = [0]
    ins 1 [] = [1]
    ins 2 [] = [2]
    ins 0 [0] = [0,0]
    ins 1 [0] = [0,1]
    ins 2 [0] = [0,2]
    ins 0 [1] = [0,1]
    ins 1 [1] = [1,1]
    ins 2 [1] = [1,2]
    ins 0 [2] = [0,2]
    ins 1 [2] = [1,2]
    ins 0 [0,0] = [0,0,0]
    ins 1 [0,0] = [0,0,1]
    ins 2 [0,0] = [0,0,2]
    ins 0 [0,1] = [0,0,1]
    ins 1 [0,1] = [0,1,1]
    ins 2 [0,1] = [0,1,2]
    ins 0 [0,2] = [0,0,2]
    ins 1 [0,2] = [0,1,2]
    ins 0 [1,1] = [0,1,1]
    ins 1 [1,1] = [1,1,1]
  |]
ins30 = [d|
    ins 0 [] = [0]
    ins 1 [] = [1]
    ins 2 [] = [2]
    ins 0 [0] = [0,0]
    ins 1 [0] = [0,1]
    ins 2 [0] = [0,2]
    ins 0 [1] = [0,1]
    ins 1 [1] = [1,1]
    ins 2 [1] = [1,2]
    ins 0 [2] = [0,2]
    ins 1 [2] = [1,2]
    ins 2 [2] = [2,2]
    ins 0 [0,0] = [0,0,0]
    ins 1 [0,0] = [0,0,1]
    ins 2 [0,0] = [0,0,2]
    ins 0 [0,1] = [0,0,1]
    ins 1 [0,1] = [0,1,1]
    ins 2 [0,1] = [0,1,2]
    ins 0 [0,2] = [0,0,2]
    ins 1 [0,2] = [0,1,2]
    ins 2 [0,2] = [0,2,2]
    ins 0 [1,1] = [0,1,1]
    ins 1 [1,1] = [1,1,1]
    ins 2 [1,1] = [1,1,2]
    ins 0 [1,2] = [0,1,2]
    ins 1 [1,2] = [1,1,2]
    ins 2 [1,2] = [1,2,2]
    ins 0 [2,2] = [0,2,2]
    ins 1 [2,2] = [1,2,2]
    ins 2 [2,2] = [2,2,2]
  |]
bmin = [d|
        mi 0 x = 0
        mi 1 0 = 0
        mi 1 1 = 1
        mi 1 2 = 1
        mi 2 0 = 0
        mi 2 1 = 1
        mi 2 2 = 2
       |]
bmax = [d|
        ma 0 0 = 0
        ma 0 1 = 1
        ma 0 2 = 2
        ma 1 0 = 1
        ma 1 1 = 1
        ma 1 2 = 2
        ma 2 0 = 2
        ma 2 1 = 2
        ma 2 2 = 2
       |]
