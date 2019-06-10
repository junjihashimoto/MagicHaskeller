#!/usr/bin/runhaskell

Compile with
ghc -O CGI.lhs -o MagicHaskeller.cgi -package cgi -package mueval -package hint --make -DGHC7

Also, timeout has to be implemented!


The running version of lighttpd ignores stderr, so logCGI actions does not work.
(I checked it using a CGI program written in C.)

\begin{code}
{-# LANGUAGE CPP #-}
module MagicHaskeller.CGI(main', simpleMain) where
import System.IO
import Network
import Network.CGI hiding (Language)
import Data.Char
import Data.Maybe(isJust)
import Data.List(nub, dropWhileEnd)
import System.Environment(getProgName)
import Prelude hiding (catch)
import Control.Monad(when)
import Control.Concurrent
import Control.Exception.Extensible(catch, SomeException(SomeException))
import System.Timeout
import Text.Html
#ifdef UNIX
import Mueval.Interpreter
import Mueval.ArgsParse
import Mueval.Context
import Mueval.Parallel
#endif
import Language.Haskell.Interpreter

import MagicHaskeller.ExpToHtml

import Language.Haskell.Parser
import Language.Haskell.Syntax

-- | The name of the config file. Nothing means the default name, which is "<the program name without the file extention>.conf"
mbConfigFileName = Nothing
-- mbConfigFileName = Just "MagicHaskeller.conf"

data Config = C {computerLanguage :: Language, 
                 portID :: PortID, hostname :: String, maximalDepth :: Int,
                 myPath :: String, -- The user writes a path here, but internally the progName will be added.
                 minimalDepth :: Int, pagesize :: Int, -- These two should be customizable, but anyway, server default should exist.
                 needSignature :: Bool -- 'needSignature' should be True if using GHC<7.6 ON THE SERVER SIDE. (So this cannot be determined by __GLASGOW_HASKELL__.)
                } deriving Read
-- Unfortunately, the Read instance of PortID is not defined in the library!
instance Read PortID where
    readsPrec _ str = case lex str of
#ifdef UNIX
                                      [("UnixSocket", strrest)] -> [ (UnixSocket str, rest) | (str, rest) <- reads strrest ]
#endif
                                      [("PortNumber", numrest)] -> [ (PortNumber $ fromInteger num, rest) | (num, rest) <- reads numrest ]
                                      _ -> []

defaultConfig :: Config
defaultConfig = C {
                  computerLanguage = LHaskell,
                  -- portID = UnixSocket "/usr/lib/cgi-bin/MagicHaskeller/mhserver"
                  portID = PortNumber 55444,
                  hostname = "localhost",
                  -- hostname = "133.54.228.70"
                  maximalDepth = depth defaultQO,
                  --myPath = "/cgi-bin/MagicHaskeller-ghc7.4.1.cgi"
                  --myPath = "/cgi-bin/MagicHaskeller.cgi"
                  myPath = "/cgi-bin/",
                  minimalDepth = 3, -- shown at once
                  pagesize     = 30,
                  needSignature = False
                }

configToTitle = languageToTitle . computerLanguage
languageToTitle LHaskell    = "MagicHaskeller on the Web"
languageToTitle LExcel      = "MagicExceller Server"
languageToTitle LJavaScript = "MagicJavaScripter"

firstlines verInfo config showAbsents predicate =
 "<HTML>" ++
 " <HEAD>" ++
 "  <TITLE> " ++ configToTitle config ++ " </TITLE>" ++
 "  <META NAME=\"AUTHOR\" CONTENT=\"Susumu Katayama\"> \n" ++
 "  <style type='text/css'> \n" ++
 "   <!-- \n" ++
 "     form { margin: 0; } \n" ++
 "     #absentbox {font-size: small} \n" ++
 "     #version {font-size: small} \n" ++
 "     .keyword  {font-weight: bold;} \n" ++
 "     .variable {font-style: oblique;} \n" ++
 "     .notice {font-size: small} \n" ++
 "     .absent {color: grey} \n" ++
 "     .absent a:link {color: #4477cc;} \n" ++
 "     .absent a:visited {color: #807780;} \n" ++
 "   --> \n" ++
 "   </style> \n" ++ dragStart ++
 " </HEAD>" ++
 " <BODY>" ++
 "  <H1> " ++ configToTitle config ++ " </H1>" ++
 "  <div id='version' align='right'>(CGI frontend version " ++ verInfo ++ ") (<a href='?predicate=:version'>Identify the backend version</a>)</div>" ++
 "  Specify a function f by writing a predicate as a boolean-valued expression. You will get functions generalizing the specification.<BR>"
   ++ predicateBox (myPath config) "90" showAbsents predicate
   ++ (case computerLanguage config of
                   LHaskell -> "Help, examples, etc. <a href='/~skata/MagicHaskeller.html'>in English</a> / <a href='/~skata/MagicHaskeller-j.html'>in Japanese</a>"
                   LExcel    -> "Help, examples, etc. <a href='/~skata/MagicExceller.html?lang=en'>in English</a> / <a href='/~skata/MagicExceller.html?lang=ja'>in Japanese</a>")
dragStart =
 "  <script type=\"text/javascript\"> \n" ++
 "  <!-- \n" ++
 "   function dragStart(event) {" ++
 "     event.dataTransfer.setData('text/plain', event.target.textContent || event.target.innerText || '');" ++
 "   } \n" ++
 "  //--> \n" ++
 "  </script>\n"
-- We want to show the following button only when Javascript is enabled.
absentButton True =
 "  <script type=\"text/javascript\"> \n" ++
 "  <!-- \n" ++
 "   function toggle_absent_vis(th) {" ++
 "     var isMSIE = /*@cc_on!@*/false;" ++
 "     var stylesheet = document.styleSheets[document.styleSheets.length - 1];" ++
 "     if (th.value != 'Show absent functions') {" ++
 "       if (isMSIE)" ++
 "         stylesheet.addRule('.absent', '{ display: none;}', 0);" ++
 "       else" ++
 "         stylesheet.insertRule('.absent { display: none;}', 0);" ++
 "       th.value = 'Show absent functions';" ++
 "     } else {" ++
 "       if (isMSIE)" ++
 "         stylesheet.removeRule(0);" ++
 "       else" ++
 "         stylesheet.deleteRule(0) ;" ++
 "       th.value = 'Hide absent functions';" ++
 "     }" ++
 "   } \n" ++
 "   document.writeln(\"<input type='button' name='but' value='Hide absent functions' onClick='toggle_absent_vis(this)'>\"); \n" ++
 "  //--> \n" ++
 "  </script>"
absentButton False = ""

-- The title was (and will be) function details, but currently it is not the right phrase.
detailsHead config =
 "<HTML>" ++
 " <HEAD>" ++
 "  <TITLE> " ++ configToTitle config ++ " --- input-output examples </TITLE>" ++
 "  <META NAME=\"AUTHOR\" CONTENT=\"Susumu Katayama\">"
      ++ detailsStyle ++
 " </HEAD>" ++
 " <BODY>" ++
 "  <H1> " ++ configToTitle config ++ " --- input-output examples </H1>"
detail config predicate = detailsHead config ++ "The candidate expression <BR>" ++ detail' config predicate

thanksHead config =
 "<HTML>" ++
 " <HEAD>" ++
 "  <TITLE> " ++ configToTitle config ++ " --- Thanks! </TITLE>" ++
 "  <META NAME=\"AUTHOR\" CONTENT=\"Susumu Katayama\">"
      ++ detailsStyle ++
 " </HEAD>" ++
 " <BODY>" ++
 "  <H1> Thank you for the feedback! </H1>"
-- | a variant of @detail@ thanking for a suggestion
thanks config predicate = "By the way, the submitted expression <BR>" ++ detail' config predicate

detailsStyle =
 "   <style type='text/css'> \n" ++
 "   <!-- \n" ++
 "     #absentbox {display: none} \n" ++
 "     form { margin: 0; \n" ++
 "            display: inline; \n" ++
 "          } \n" ++
 "   --> \n" ++
 "   </style>"


detail' config predicate =
    "<FORM ACTION=\""++myPath config++"\" METHOD=GET>" ++
 "   f = <INPUT TYPE=TEXT NAME='predicate' VALUE='"++ concatMap escapeQuote predicate ++"' SIZE=90> <INPUT TYPE=\"submit\" VALUE=\"Exemplify\">" ++
 "  </FORM>" ++
 "  <BR> satisfies the following input-output relation: <BR><BR>"
-- about `display: inline;', See newnotes on Nov. 1, 2012 and http://www.cs.tut.fi/~jkorpela/forms/extraspace.html
-- input-output examples画面でabsentboxを表示してもゴチャゴチャするだけなので，隠しておく．
-- 注*1 #absentboxのところは、下記の*1で書いた問題を解決してからテストしたいので，その時はdisplay: noneではなくfont-size: smallにしてからチェックしておきたい．

-- details の画面でbox内をカッコでくくるworkaround. 本当はサーバー側で最初からカッコでくくっておいた方が回りくどくない．
parenthesize xs | last xs == ')' = xs           -- クエリー毎にカッコが増えていかないように，すでにカッコがあると思われるときは括らない．
                | otherwise      = '(':xs++")"

predicateBox myPathName size showAbsents predicate = queryBox  myPathName size showAbsents predicate "Synthesize f"
queryBox myPathName size showAbsents predicate label
  = "<FORM ACTION=\""++myPathName++"\" METHOD=GET>" ++
 "   <INPUT TYPE=TEXT NAME='predicate' VALUE='"++ concatMap escapeQuote predicate++"' SIZE="++size++">" ++
 "  <div id='absentbox'><input type='checkbox' name='absent' value='show' " ++ (if showAbsents then "checked" else "") ++ "> show functions with unused arguments </div>" ++
 "  <INPUT TYPE=\"submit\" VALUE=\"" ++ label ++ "\">" ++
 "  </FORM>"

escapeQuote '\'' = "&apos;"
escapeQuote c    = [c]
examplePredicate = " f \"abcde\" 2 == \"aabbccddee\" "

more myPathName d  sa p = "<FORM ACTION=\""++myPathName++"\" METHOD=GET>" ++
 "    <INPUT TYPE=HIDDEN NAME='depth' VALUE='"++ show d ++"'>" ++
    absentInput sa ++
    " <INPUT TYPE=HIDDEN NAME='predicate' VALUE='"++ concatMap escapeQuote p ++"'>" ++
 "    <INPUT TYPE=\"submit\" VALUE=\"More...\">" ++
 "  </FORM>"
next myPathName pg sa p = "<FORM ACTION=\""++myPathName++"\" METHOD=GET>" ++
 "    <INPUT TYPE=HIDDEN NAME='page' VALUE='"++ show pg ++"'>" ++
    absentInput sa ++
    " <INPUT TYPE=HIDDEN NAME='predicate' VALUE='"++ concatMap escapeQuote p ++"'>" ++
 "    <INPUT TYPE=\"submit\" VALUE=\"Next...\">" ++
 "  </FORM>"

absentInput True  = "<INPUT TYPE=HIDDEN NAME='absent' VALUE='show'>"
absentInput False = ""

lastLines True = "<script language='javascript'> \n" ++
 "<!-- \n" ++
 "var xlanchors = document.getElementsByTagName('a');" ++
 "var lang = location.search.indexOf('lang=ja') >= 0 ? 'ja-jp'" ++
 "                                                   : location.search.indexOf('lang=en') >= 0 ? 'en-us'" ++
 "                                                                                             : (window.navigator.userLanguage || window.navigator.language).indexOf('ja') >= 0 ? 'ja-jp' : 'en-us';" ++
 "for (var i = 0; i < xlanchors.length; i++) {" ++
 "    xlanchors[i].href = xlanchors[i].href.replace('en-us', lang);" ++
 "} \n" ++
 "// --> \n" ++
 "</script>" ++
 "</BODY></HTML>"
lastLines False = "</BODY></HTML>"

unavailable config = detailsHead config ++ "<p>We are sorry, but this functionality is not provided by the CGI frontend built for non-UNIX servers.</p>" ++ lastLines False


main = main' "(Version unknown)" runCGI
main' verInfo run = do
          progName <- getProgName
          let configFileName = maybe (dropWhileEnd (/='.') progName ++ "conf") id mbConfigFileName
          config <- do str <- readFile configFileName
                       return $ readUrk str
                    `catch` \(SomeException _) -> do hPutStrLn stderr $ "Warning: could not read the config file" ++ shows configFileName ". Using the default."
                                                     return defaultConfig
          run (handleErrors (cgiMain verInfo $ config{myPath = myPath config ++ progName}))
simpleMain = do progName <- getProgName
                runCGI (handleErrors $ simpleCgiMain $ defaultConfig{myPath = myPath defaultConfig ++ progName})
cgiMain :: String -> Config -> CGI CGIResult
cgiMain verInfo config
    = let myPathName = myPath config
      in do -- firstlines <- liftIO $ readFile "firstlines"
         mbXL    <- getInput "xl"
         let useJS = case computerLanguage config of LHaskell -> not $ isJust mbXL -- if MagicHaskeller.cgi is called with xl=1, disable JavaScript in order to pass the XSS filter of Internet Explorer.
                                                     _        -> True
         mbAbsent <- getInput "absent"
         let showAbsents = isJust mbAbsent
         mbPred  <- getInput  "predicate"
         case mbPred of
           Just command@(':':xs) | not $ all (`elem` "!@#$%&*+./<=>?\\^|-~:") xs -> passCommand verInfo config showAbsents command -- Just pass it if it is a command. (But be careful about any danger.) 
         -- If unknown commands are also passed without any checking, the backend server must check them and print an error message when necessary.
           Just predicate 
             | all isSpace predicate -> defaultPage verInfo config
             | otherwise -> do
               let qBox    = queryBox myPathName (show $ length predicate `max` 10) showAbsents predicate
                   predBox = qBox "Synthesize f"
               mbCandi <- getInput "candidate"
               case mbCandi of
                 Nothing ->
                   case lex predicate of
                     [(word@(w:_),"")] | isAlpha w || w `elem` "=+!@#$%^&*-\\|:/?<>.~" -> do setHeader "Location" $ snd $ refer word
                                                                                             outputNothing
                     _        -> do setHeader "Content-type" "text/html"
                                    if faru predicate
                                      then organizeSynthesis verInfo config showAbsents predicate useJS
                                      else 
#ifdef UNIX
                                        case fixCandidate predicate of
                                                Left msg -> output $ detail config predicate ++ stringToHtmlString msg ++ lastLines useJS 
                                                Right (candi, fxd)-> do 
                                                  -- liftIO $ putStrLn "Exemplifying the user-supplied expression..."
                                                  mbresult <- liftIO $ runErr $ "showIOPairsHTML \"f\" (generateIOPairs ("++candi++"))"
                                                  -- liftIO $ putStrLn "exemplified."
                                                  logCGI $ "MagHLogUser " ++ candi
                                                  case mbresult of Left  msg    -> output $ detailsHead config ++ blameQuery (qBox "Exemplify") msg ++ lastLines False
                                                                   Right result -> output $ detail config (parenthesize candi) ++ "<table border=0 cellspacing=0 align=left>"++result ++"</table>"++ lastLines useJS
#else
                                        output $ unavailable config
#endif
                 Just candi ->
#ifdef UNIX
                               do -- liftIO $ putStrLn "Exemplifying the synthesized expression..."
--                                result <- liftIO $ genIOPs $ ("showIOPairsWithFormsHTML "++show myPathName++" ")++shows predicate (" \"f\" (generateIOPairs ("++candi++"))") -- This is not good unless the type signature is added, because type variables would be instantiated to ().
                                  eitherResult <- liftIO $ runErr $ ("showIOPairsWithFormsHTML "++show myPathName++" ")++shows predicate (" \"f\" (generateIOPairs (let {f = const ("++candi++") ("++predicate++")} in f))")
                                  
                                  mbSug <- getInput "suggest"
                                  let suggesting = isJust mbSug
                                      errHead | suggesting = blameSuggestion candi predicate
                                              | otherwise  = apologize
                                  logCGI $ (if suggesting then "MagHLogSuggest " else "MagHLogSynth ") ++ candi ++ " ;; " ++ predicate
                                  
                                  case eitherResult of
                                    Left msg     -> output $ (if suggesting then thanksHead else detailsHead) config ++ errHead msg ++ lastLines False
                                    Right result -> do
                                      bs <- liftIO $ runErr ("let {f = " ++ candi ++ "} in " ++ predicate)
                                      case bs of 
                                             Left  msg   -> do logCGI $ "MagHLogErr " ++ msg
                                                               output ((if suggesting then thanksHead else detailsHead) config ++ errHead msg ++ lastLines False)
                                             Right b -> do let pb = if b then predBox else "<strong>not</strong> ("++predBox++")"
                                                           when (not b) $ logCGI $ "MagHLogErr " ++ pb
                                                           output ((if suggesting then thanks else detail) config candi ++ pb ++ "<br><table border=0 cellspacing=0 align=left>"++result ++"</table>"++ lastLines useJS) -- <BR> is necessary for Safari.
                                  -- Exemplifyボタンがちゃんとabsentを設定していないので，showAbsentsを送ってもあまり意味がない．注*1
#else
                                        output $ unavailable config
#endif
           Nothing        -> defaultPage verInfo config

-- blameQuery predBox = "I'm afraid that the expression " ++ predBox ++ " you provided is an invalid Haskell expression, or has an unexpected type." ++ ghcComplaint
-- blameSuggestion candidate = "I'm afraid that your candidate expression<br>" ++ candidate ++ "<br>is either invalid as a Haskell expression or inconsistent with the type of the predicate."
--                   ++ ghcComplaint
-- apologize = "I'm sorry but the candidate expression is inconsistent with the given predicate. Please let <a href='mailto:skata@cs.miyazaki-u.ac.jp'>me</a> know if this situation is caused just by clicking an autogenerated button." ++ ghcComplaint
-- ghcComplaint = "GHC complained with the following error message:"


blamePredicate predBox msg = "I'm afraid that the expression <blockquote>" ++ predBox ++ "</blockquote>caused some error(s):<blockquote>" ++ msg ++ "</blockquote>If you do not understand the error message, please check your expression's validity as a Haskell expression, and make sure that it is a type-consistent unary function returning a boolean value."
blameQuery predBox msg = "I'm afraid that the expression <blockquote>" ++ predBox ++ "</blockquote>caused some error(s):<blockquote>" ++ msg ++ "</blockquote>If you do not understand the error message, please check your expression's validity as a Haskell expression and type consistency with the type of the predicate, and make sure it does not cause an infinite loop."
blameSuggestion candidate predicate msg = "However, I'm afraid that your candidate expression<blockquote>" ++ candidate ++ "</blockquote>with your predicate<blockquote>" ++ predicate ++ "</blockquote>caused some error(s):<blockquote>" ++ msg ++ "</blockquote>If you do not understand the error message, please check your expressions' validity and type consistency as Haskell expressions, and make sure they do not cause an infinite loop."
apologize   msg = "I'm sorry but the candidate expression with the predicate causes some error(s):<blockquote>" ++ msg ++ "</blockquote> Please let <a href='mailto:skata@cs.miyazaki-u.ac.jp'>me</a> know if this situation is caused just by clicking an autogenerated button."

\end{code}

 
"Do you mean?" functionality for I/O example query expressions.
This balances parens by adding some, and lambda-binds free alphabetic 1-letter variables.

Even then, the problem of type variable ambiguity may occur.
\begin{code}
parseExpr e = case parseModule $ "x= "++e of    -- This is a pattern binding, not a function binding.
                                                -- The space after x= is necessary. Without it "x=\a->..." causes parse error. 
     ParseOk (HsModule _ _ _ _ [HsPatBind _ _ (HsUnGuardedRhs hsexp) _]) -> Right hsexp
     ParseFailed _loc msg -> Left msg
countParens (HsParen e) = succ $ countParens e
countParens e = 0

fixCandidate :: String -> Either String (String, Bool)
fixCandidate xs = case balance xs of Left msg   -> Left msg
                                     Right tri  -> Right $ bind tri

balance :: String -> Either String (String, HsExp, Bool) -- Left  msg              if no parse is possible even after fix;
                    -- Right (str, hse, True) if parens are added.
balance xs = let numKokka = count ')' xs
                 numKakko = count '(' xs
                 balanced = replicate numKokka '(' ++ xs ++ replicate numKakko ')'
             in case parseExpr xs of  -- We need this step because parentheses can be in Char and String literals.
                        Left msg -> case parseExpr balanced of
                                                 Left _m -> Left msg
                                                 Right parened -> let redundancy = countParens parened
                                                                  in Right (dropNChars redundancy '(' $ reverse $ dropNChars redundancy ')' $ reverse balanced,
                                                                            parened, True)
                        Right hse -> Right (xs, hse, False)

dropNChars 0 _ xs = xs
dropNChars n c (x:xs) | c==x      = dropNChars (pred n) c xs
                      | isSpace x = dropNChars n        c xs
dropNChars _ _ _      = error "while balancing: cannot happen."

  
bind :: (String, HsExp, Bool) -> (String, Bool)
bind (xs, hse, chg) = case freeVars hse of []    -> (xs, chg)
                                           names -> ("(\\"++unwords names++" -> "++xs++")", True)
-- freeVars obtains the list of unbound 1-letter alphabetic variable names. 
freeVars hse = nub $ fv [] hse []
fv bounds (HsInfixApp e0 qop e1) = fv bounds e0 . freeVarsQOp bounds qop . fv bounds e1
fv bounds (HsApp e0 e1)       = fvList bounds [e0,e1]
fv bounds (HsNegApp e)        = fv bounds e
fv bounds (HsLambda _ pats e) = fv (boundVars pats bounds) e
-- fv bounds (HsLet decls e) =  -- bothered.
fv bounds (HsIf b t f)        = fvList bounds [b,t,f]
fv bounds (HsCase e alts)     = fv bounds e -- I ignore alts. I am just tired.
-- fv bounds (HsDo stmts)      =
fv bounds (HsTuple es)        = fvList bounds es
fv bounds (HsList  es)        = fvList bounds es
fv bounds (HsParen e)         = fv bounds e
fv bounds (HsLeftSection e qop) = fv bounds e . freeVarsQOp bounds qop
fv bounds (HsRightSection qop e) = freeVarsQOp bounds qop . fv bounds e
fv bounds (HsRecConstr _con updates)  = fvRecord bounds updates
fv bounds (HsRecUpdate e    updates)  = fv bounds e . fvRecord bounds updates
fv bounds (HsEnumFrom e)              = fv bounds e
fv bounds (HsEnumFromTo e0 e1)        = fvList bounds [e0,e1]
fv bounds (HsEnumFromThen e0 e1)      = fvList bounds [e0,e1]
fv bounds (HsEnumFromThenTo e0 e1 e2) = fvList bounds [e0,e1,e2]
-- fv bounds (HsListComp e stmts) =
fv bounds (HsExpTypeSig _loc e _qty)  = fv bounds e
fv bounds (HsVar (UnQual (HsIdent name@[_]))) | not $ name `elem` bounds = (name:)
fv bounds _ = id
fvList bounds = foldr (.) id . map (fv bounds)
fvRecord bounds updates = fvList bounds [ e | HsFieldUpdate _ e <- updates ]

freeVarsQOp bounds (HsQVarOp (UnQual (HsIdent name@[_]))) | not $ name `elem` bounds = (name:)
freeVarsQOp _      _  = id
boundVars [] = id
boundVars (HsPNeg p : pats)                  = boundVars (p:pats)
boundVars (HsPInfixApp p0 op p1 : pats)      = qNameToStrs op . boundVars (p0:p1:pats)
boundVars (HsPApp _con ps : pats)            = boundVars ps . boundVars pats
boundVars (HsPTuple ps : pats)               = boundVars ps . boundVars pats
boundVars (HsPList ps : pats)                = boundVars ps . boundVars pats
boundVars (HsPParen p : pats)                = boundVars (p:pats)
boundVars (HsPRec _con patfields : pats)     = boundVars [ p | HsPFieldPat _name p <- patfields ] . boundVars pats
boundVars (HsPAsPat name p : pats)           = nameToStrs name . boundVars (p:pats)
boundVars (HsPIrrPat p : pats)               = boundVars (p:pats)
boundVars (HsPVar (HsIdent name@[_]) : pats) = (name:) . boundVars pats
boundVars (_ : pats)                         = boundVars pats

qNameToStrs :: HsQName -> [String] -> [String]
qNameToStrs (UnQual (HsIdent name@[_])) = (name:)
qNameToStrs _ = id
nameToStrs :: HsName -> [String] -> [String]
nameToStrs (HsIdent name@[_]) = (name:)
nameToStrs _ = id

count :: Char -> String -> Int
count =  (\a b -> length (filter (== a) b)) -- synthesized by MagicHaskeller on the Web:)
\end{code}

\begin{code}
showError verInfo config predicate message = output $ firstlines verInfo config False predicate ++ message ++ lastLines False

organizeSynthesis verInfo config showAbsents predicate useJS = do
  mbIns   <- getInput  "inputs"
  mbOut   <- getInput  "output"
  let augPred
        = case (mbIns, mbOut) of
              (Nothing,  Nothing)  -> predicate
              (Just ins, Just out) -> let str = ") && f "++ins++" ~= "++out
                                      in '(':predicate++str
              _                    -> error "Only one of 'inputs' and 'output' is set."
  
  case review augPred of
      Left  msg                -> showError verInfo config augPred msg
      Right (predi, corrected) -> 
        if needSignature config
          then case addSignature predi of
                      []        -> showError verInfo config augPred "<br><br>Lex error!<br>"
                      [sigPred] -> organizeSynthesis' verInfo config True showAbsents augPred predi sigPred useJS
          else organizeSynthesis' verInfo config corrected showAbsents augPred predi predi useJS

organizeSynthesis' verInfo config corrected showAbsents origPred predicate sigPred useJS = do
  mbPage  <- readInput "page"
  mbDepth <- readInput "depth"

  mbDepthBound <- readInput "depthbound" -- This is used by MagicExceller, for controling the vertical synthesis.
--  let neocon = config{maximalDepth = maybe (maximalDepth config) id mbDepthBound}

--  let reqDepth = min maximalDepth $ 1 + maybe (maybe minimalDepth (const maximalDepth) mbPage) id mbDepth
  let reqDepth = maximalDepth config -- See notes on Apr. 25, 2013
      theReqDepth = maybe reqDepth id mbDepthBound -- `min` reqDepth
  
  result  <- liftIO $ synthesize config $ shows Q{depth = theReqDepth, absents = showAbsents} sigPred

  let body = case result of '!':res -> "<p>"++blamePredicate origPred res
                            _       -> notice++clipped
      results = lines result
      notice | corrected = "<H3>Results:<div class=notice>(Corrected from "++stringToHtmlString origPred++")</div></H3>"
             | otherwise = "<H3>Results:</H3>"
      clipped = case mbPage of
                    Nothing -> case mbDepthBound of 
                                 Nothing -> let shownDepth = maybe (minimalDepth config) id mbDepth
                                            in byDepth config shownDepth showAbsents results origPred useJS
                                 Just shownDepth ->
                                            byDepthBound config shownDepth (showAbsents && useJS) results origPred
                    Just pg -> absentButton (showAbsents && useJS) ++
                               case takeNFORMs (pagesize config) (dropNFORMs (pred pg * pagesize config) result) of
                                 (True, sc) -> sc ++ next (myPath config) (succ pg) showAbsents origPred
                                 (False,sc) -> sc
  output $ firstlines verInfo config showAbsents predicate ++ body ++ lastLines useJS

passCommand verInfo config showAbsents command = do
  result  <- liftIO $ synthesize config command
  output $ firstlines verInfo config showAbsents command ++ "<p>" ++ result ++ lastLines False

defaultPage :: String -> Config -> CGI CGIResult
defaultPage verInfo config = do 
                            setHeader "Content-type" "text/html"
                            showError verInfo config "" ""

stringToHtmlStringBr = concatMap (\c -> case c of {'\n' -> "<br>";_->[c]}) . stringToHtmlString


#ifdef UNIX
-- hack for extracting Mueval.ArgsParse.defaultOptions which is not exported. This is useful for supporting both mueval<0.9 and mueval>=0.9.
Right defaultOptions = interpreterOpts []
-- Functions causing infinite loop should be excluded, and I guess use of Safe Haskell is against this (future) policy.

options = defaultOptions{ 
                   modules = Just ["MagicHaskeller.IOGenerator","Prelude","Data.List","Data.Char","Data.Maybe","Data.Either","MagicHaskeller.FastRatio","MagicHaskeller.LibExcel"]
                 , timeLimit = 5
                 , user = ""
                 , loadFile = ""
                 , printType = False
                 , extensions = False
                 , namedExtensions = ["FlexibleInstances", "UndecidableInstances", "OverlappingInstances", "IncoherentInstances", "ExtendedDefaultRules"]
                 , noImports = False
                 , rLimits = False
                 , help = False }

-- unused
genIOPs :: String -> IO String
genIOPs expr = do result <- runErr expr
                  return $ case result of Left msg -> msg
                                          Right xs -> xs
runErr :: Read a => String -> IO (Either String a)
runErr expr  = do result <- block run options{expression=expr}
                  return $ case result of Left (WontCompile es) -> Left $ stringToHtmlStringBr $ unlines $ map errMsg es
                                          Left e                -> Left $ stringToHtmlStringBr $ show e
                                          Right (_,_,result) -> Right $ readUrk result
               `catch`
               (\e -> return $ Left $ stringToHtmlStringBr $ show (e::SomeException))
{- This is not always forcible.
genIOPs expr = do mb <- timeout 2000000 $    -- two seconds. too short?
                        do result <- runInterpreter $ interpreter $ options{expression="showIOPairs \"<br>\" \"f\" ("++expr++")"}
                           case result of Left e -> return $ show e
                                          Right (_,_,result) -> return result
                  return $ maybe "Timeout occurred.<br>" id mb
               `catch`
               (return . show)
-}
run opts mvar = do mainId <- myThreadId
                   watchDog (timeLimit opts) mainId
                   hSetBuffering stdout NoBuffering

                           -- Our modules and expression are set up. Let's do stuff.
                   forkIO $ ((runInterpreter . interpreter) opts
                                                            >>= putMVar mvar)
                                      `catch` \e -> throwTo mainId (e::SomeException)
#endif

byDepth config depth showAbsents results predicate useJS
  = let 
      myPathName = myPath config
      thatsitblah = thatsit myPathName predicate
    in case splitAt depth results of
                                   (tk,[]) | all null tk -> thatsitblah
                                           | otherwise   -> absentButton (showAbsents && useJS) ++ unlines tk ++ thatsitblah
                                   (tk,_)  | all null tk || null (last tk) -> byDepth config (succ depth) showAbsents results predicate useJS
                                           | otherwise   -> absentButton (showAbsents && useJS) ++
                                                            let cl = unlines tk
                                                            in case takeNFORMs (pagesize config) cl of
                                                                 (False,_) -> cl ++ if depth >= maximalDepth config then thatsitblah else more myPathName (succ depth) showAbsents predicate
                                                                 (True,sc) -> sc ++ next myPathName 2 showAbsents predicate
byDepthBound config depth showAbsents results predicate
  = let 
      myPathName = myPath config
      thatsitblah = thatsit myPathName predicate
    in case splitAt depth results of
                                   (tk, _) | all null tk -> thatsitblah
                                           | otherwise   -> absentButton showAbsents ++ unlines tk ++ thatsitblah

{- 
-- -- The downloadable version is not updated for a while....
-- thatsit = "<br>That's it! More (or less) results may be obtained with <a href='http://nautilus.cs.miyazaki-u.ac.jp/~skata/MagicHaskeller.html'>the downloadable version</a>.<br>"
thatsit = "<br>That's it! Please let <a href='mailto:skata@cs.miyazaki-u.ac.jp'>me</a> know if you think some expression should be synthesized, but isn't.<br>"
-}
thatsit myPathName predicate
  = "<br>That's it! Please submit the right expression in your mind (or your partial solution as a subexpression) if you like." ++
 "   It will be regarded as your suggestion, and may be able to be synthesized by future versions.<br>" ++
 "   <FORM ACTION=\""++myPathName++"\" METHOD=GET>" ++
 "        f = <INPUT TYPE=TEXT NAME='candidate' VALUE='' SIZE=90> <INPUT TYPE=\"submit\" VALUE=\"Suggest\">" ++
 "        <INPUT TYPE=HIDDEN NAME='predicate' VALUE='" ++ predicate ++ "'> <INPUT TYPE=HIDDEN NAME='suggest' VALUE='1'>" ++
 "   </FORM>"
faru xs = case lex xs of []        -> False
                         [("",_)]  -> False
                         [("f",_)] -> True
                         [(_,ys)]  -> faru ys

addSignature xs = do (cs,rest) <- lex xs
                     case cs of "" -> return ""
                                c:cs' | isDigit c && all (/='.') cs'
                                          -> do (token,rest2) <- lex rest
                                                case token of "::" -> fmap ((cs++).("::"++)) $ addSignature rest2
                                                              _    -> fmap (('(':).(cs++).("::Int)"++)) $ addSignature rest
                                      | otherwise -> fmap ((cs++).(' ':)) $ addSignature rest

-- splitAtNBRsにすればよかった．

takeNBRs 0 _  = (True, "")
takeNBRs n "" = (False,"")
takeNBRs n ('<':'b':'r':'>':xs) = case takeNBRs (pred n) xs of (b,r) -> (b, "<br>" ++ r)
takeNBRs n (x:xs)               = case takeNBRs n        xs of (b,r) -> (b, x : r)

dropNBRs 0 xs = xs
dropNBRs n "" = ""
dropNBRs n ('<':'b':'r':'>':xs) = dropNBRs (pred n) xs
dropNBRs n (x:xs)               = dropNBRs n xs

takeNFORMs 0 _  = (True, "")
takeNFORMs n "" = (False,"")
takeNFORMs n ('<':'/':'F':'O':'R':'M':'>':xs) = case takeNFORMs (pred n) xs of (b,r) -> (b, "</FORM>" ++ r)
takeNFORMs n (x:xs)               = case takeNFORMs n        xs of (b,r) -> (b, x : r)

dropNFORMs 0 xs = xs
dropNFORMs n "" = ""
dropNFORMs n ('<':'/':'F':'O':'R':'M':'>':xs) = dropNFORMs (pred n) xs
dropNFORMs n (x:xs)               = dropNFORMs n xs

synthesize :: Config -> String -> IO String
synthesize config predicate = do
                          handle <- connectTo (hostname config) (portID config)
                          hSetBuffering handle LineBuffering
                          hPutStrLn handle predicate
                          hGetContents handle

-- just for testing and debugging
simpleCgiMain :: Config -> CGI CGIResult
simpleCgiMain config
    = do -- firstlines <- liftIO $ readFile "firstlines"
         setHeader "Content-type" "text/html; charset=EUC-JP"
         mbPred  <- getInput  "predicate"
         case mbPred of Just predicate -> do result <- liftIO $ synthesize config predicate
                                             output $ firstlines "" config False predicate ++ unlines (take 3 $ lines result) ++ lastLines False
                        Nothing        -> output $ firstlines "" config False examplePredicate ++ lastLines False

readUrk :: Read a => String -> a
readUrk xs = case reads xs of [(v,ys)] | all isSpace ys -> v
                              _                         -> error $ "urk" ++ xs
\end{code}
