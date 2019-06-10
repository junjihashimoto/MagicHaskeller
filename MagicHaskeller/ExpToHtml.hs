{-# LANGUAGE CPP, TemplateHaskell #-}
module MagicHaskeller.ExpToHtml(QueryOptions(..), defaultQO, 
                                review,
                                expToPlainString, expSigToString, refer, pprnn, annotateFree, annotateString, Language(..)) where
import Language.Haskell.TH as TH
import Language.Haskell.TH.PprLib(to_HPJ_Doc)
import Text.PrettyPrint
import Network.URI(escapeURIString, isUnreserved)
import Text.Html(stringToHtmlString)
import MagicHaskeller.LibTH(fromPrelude, fromDataList, fromDataChar, fromDataMaybe, Primitive, ords, prelOrdRelated, prelEqRelated, dataListOrdRelated, dataListEqRelated, fromPrelDouble, fromPrelRatio, fromDataRatio)
import Data.Char(isAlpha, ord, isDigit, isSpace, toUpper)
import qualified Data.Map
import qualified Data.IntSet as IS
import Data.Generics
import MagicHaskeller.CoreLang(stripByd_)
import Data.Hashable
import Data.List((\\))
import Control.Monad(mplus)

-- Maybe QueryOptions should be put in a new module.
data QueryOptions  = Q {depth :: Int, absents :: Bool} deriving (Read, Show)
defaultQO = Q {depth = 7, absents = False}




data Language = LHaskell | LExcel | LJavaScript deriving (Read, Show, Eq)

-- | 'review' makes sure the predicate string does not use either let or where, and may correct grammatical mistakes.
--   This check should be done on both the CGI frontend side and the backend server side.
--   (But actually is done only on the CGI side.)
review :: String -> Either String (String,Bool)
review "" = return ("",False)
review xs = case lex xs of
              []             | '"':_ <- dropWhile isSpace xs -> Left "<br><br>Lex error: maybe double-quotes are not balanced.<br>"   -- Unbalanced double-quotes may be automatically closed at the end, but that can be confusing.
                             | otherwise   -> Left "<br><br>Lex error!<br>"
              [("let",   _)] -> Left loopErrMsg
              [("where", _)] -> Left loopErrMsg
              [("=",  rest)] -> do (zs,_)    <- review rest
                                   return ("~= "++zs, True)
              [("&",  rest)] -> do (zs,_)    <- review rest
                                   return ("&& "++zs, True)
              [("NaN",rest)] -> do (zs,_)    <- review rest
                                   return ("(0/0) "++zs, True)
              [("Infinity",rest)] -> do (zs,_)    <- review rest
                                        return ("(1/0) "++zs, True)
              [(tkn,  rest)] -> do (zs,repl) <- review rest
                                   return (tkn++' ':zs, repl)
loopErrMsg = "<br><br>Error: <b>let</b> expressions and <b>where</b> clauses are prohibited here. You can still use " ++ refLink "case" "case" ++ " expressions without <b>where</b> clauses for non-recursive bindings.<br>"



expToPlainString, expToString :: Exp -> String
expToPlainString = ('\n':) . pprint
-- expToString = (\xs -> '(':xs++")<br>") . {- replaceRightArrow . -} pprint . annotateEverywhere -- simple and stupid
expToString = (\xs -> '(':xs++")<br>") . filter (/='\n') . {- replaceRightArrow . -} annotateString LHaskell. pprnn -- no buttons
expSigToString = mkButton -- with buttons

pprnn = renderStyle style{mode=OneLineMode} . to_HPJ_Doc . pprExp 4

isAbsent :: TH.Exp -> Bool
isAbsent (LamE pats e) = any (==WildP) pats || isAbsent e
isAbsent (VarE name)   = nameBase name == "const"
isAbsent _             = False

-- どうも ->をescapeする必要はないみたい．ま，<->みたいな演算子はescapeされているはずだし，<!--   -->みたいなコメントはないはずなので，→で置き換えても害はなさそう．
-- と思ったけど，コピペするのに不便．
replaceRightArrow ""           = ""
replaceRightArrow ('-':'>':xs) = "&rarr;"++replaceRightArrow xs
replaceRightArrow (x:xs)       = x : replaceRightArrow xs


-- Unfortunately, w3m does not understand <button>. 
-- mkButton sig expr body = "<button type='submit' name='predicate' value='(" ++  concatMap escapeHTML (filter (/='\n') (pprint expr)) ++ ") :: "++  sig  ++ "'>Exemplify</button>"++body ++ "<br>"
mkButton :: Language -> [Char] -> [Char] -> Exp -> [Char]
mkButton lang predStr sig expr | usesBlackListed expr = body ++ "<br>"
                               | otherwise = "<FORM"++ (if isAbsent expr then " class='absent'" else "") ++">"
--                                             ++body++"&nbsp;&nbsp;<input type='submit' value='Exemplify'>"
                                               ++"<input type='submit' value='Exemplify'>&nbsp; f &nbsp; = &nbsp; <span draggable='True' ondragstart='dragStart(event)'>"++body
                                             ++"</span><input type=hidden name='predicate' value='" ++  concatMap escapeHTML predStr ++ "'><input type=hidden name='candidate' value='" ++ concatMap escapeHTML pprExp ++ sig  ++ "'></FORM>"
  where pprExp = pprnn expr
        body   = annotateString lang pprExp
-- <FORM>でやる場合、 <br>をつけると改行しすぎ。

usesBlackListed :: TH.Exp -> Bool
usesBlackListed = everything (||) (False `mkQ` (\name -> hash (nameBase name) `IS.member` partial))
partial :: IS.IntSet
partial = IS.fromList $ map hash ["div", "mod", {- my version of -} "enumFromThenTo", "^", "head", -- "!!", -- "chr",  -- used as chr . abs when auto-generated.
                                  "init", "maximum", "minimum", "maximumBy", "minimumBy"]

escapeHTML '<' = "&lt;"
escapeHTML '>' = "&gt;"
escapeHTML '&' = "&amp;"
escapeHTML '"' = "&quot;"
escapeHTML '\'' = "&apos;"
escapeHTML c    = [c]




-- This is the version that can annotate bound variables (if there exists a one-letter library function), but is free from the cheating of moving out the first letter.
-- Also, the unary minus cannot be distinguished from the binary (-)

-- x #define RESPECTQUALIFICATIONS
-- 将来的には、名前が同じでもmoduleごとに違うものをちゃんと扱う。
#ifdef RESPECTQUALIFICATIONS
annotateString lang xs = case lex xs of 
                                   []        -> error $ "parse error during annotateString: " ++ xs ++ "\nThis should not happen, when connected to the right server."
                                   [("","")] -> ""
                                   [(cs@(c:_),'.':rs@(r:_))] | isUpper c && not (isSpace r) -> annStr lang (cs++".") rs -- Without this pattern, '.' in "Data.Maybe.maybe" would be annotated.
                                   [(cs,rs)] ->  (if isSpace $ head xs then (' ':) else id) (annotateWord lang cs ++ annotateString lang rs)

annStr lang mod xs = case lex xs of 
                                   []        -> error $ "parse error during annStr: " ++ xs ++"\nThis should not happen, when connected to the right server."
                                   [("","")] -> error $ "parse error during annStr: " ++ xs ++"\nThis should not happen, when connected to the right server."
                                   [(cs@(c:_),".":rs@(r:_))] | isUpper c && not (isSpace r) -> annStr lang (mod++cs++".") rs -- Without this pattern, '.' in "Data.Maybe.maybe" would be annotated.
                                   [(cs,rs)] ->  (if isSpace $ head xs then (' ':) else id) (annotateWord lang cs ++ annotateString lang rs)
#else
annotateString lang xs = case lex xs of
                                   []        -> error $ "parse error during annotateString: " ++ xs ++ "\nThis should not happen, when connected to the right server."
                                   [("","")] -> ""
                                   [(".",rs@(r:_))] | not $ isSpace (head xs) && isSpace r -> '.' : annotateString lang rs -- Without this pattern, '.' in "Data.Maybe.maybe" would be annotated.
                                   [(cs,rs)] ->  (if isSpace $ head xs then (' ':) else id) (annotateWord lang cs ++ annotateString lang rs)
#endif


-- 「１単語入れればDocumentationに飛ぶ」ってやつも，「lexして残りの部分がall isSpaceならannoatateWordを実行」に拡張できる．となると，let, in, where, case of, doもいるか．さすがにclassとかtypeとかはいいでしょう．whereもいらないか．::や=>は要らないか．ま，この辺は後回しでもよい．

  -- file:///usr/share/doc/haskell98-report/html/haskell98-report-html/lexemes.html#sect2.6 -- Character and String Literals
annotateWord LHaskell cs@('\'':_) = mkLink cs "http://www.haskell.org/onlinereport/haskell2010/haskellch2.html#x7-200002.6" "literal"
annotateWord LHaskell cs@('"' :_) = mkLink cs "http://www.haskell.org/onlinereport/haskell2010/haskellch2.html#x7-200002.6" "literal"

  -- http://www.haskell.org/onlinereport/haskell2010/haskellch3.html#x8-580003.17   -- Pattern Matching
  -- http://www.haskell.org/onlinereport/haskell2010/haskellch3.html#x8-590003.17.1 -- Patterns
annotateWord LHaskell cs@('_' :_) = mkLink cs "http://www.haskell.org/onlinereport/haskell2010/haskellch3.html#x8-580003.17" "keyword"
  -- _１文字の場合はkeywordと考えてもよい．てか，MagHでは現状は１文字の場合しかない．keywordだと太字．まあ，_が変数名の真ん中で使えることを考えるとkeywordか．

  -- file:///usr/share/doc/haskell98-report/html/haskell98-report-html/lexemes.html#sect2.5 -- Numeric Literals
annotateWord LHaskell cs@(c   :_) 
                         | isDigit c = mkLink cs "http://www.haskell.org/onlinereport/haskell2010/haskellch2.html#x7-190002.5" "literal"
                         | otherwise = case referMb cs of Just (cls, str) -> mkLink cs str cls
                                                          Nothing | isAlpha c -> "<span class=variable>"++cs++"</span>" 
                                                                  | otherwise -> cs
annotateWord LExcel cs = case Data.Map.lookup capcs xlmap of Nothing       -> cs -- bound variablesは小文字のまま。
                                                             Just filename -> "<a href='https://support.office.com/en-us/article/Excel"++filename++"?ui=en-US&rs=en-US&ad=US'>"
-- 古いやつ
-- Just filename -> "<a href='http://office.microsoft.com/en-us/excel-help/redir/"++filename++"'>" -- ?CTT=5&origin=HP005204211 ってのが付いてたけど、なくてもちゃんと飛んでくれる。
                                                                              ++ capcs ++ "</a>"
  where capcs = map toUpper cs
annotateWord _ [] = []


xlmap :: Data.Map.Map String String
xlmap = Data.Map.fromList $ read $(fmap (LitE . StringL) $ runIO $ readFile "xlmap")






-- version that never mistakenly annotate bound variables, but is with cheating of moving out the first letter, seen in annotateName.
annotateEverywhere = everywhere (mkT annotateName)

annotateFree :: [String] -> TH.Exp -> TH.Exp
annotateFree names v@(VarE name) | show name `elem` names = v
                                 | otherwise              = VarE $ annotateName name
annotateFree _     (ConE name)         = ConE $ annotateName name
annotateFree _     l@(LitE _)          = l
annotateFree names (AppE f e)          = annotateFree names f `AppE` annotateFree names e
annotateFree names (InfixE mbf op mbe) = InfixE (fmap (annotateFree names) mbf) (annotateFree names op) (fmap (annotateFree names) mbe)
annotateFree names (LamE pats e)       = LamE pats $ annotateFree (patsToNames pats names) e
annotateFree names (TupE es)           = TupE $ map (annotateFree names) es
annotateFree names (CondE b t f)       = CondE (annotateFree names b) (annotateFree names t) (annotateFree names f)
annotateFree names (ListE es)          = ListE $ map (annotateFree names) es
annotateFree names (SigE e t)          = SigE (annotateFree names e) t
annotateFree names e                   = annotateEverywhere e  -- bothered....

patsToNames []          = id
patsToNames (p:ps)      = patToNames p . patsToNames ps
patToNames (VarP name)    = (show name :)
patToNames (TupP ps)      = patsToNames ps
patToNames (ConP _ ps)    = patsToNames ps
patToNames (InfixP p _ q) = patsToNames [p,q]
patToNames (TildeP p)     = patToNames p
patToNames (AsP name p)   = (show name :) . patToNames p
patToNames (ListP ps)     = patsToNames ps
patToNames (SigP p _)     = patToNames p
patToNames _              = id


-- 名前の1文字目が記号だとbinary operator扱いになってカッコがついてしまうので．
annotateName :: TH.Name -> TH.Name
annotateName name = case nameBase name of nameStr@(c:cs) | isAlpha c                        -> mkName $ c : refLink nameStr cs
                                                         | c `elem` "=+!@#$%^&*-\\|:/?<>.~" -> mkName $ refLink nameStr $ stringToHtmlString nameStr
                                          _              -> name        -- special names like [] and ()
refLink nameStr body = case refer nameStr of (cls, url) -> mkLink body url cls
refer nameStr = case referMb nameStr of Just tup -> tup
                                        Nothing  -> ("variable", referHoogle nameStr)
mkLink body url cls = "<a href='"++url++"' class="++cls++">"++body++"</a>"
referMb str = do (cls, f) <- Data.Map.lookup str mapNameModule `mplus` Data.Map.lookup (str++"By") mapNameModule
                 return (cls, f str)
mapNameModule :: Data.Map.Map String (String, String->String)
mapNameModule = Data.Map.fromList $
                mkAssoc "base" "Prelude"    preludeNameBases ++ 
                mkAssoc "base" "Data-List"  (["\\\\"] ++ primssToStrs fromDataList ++ [ stripByd_ nm | nm <- primssToStrs $ dataListOrdRelated ++ dataListEqRelated ]) ++
                mkAssoc "base" "Data-Char"  dataCharNameBases ++
                mkAssoc "base" "Data-Maybe" (primssToStrs fromDataMaybe) ++
                mkAssoc "base" "Data-Ratio" (primssToStrs fromDataRatio) ++
                [ (kw, ("keyword", const $ repch3 ++ str)) | (kw, str) <- [
                                                                           ("@",   "#x8-580003.17"), -- Pattern Matching
                                                                           ("~",   "#x8-580003.17"), -- Pattern Matching
                                                                           ("..",  "#x8-400003.10"), -- Arithmetic Sequences
                                                                           ("\\",  "#x8-260003.3"),  -- Curried Applications and Lambda Abstractions
                                                                           ("->",  "#x8-260003.3"),  -- Curried Applications and Lambda Abstractions
                                                                           ("if",  "#x8-320003.6"),  -- Conditionals
                                                                           ("then","#x8-320003.6"),  -- Conditionals
                                                                           ("else","#x8-320003.6"),  -- Conditionals
                                                                           (":",   "#x8-340003.7"),  -- Lists
                                                                           ("let", ""),              -- Let can appear at different places.
                                                                           ("in",  "#x8-440003.12"), -- Let
                                                                           ("case","#x8-460003.13"), -- Case
                                                                           ("of",  "#x8-460003.13"), -- Case
                                                                           ("do",  "#x8-470003.14"), -- Do
                                                                           ("::",  "#x8-560003.16")  -- Expression type-signatures
                                                                          ] ] ++
                [ (kw, ("other", const $ repch3 ++ str)) | (kw, str) <- [
                                                                           ("[",   ""), -- There are some possibilities, so the syntax is pointed.
                                                                           ("]",   ""),
                                                                           ("|",   ""),
                                                                           ("`",   "#x8-240003.2"), -- Variables, Constructors, Operators, and Literals
                                                                           ("-",   "#x8-280003.4")   -- Operator Applications
                                                                        ] ]
repch3 = "http://www.haskell.org/onlinereport/haskell2010/haskellch3.html"

mkAssoc package mod namebases = [ (str, ("variable", referHackage package mod)) | str <- namebases ]

preludeNameBases = ["iterate", "!!", "id", "$", "const", ".", "flip", "subtract", "maybe", "foldr", "foldl", "zipWith", "either", "last"] ++   -- These are not included in the component library, but introduced by MagicHaskeller.LibTH.postprocess.
                   (primssToStrs fromPrelude \\ [":","-"]) ++ primssToStrs fromPrelDouble ++ primssToStrs fromPrelRatio ++ [ stripByd_ nm | nm <- primssToStrs $ prelOrdRelated ++ prelEqRelated ]
dataCharNameBases = ["chr"] ++ 
                    primssToStrs fromDataChar

primssToStrs = primsToStrs . concat
primsToStrs = map TH.nameBase . primsToNames
primsToNames  :: [Primitive] -> [TH.Name]
primsToNames ps = [ name | (_, VarE name, _) <- ps ] ++ [ name | (_, ConE name, _) <- ps ]
                  ++ [ name | (_, _ `AppE` VarE name, _) <- ps ] -- ad hoc approach to the (flip foo) cases:)

-- So far this should work:
referHackage package modulename str = "http://hackage.haskell.org/packages/archive/"++package++"/latest/doc/html/"++modulename++".html#v:"++hackageEncode str
hackageEncode cs@(a:_) | isAlpha a = cs
                       | otherwise = concatMap (\c -> '-' : shows (ord c) "-") cs

-- But this is more generic:)
referHoogle  str = "http://www.haskell.org/hoogle/?hoogle=" ++ escapeURIString isUnreserved str
