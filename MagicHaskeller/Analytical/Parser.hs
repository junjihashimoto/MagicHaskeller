-- 
-- (C) Susumu Katayama
--
module MagicHaskeller.Analytical.Parser where

import Data.List(sort, group, genericLength)
import Control.Monad -- hiding (guard)
import Control.Monad.State -- hiding (guard)
import Data.Char(ord)
import Data.Array
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import Language.Haskell.TH hiding (match)

import MagicHaskeller.CoreLang(VarLib, Var)
import qualified MagicHaskeller.Types as T
import MagicHaskeller.PriorSubsts hiding (unify)
import MagicHaskeller.TyConLib
import MagicHaskeller.ReadTHType(thTypeToType)
import qualified MagicHaskeller.PolyDynamic as PD

import MagicHaskeller.Analytical.Syntax

import Data.Word

data XVarLib = XVL {varLib :: VarLib, invVarLib :: Map.Map String Var, zeroID :: Var, succID :: Var, negateID :: Var} deriving Show

-- We compare nameBase ignoring the module name, instead of using equivalence over Name's.
mkXVarLib :: VarLib -> XVarLib
mkXVarLib vl = let
                   (_,mx) = bounds vl
               in XVL {varLib = vl
                      , invVarLib = Map.fromListWith (\_ a -> a) ([ (nameBase name, num) | (num, PD.Dynamic{PD.dynExp=thexpr}) <- assocs vl, name <- extractName thexpr ])
                      , zeroID = mx-2   -- These are dependent on the order in CoreLang.defaultPrimitives
                      , succID = mx-1
                      , negateID = mx
                      }
extractName (ConE name) = [name]
extractName (VarE name) = [name]
extractName _           = []
parseTypedIOPairss :: (Functor m, MonadPlus m) => TyConLib -> XVarLib -> [Dec] -> PriorSubsts m [(Name, T.Typed [IOPair T.Type])]
parseTypedIOPairss tcl xvl ds = inferTypedIOPairss =<< parseTypedIOPairss' tcl xvl ds
inferTypedIOPairss :: (Functor m, MonadPlus m) => [(Name,(Maybe T.Type, Maybe (T.Typed [IOPair T.Type])))] -> PriorSubsts m [(Name, T.Typed [IOPair T.Type])]
inferTypedIOPairss ((name, (Just ty, Just (iops T.::: infty))):ts)
    = do apinfty <- applyPS infty
         mguPS apinfty $ T.quantify ty
--         updateSubstPS (return . unquantifySubst)

         s <- getSubst
         let hd = (name, map (tapplyIOP s) iops T.:::ty)
         tl <- inferTypedIOPairss ts
         return (hd:tl)
inferTypedIOPairss ((name, (Nothing, Just (iops T.::: infty))):ts)
    = do s <- getSubst
         let hd = (name, map (tapplyIOP s) iops T.::: T.apply s infty)
         tl <- inferTypedIOPairss ts
         return (hd:tl)
inferTypedIOPairss ((_nam, (Just _t, Nothing)):ts) = inferTypedIOPairss ts -- pattern including only a type signature. This is still useful when incorporating with MagicHaskeller, but MagH has its own parser, so let's ignore the pattern silently.
inferTypedIOPairss ((_,    (Nothing, Nothing)):_)  = error "MagicHaskeller.TypedIOPairs.inferTypedIOPairss: impossible"
inferTypedIOPairss [] = return []

parseTypedIOPairss' :: (Functor m,MonadPlus m) => TyConLib -> XVarLib -> [Dec] -> PriorSubsts m [(Name, (Maybe T.Type, Maybe (T.Typed [IOPair T.Type])))]
parseTypedIOPairss' tcl xvl ds
    = do tups <- parseIOPairss xvl ds
         return $ Map.toList $ Map.fromListWith plus
                    ([(name, (Just t,  Nothing))   | (name, t)    <- parseTypes tcl ds] ++
                     [(name, (Nothing, Just tiops)) | (name, tiops) <- tups])
(a,b) `plus` (c,d) = (a `mplus` c, b `mplus` d)

parseTypes :: TyConLib -> [Dec] -> [(Name,T.Type)]
parseTypes tcl ds = [ (name, thTypeToType tcl ty) | SigD name ty <- ds ]


parseIOPairss :: (Functor m, MonadPlus m) => XVarLib -> [Dec] -> PriorSubsts m [(Name, T.Typed [IOPair T.Type])]
parseIOPairss xvl (FunD funname clauses : decs) 
    = do tiops <- mapM (clauseToIOPair xvl) clauses
         let (iops,t:ts) = unzipTyped tiops
         ty <- foldM mgtPS t ts
         s <- getSubst
         let hd = (funname, map (tapplyIOP s) iops T.::: ty)
         tl <- parseIOPairss xvl decs
         return $ hd:tl
parseIOPairss xvl (ValD (VarP name) (NormalB ex) [] : decs)
    = do (vout, _intmap) <- runStateT (inferType (thExpToExpr xvl ex)) IntMap.empty
         let hd = (name,    [IOP 0 [] vout] T.::: ann vout)
         tl <- parseIOPairss xvl decs
         return $ hd:tl
parseIOPairss xvl (_:decs) = parseIOPairss xvl decs
parseIOPairss _   []       = return []

-- 型宣言がある場合，そのforallなやつにマッチして終了．
-- ない場合，そのまま関数にして終了．
clauseToIOPair :: (Functor m, MonadPlus m) => XVarLib -> Clause -> PriorSubsts m (T.Typed (IOPair T.Type))
clauseToIOPair ivl cl = fmap fst $ runStateT (clauseToIOPair' ivl cl) IntMap.empty
clauseToIOPair' ivl (Clause inpats (NormalB ex) []) =do ins <- mapM inferT (reverse $ map (patToExp ivl) inpats)
                                                        vout <- inferT (thExpToExpr ivl ex)
                                                        ty <- lift $ applyPS (T.popArgs (map ann ins) $ ann vout)
                                                        return $ normalizeMkIOP ins vout T.::: ty
clauseToIOPair' _ _ = error "Neither _guards_ nor _where_clauses_ are permitted in clauses representing I/O pairs." 
-- In future where-clauses might be supported.


matchType :: (Functor m, MonadPlus m) => [T.Type] -> T.Type -> T.Type -> PriorSubsts m ()
matchType argtys retty ty = mguType argtys retty (T.quantify ty) >> updateSubstPS (return . unquantifySubst)
unquantifySubst = map (\(v,t) -> (v, T.unquantify t))
mguType (t:ts) r (u T.:->v) = do mguPS t u
                                 s <- getSubst
                                 mguType (map (T.apply s) ts) (T.apply s r) v
mguType []     r v       = T.mgu r v
mguType (_:_)  _ _       = error "Not enough arguments supplied."


inferType, inferT :: (Functor m, MonadPlus m) => Expr a -> StateT (IntMap.IntMap T.Type) (PriorSubsts m) (Expr T.Type)
inferType e = do e' <- inferT e
                 s <- lift getSubst
                 return $ tapplyExpr s e'
inferT v@(U _ i) = do 
                    tenv <- get
                    case IntMap.lookup i tenv of
                        Nothing -> do tvid <- lift newTVar
                                      let ty = T.TV tvid
                                      put $ IntMap.insert i ty tenv
                                      return (U ty i)
                        Just ty -> do apty <- lift $ applyPS ty
                                      return (U apty i)
inferT (C _ sz (i T.:::ty) es)
                       = do es' <- mapM inferT es
                            lift $ do let tvs = map head $ group $ sort $ T.tyvars ty
                                      tvid <- reserveTVars $ genericLength tvs
                                      let apty = T.apply (zip tvs $ map T.TV [tvid..]) ty
                                      rty <- foldM funApM apty $ map ann es'
                                      rapty <- applyPS rty
                                      return $ C rapty sz (i T.:::apty) es'
funApM :: (Functor m, MonadPlus m) => T.Type -> T.Type -> PriorSubsts m T.Type
funApM (a T.:-> r) t = fAM a r t
funApM (a T.:>  r) t = fAM a r t
funApM (T.TV i)    t = do tvid <- newTVar
                          updatePS [(i,t T.:->T.TV tvid)]
                          return $ T.TV tvid
funApM _         _ = fail "too many arguments applied."
fAM apa r t = do apt <- applyPS t
                 mguPS apa apt
                 applyPS r
tapplyIOP :: T.Subst -> IOPair T.Type -> IOPair T.Type
tapplyIOP s (IOP bvs ins out) = IOP bvs (map (tapplyExpr s) ins) (tapplyExpr s out)

tapplyExpr :: T.Subst -> Expr T.Type -> Expr T.Type
tapplyExpr sub (C t sz (i T.:::cty) es) = C (T.apply sub t) sz (i T.:::T.apply sub cty) (map (tapplyExpr sub) es)
tapplyExpr _   v               = v
{-
substitutionを一度getしたら，それを全体に波及させる必要がある？
てゆーか，各コンストラクタのforallでfreshVarしたやつだけすればよい？
考えるの面倒くさいし，律速ではないので2パスで．
-}

-- MagicHaskeller.Typesに置くべきという気がしないでもない．
unzipTyped [] = ([],[])
unzipTyped ((e T.:::t):ets) = let (es,ts) = unzipTyped ets in (e:es,t:ts)


getMbTypedConstr :: XVarLib -> Name -> Maybe (T.Typed Constr)
getMbTypedConstr xvl name = fmap (mkTypedConstr xvl) $ Map.lookup (nameBase name) (invVarLib xvl)
getTypedConstr :: XVarLib -> Name -> T.Typed Constr
getTypedConstr xvl name = case Map.lookup (nameBase name) $ invVarLib xvl of Just c -> mkTypedConstr xvl c
                                                                             Nothing -> error ("could not find "++show name)
mkTypedConstr  xvl c   = c T.::: PD.dynType (varLib xvl!c)
patToExp ivl (LitP (IntegerL i)) | i>=0      = natToConExp ivl i
                                 | otherwise = cap () (mkTypedConstr ivl (negateID ivl)) [natToConExp ivl (-i)]
-- patToExp tcl (LitP (CharL c))     = C (Ctor (ord c) (cに相当する奴. ある訳ない?)) []
-- patToExp tcl (LitP (StringL str)) = strToConExp tcl str
patToExp ivl (VarP name)   = U () (strToInt $ nameBase name)
patToExp ivl (TupP pats)         = cap () (getTypedConstr ivl (tupleDataName (length pats))) (map (patToExp ivl) pats)
patToExp ivl (ConP name pats)    = cap () (getTypedConstr ivl name)                          (map (patToExp ivl) pats)
patToExp ivl (InfixP p1 name p2) = cap () (getTypedConstr ivl name)                          (map (patToExp ivl) [p1,p2])
patToExp ivl (TildeP p)    = patToExp ivl p
patToExp ivl (AsP _ _)     = error "As (@) patterns not supported."
patToExp ivl WildP         = U () (strToInt "_") -- will not work correctly if there are more than one wildcards in one I/O pair, I think.
patToExp ivl (RecP _ _)    = error "Record patterns not supported."
patToExp ivl (ListP pats)  = foldr cons nil $ map (patToExp ivl) pats 
    where nil        = C () 1 (getTypedConstr ivl '[]) []
          cons e1 e2 = cap () (getTypedConstr ivl '(:)) [e1,e2]
patToExp ivl (SigP pat _t) = patToExp ivl pat -- Or should this cause an error?

-- Is this encoding really quicker than raw String (or maybe PackedString)?
strToInt [] = 1
strToInt (x:xs) = ord x + 256 * strToInt xs

natLimit = 32
natToConExp ivl i -- x | i > natLimit = C (Ctor i  (iに相当する奴. ある訳ない?)) []
                  | otherwise    = smallNat ivl i
smallNat ivl 0 = C () 1 (mkTypedConstr ivl (zeroID ivl)) []
smallNat ivl i = cap () (mkTypedConstr ivl (succID ivl)) [smallNat ivl (i-1)]
-- strToConExp tcl "" = C (Ctor 0 ([]に相当する奴)) []

thExpToExpr :: XVarLib -> Exp -> Expr ()
thExpToExpr ivl (VarE name) = case getMbTypedConstr ivl name of Nothing -> U () (strToInt $ nameBase name)
                                                                Just x  -> C () 1 x []
thExpToExpr ivl (ConE name) = C () 1 (getTypedConstr ivl name) []
thExpToExpr ivl (LitE (IntegerL i)) | i >= 0    = natToConExp ivl i
                                    | otherwise = cap () (mkTypedConstr ivl (negateID ivl)) [natToConExp ivl (-i)]
thExpToExpr ivl (AppE f x)  = case thExpToExpr ivl f of C () sz c xs -> let thx = thExpToExpr ivl x
                                                                        in C () (sz + size thx) c (xs ++ [thx])  -- O(n^2)
                                                        U () _    -> error "Only constructor applications are permitted in IO examples."
thExpToExpr ivl (InfixE (Just x) (ConE name) (Just y)) = cap () (getTypedConstr ivl name) [thExpToExpr ivl x, thExpToExpr ivl y]
thExpToExpr ivl (InfixE (Just x) (VarE name) (Just y)) = cap () (getTypedConstr ivl name) [thExpToExpr ivl x, thExpToExpr ivl y]
thExpToExpr ivl (TupE es) = cap () (getTypedConstr ivl (tupleDataName (length es))) (map (thExpToExpr ivl) es)
thExpToExpr ivl (ListE es) = foldr cons nil $ map (thExpToExpr ivl) es 
    where nil        = cap () (getTypedConstr ivl '[]) []
          cons e1 e2 = cap () (getTypedConstr ivl '(:)) [e1,e2]
thExpToExpr ivl (SigE e _t) = thExpToExpr ivl e
thExpToExpr _ _ = error "Unsupported expression in IO examples."
{-
caseの場合，既にあるprimitive componentに合わせるのは結構ややこしい．（たとえば，コンストラクタの順序づけとかを合わせるのはってことね．）
コンストラクタの順序づけはreifyでゲットした順にすることにして，caseは直接THを生成することにする．
これが可能なのは，まずanalyticalやってそれからsystematicをやるから．

そうなると，clauseToIOPairとかにVarLibはいらなくなるし，ConstrはCoreExprの代わりにTH.Exp(かTH.Name)を持つことになる．
-}
