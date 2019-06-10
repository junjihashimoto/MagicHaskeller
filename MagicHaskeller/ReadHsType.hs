module MagicHaskeller.ReadHsType(readHsTypeSigs) where
import Language.Haskell.TH as TH
import Language.Haskell.Syntax
import Language.Haskell.Parser
import Data.List

import MagicHaskeller.ReadTHType(plainTV)

-- | @readHsTypeSigs@ reads a module string and returns an Exp that can be supplied to MagicHaskeller.p
readHsTypeSigs :: String -> TH.Exp
readHsTypeSigs str = TupE [ mkSigE hsname hsqty
                            | HsTypeSig _loc hsnames hsqty <- readHsDecls str
                            , hsname <- hsnames ]

mkSigE :: HsName -> HsQualType -> TH.Exp
mkSigE hsname hsqty = SigE (VarE $ hsNameToTHName hsname) (hsQTypeToTHType hsqty)

hsQTypeToTHType :: HsQualType -> TH.Type
-- hsQTypeToTHType (HsQualType cxt hsty) = ForallT (map (plainTV . hsNameToTHName) $ map head $ group $ sort $ varnames [] hsty) (map hsAsstToTHType cxt) (hsTypeToTHType hsty) -- This is incorrect since template-haskell-2.4*, so just forget the contexts. 
hsQTypeToTHType (HsQualType [] hsty) = ForallT (map (plainTV . hsNameToTHName) $ map head $ group $ sort $ varnames [] hsty) [] (hsTypeToTHType hsty)
hsQTypeToTHType (HsQualType _cxt _hsty) = error "Contexts are not supported yet."
hsTypeToTHType (HsTyTuple hts)   = foldl AppT (TupleT (length hts)) (map hsTypeToTHType hts)
hsTypeToTHType (HsTyFun ht0 ht1) = ArrowT `AppT` (hsTypeToTHType ht0) `AppT` (hsTypeToTHType ht1)
hsTypeToTHType (HsTyApp ht0 ht1) = (hsTypeToTHType ht0) `AppT` (hsTypeToTHType ht1)
hsTypeToTHType (HsTyCon hsqname) = hsQNameToTHType hsqname
hsTypeToTHType (HsTyVar hsname)  = VarT $ hsNameToTHName hsname
-- The above definition should be exhaustive
varnames vs (HsTyTuple hts)   = foldl varnames vs hts
varnames vs (HsTyFun ht0 ht1) = varnames (varnames vs ht0) ht1
varnames vs (HsTyApp ht0 ht1) = varnames (varnames vs ht0) ht1
varnames vs (HsTyCon _)       = vs
varnames vs (HsTyVar hsname)  = hsname:vs

hsNameToTHName = mkName . hsNameToString

hsNameToString (HsIdent  str) = str
hsNameToString (HsSymbol str) = str -- Was: '(':str++")"

hsAsstToTHType :: HsAsst -> TH.Type
hsAsstToTHType (hsqname, hstypes) = foldl AppT (hsQNameToTHType hsqname) (map hsTypeToTHType hstypes)

hsQNameToTHType (UnQual hsname) = ConT $ hsNameToTHName hsname
hsQNameToTHType (Qual _ hsname) = ConT $ hsNameToTHName hsname -- qualifications over type names are ignored for now.
hsQNameToTHType (Special HsFunCon)  = ArrowT
hsQNameToTHType (Special HsUnitCon) = ConT $ mkName "()"
hsQNameToTHType (Special HsListCon) = ListT
hsQNameToTHType (Special (HsTupleCon n)) = TupleT n


readHsDecls :: String -> [HsDecl]
readHsDecls src = case parseModule src of ParseOk (HsModule _loc _nam _ex _imports decls) -> decls
                                          ParseFailed (SrcLoc _fn line column) str
                                                        -> error (str ++ " in " ++ shows line ":" ++ shows column " of\n" ++ src)
