-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE CPP #-}
module MagicHaskeller.ReadTypeRep where
import Data.Typeable
import MagicHaskeller.Types as Types
import MagicHaskeller.TyConLib
import Data.Array.IArray((!))
import qualified Data.Map(lookup)

import qualified Language.Haskell.TH as TH

#if __GLASGOW_HASKELL__ < 700
tyConName = tyConString
#endif

{- mkTyCon is now obsolete.
typeToTR ::  TyConLib -> Type -> TypeRep
typeToTR tcl ty = tyToTR tcl 0 ty
tyToTR :: TyConLib -> Kind -> Type -> TypeRep
tyToTR _      0 (TV _)    = typeOf 'c' -- めんどくさいのでとりあえずChar
tyToTR (_,ar) k (TC tc)   | tc >= 0   = mkTyConApp (mkTyCon $ fst ((ar!k) !! fromIntegral tc)) []
                          | otherwise = error "tyToTR: impossible (tc<0)."
tyToTR tcl    k (TA a b)  = mkAppTy (tyToTR tcl (k+1) a) (tyToTR tcl 0 b)
tyToTR tcl    0 (a :-> b) = mkFunTy (tyToTR tcl 0 a) (tyToTR tcl 0 b)
-}

-- とりあえずはFakeでないDynamicでのtype checkに使うだけなので，効率は考えなくてよい．
-- でもまあ，monomorphic限定ならTypeRepの方が速いみたい（？）．ソースを見た感じ，特に，equalityに関しては効率的な実装をやってるみたい．

{- -- 間違ってもう一回同じものを作ってしまった．kindに関してはtcIDを使った方がいいかも？
typeToTR ::  TyConLib -> Type -> TypeRep
typeToTR _       (TV _) = typeOf 'c' -- めんどくさいのでとりあえずChar
typeToTR (_,ar) (TC tc) | tcid >= 0 = mkTyConApp (mkTyCon $ fst ((ar ! tcKind tc) !! tcid)) []
                        | otherwise = error "tyToTR: impossible (tcid<0)."
                        where tcid = tcID tc
typeToTR tcl   (TA f a) = mkAppTy (typeToTR tcl f) (typeToTR tcl a)
typeToTR tcl  (a :-> r) = mkFunTy (typeToTR tcl a) (typeToTR tcl r)
-}

trToType :: TyConLib -> TypeRep -> Types.Type
trToType tcl tr = case splitTyConApp tr of
                    (tc,trs) -> (if tc == funTyCon || show tc == show funTyCon -- dunno why, but sometimes |tc==funTyCon| is not enough.
                                   then trToType tcl (head trs) :-> trToType tcl (head (tail trs))
                                   else foldl TA (TC $ fromJust $ Data.Map.lookup (tyConString' tc) (fst tcl)) (map (trToType tcl) trs))
                        where fromJust (Just x) = x
                              fromJust Nothing  = error (tyConString' tc ++ " does not appear in the component library. (This is a known bug.) For now, please use a type variable instead of "++show tc
                                                                 ++ " and use `matching :: Int -> Memo -> TH.Type -> [[TH.Exp]]'.\n(or maybe you forgot to set a component library?)")
--                              fromJust Nothing = error ("tyConString = "++show (tyConString' tc) ++ ", and fst tcl = "++show (fst tcl))
--                              fromJust Nothing  = error (show tc ++ " does not appear in the component library. Forgot to set one? BTW tc==funTyCon is "++show (tc==funTyCon)++" and funTyCon is "++show funTyCon)
                              tyConString' tc = case tyConName tc of
                                                                         str@(',':_) -> '(':str++")" -- tyConString mistakenly prints "," instead of "(,)".
                                                                         str         -> unqualify str
                                                                         -- Use the unqualified name to avoid confusion
                                                                         -- because Data.Typeable.tyConString shows the unqualified name
                                                                         -- for types defined in the Standard Hierarchical Library
                                                                         -- (though the qualified name is shown when Typeable is derived).
                              unqualify :: String -> String
                              unqualify = reverse . takeWhile (/='.') . reverse

-- Do the following, because (mkTyCon "(->)") may or may not be equivalent to TyCon for functions in general.
funTyCon :: Data.Typeable.TyCon
funTyCon = typeRepTyCon (mkFunTy undefTC undefTC)
-- undef = error "funTyCon" -- Dunno why, but seemingly mkFunTy is strict.
undefTC = mkTyConApp (mkTyCon3 "base" "Prelude" "Hoge") []

trToTHType :: TypeRep -> TH.Type
trToTHType tr = case splitTyConApp tr of
                  (tc,trs) -> if tc == funTyCon || show tc == show funTyCon -- dunno why, but sometimes |tc==funTyCon| is not enough.
                                   then TH.AppT TH.ArrowT (trToTHType (head trs)) `TH.AppT` trToTHType (head (tail trs))
                                   else foldl TH.AppT (TH.ConT (TH.mkName (tyConName tc))) (map trToTHType trs)
                        where tyConToName str = case tyConName str of   "[]"        -> TH.ListT
                                                                        str@(',':_) -> TH.TupleT (length str) -- tyConString mistakenly prints "," instead of "(,)".
                                                                        str         -> TH.ConT $ TH.mkName str
