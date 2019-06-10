-- 
-- (c) Susumu Katayama
--
module MagicHaskeller.TyConLib where
import qualified Data.Map as Map
import MagicHaskeller.Types
import Data.Array.IArray
import qualified Language.Haskell.TH as TH
import Data.List(nub)

type Map = Map.Map

type TyConLib = (Map TypeName TyCon, Array Kind [(TypeName,TyCon)])

defaultTCL = tyConsToTCL defaultTyCons

tyConsToTCL :: [(Kind, TypeName)] -> TyConLib
tyConsToTCL tcs
    = (Map.fromListWith (\new old -> old) [ tup | k <- [0..7], tup <- tcsByK ! k ], tcsByK)
    where tnsByK :: Array Kind [TypeName]
          tnsByK = accumArray (flip (:)) [] (0,7) (reverse (nub tcs))
          tcsByK :: Array Kind [(TypeName,TyCon)]
          tcsByK = listArray (0,7) [ tnsToTCs (tnsByK ! k) | k <- [0..7] ]
          tnsToTCs :: [TypeName] -> [(TypeName,TyCon)]
          tnsToTCs tns = zipWith (\ i tn -> (tn, i)) [0..] tns


 -- other info is used when adding type constructors as functions
-- listToFM_C op = addListToFM_C op emptyFM -- moved to XFiniteMap
{-
defaultTyCons :: Kind -> [TypeName]
defaultTyCons 0 = ["()", "Char", "Integer", "Int", "Double", "Float", "Bool"]
defaultTyCons 1 = ["[]", "IO"]
defaultTyCons i | i<=7 = tuplename i
-}
defaultTyCons :: [(Kind, TypeName)]
defaultTyCons = [(0, "()"), (1, "[]")] ++ [ (i, tuplename i) | i<-[2..tupleMax] ] ++ [(0, "Int"), (0, "Char"), (0, "Bool"), (0, "Integer"), (0, "Double"), (0, "Float"), (1,"Maybe"), (1,"IO"), (2,"Either"), (0,"Ordering"), (1,"Ratio"), (1,"Gen")]
tupleMax = 7
{- can be used at least with lthprof
defaultTyCons = []
tupleMax = 0
-}

tuplename i = '(':replicate (i-1) ',' ++")"

unit  tcl   = nameToTyCon tcl "()"
list  tcl   = nameToTyCon tcl "[]"
disj  tcl   = nameToTyCon tcl "Either"
tuple tcl n = nameToTyCon tcl (tuplename n)

nameToTyCon :: TyConLib -> String -> TyCon
nameToTyCon (fm,_) name = case Map.lookup name fm of
                            Nothing -> error "nameToTyCon: unknown TyCon"
                            Just c  -> c

thTypesToTCL thts = tyConsToTCL (thTypesToTyCons thts ++ defaultTyCons)
thTypesToTyCons :: [TH.Type] -> [(Kind,TypeName)]
thTypesToTyCons thtys = [ tycon | thty <- thtys, tycon <- thTypeToTyCons 0 thty ]

thTypeToTyCons :: Kind -> TH.Type -> [(Kind,TypeName)]
thTypeToTyCons k (TH.ForallT names _cxt t) = thTypeToTyCons k t
thTypeToTyCons k (TH.AppT  t u)    = thTypeToTyCons (k+1) t ++ thTypeToTyCons 0 u
thTypeToTyCons 2 TH.ArrowT         = []
thTypeToTyCons 1 TH.ListT          = [(1, "[]")] -- It should be in defaultTyCons
thTypeToTyCons _ (TH.VarT  _name)  = []
thTypeToTyCons k (TH.ConT  qname)  = [(k, show qname)]
thTypeToTyCons k (TH.TupleT  i)    | k == i = [(i, tuplename i)]
thTypeToTyCons k tht = error ("thTypeToTyCons :: Kind error. k = "++show k++" and tht = "++TH.pprint tht)
