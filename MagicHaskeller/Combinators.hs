-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE TemplateHaskell #-}
module MagicHaskeller.Combinators where
import MagicHaskeller.ExprStaged
import Language.Haskell.TH
import Debug.Trace
finiteHVss = $(do dss <- mapM (\lenavails -> mapM (\arity -> hdmnTHEQ arity lenavails) [0..maxArity]) [0..maxLenavails]
                  return $ ListE $ map ListE dss)
finiteHVsss = $(do dsss <- mapM (\debindex -> mapM (\lenavails -> mapM (\arity -> aimnTHEQ debindex arity lenavails) [0..maxArity]) [debindex+1..maxLenavails]) [0..maxDebindex]
                    -- trace (pprint $ ListE $ map (ListE . map ListE) dsss) $
                   return $ ListE $ map (ListE . map ListE) dsss)
