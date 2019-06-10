-- 
-- (c) Susumu Katayama
--
{-# LANGUAGE CPP #-}
# ifdef REALDYNAMIC
module MagicHaskeller.MyDynamic(module MagicHaskeller.PolyDynamic, dynamic, dynamicH) where
import MagicHaskeller.PolyDynamic
# else
module MagicHaskeller.MyDynamic(module MagicHaskeller.FakeDynamic, dynamic, dynamicH) where
import MagicHaskeller.FakeDynamic -- MY dynamic
# endif
