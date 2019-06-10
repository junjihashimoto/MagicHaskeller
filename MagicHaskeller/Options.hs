{-# LANGUAGE CPP #-}
module MagicHaskeller.Options where
#ifdef TFRANDOM
import System.Random.TF(seedTFGen, TFGen)
#else
import System.Random(mkStdGen, StdGen)
#endif
import MagicHaskeller.Execute(unsafeExecute)
import MagicHaskeller.MemoToFiles(MemoCond, MemoType(..))
import MagicHaskeller.CoreLang
import MagicHaskeller.MyDynamic
import MagicHaskeller.Types(Type)

-- | options that limit the hypothesis space.
data Opt a   = Opt{ primopt :: Maybe a           -- ^ Use this option if you want to use a different component library for the stage of solving the inhabitation problem.
                                                 --   @Nothing@ means using the same one.
                                                 --   This option makes sense only when using *SF style generators, because otherwise the program generation is not staged.
                                                 --   Using a minimal set for solving the inhabitation and a redundant library for the real program generation can be a good bet.
                  , memodepth :: Int -- ^ memoization depth. (Sub)expressions within this size are memoized, while greater expressions will be recomputed (to save the heap space). Only effective when using 'ProgGen' and unless using the 'everythingIO' family.
                  , memoCondPure  :: Type -> Int -> Bool        -- ^ This represents when to memoize. It takes the query type and the query depth, and returns @True@ if the corresponding entry should be looked up from the lazy memo table. Currently this only works for ProgGenSF.
                  , memoCond  :: MemoCond        -- ^ This represents which memoization table to be used based on the query type and the search depth, when using the 'everythingIO' family.
                  , execute :: VarLib -> CoreExpr -> Dynamic -- timeout はこの中でやるべき．IO Dynamicの場合にunsafePerformIOを2回やると変なことになりそうなので．
                  , timeout :: Maybe Int         -- ^ @Just ms@ sets the timeout to @ms@ microseconds. Also, my implementation of timeout also catches inevitable exceptions like stack space overflow. Note that setting timeout makes the library referentially untransparent. (But currently @Just 20000@ is the default!) Setting this option to @Nothing@ disables both timeout and capturing exceptions.
                  , forcibleTimeout :: Bool      -- ^ If this option is @True@, 'System.Posix.Process.forkProcess' instead of 'Control.Concurrent.forkIO' is used for timeout.
                                                 --   The former is much heavier than the latter, but is more preemptive and thus is necessary for interrupting some infinite loops.
                                                 --   This record is ignored if FORCIBLETO is not defined.
                  , guess   :: Bool                 -- ^ If this option is @True@, the program guesses whether each function is a case/catamorphism/paramorphism or not.
                                                 --   This information is used to filter out some duplicate expressions.
                                                 --   (History: I once abandoned this guessing strategy around the time I moved to the library implementation, because
                                                 --   I could not formally prove the exhaustiveness of the resulting algorithm.
                                                 --   For this reason, the old standalone version of MagicHaskeller uses this strategy, but almost the same effect
                                                 --   can be obtained by setting this option to True, or using 'MagicHaskeller.init075' instead of 'MagicHaskeller.initialize'. 
                  , contain :: Bool                 -- ^ This option is now obsolete, and we always assume True now.
                                                 --   If this option was @False@, data structures might not contain functions, and thus types like @[Int->Int]@, @(Int->Bool, Char)@, etc. were not permitted.
                                                 --   (NB: recently I noticed that making this @False@ might not improve the efficiency of generating lambda terms at all, though when I generated combinatory expressions it WAS necessary.
                                                 --   In fact, I mistakenly turned this limitation off, and my code always regarded this as True, but I did not notice that, so this option can be obsoleted.)
                  , constrL :: Bool              -- ^ If this option is @True@, matching at the antecedent of induction rules may occur, which constrains generation of existential types. 
                                                 --   You need to use prefixed @(->)@ to show that some parameter can be matched at the antecedent, e.g.,
                                                 --   @'p' [| ( []::[a], (:)::a->[a]->[a], foldr :: (a->b->b) -> b -> (->) [a] b ) |]@
                                                 --   See LibTH.hs for examples.
                  , tvndelay:: Int               -- ^ Each time the type variable which appears in the return type of a function (e.g. @b@ in @foldr::(a->b->b)->b->[a]->b@)
                                                 --   is expanded to a function type, the search priority of the current computation is lowered by this number.
                                                 --   It's default value is 1, which means there is nothing special, and the priority for each expression corresponds
                                                 --   to the number of function applications in the expression.
                                                 --
                                                 --   Example: when tvndelay = 1,
                                                 --
                                                 --   The priority of
                                                 --
                                                 -- > \xs -> foldr (\x y -> x+y) 0 xs
                                                 --                             
                                                 --   is 5,
                                                 --   because there are five @$@'s in
                                                 --
                                                 -- > \xs -> ((foldr $ (\x y -> ((+) $ x) $ y)) $ 0) xs
                                                 --   
                                                 --   
                                                 --   The priority of
                                                 --   
                                                 -- > \xs ys -> foldr (\x y zs -> x : y zs) (\ws->ws) xs ys
                                                 --   
                                                 --   is 7,
                                                 --   because there are seven @$@'s in
                                                 --   
                                                 -- > \xs ys -> (((foldr $ (\x y zs -> (((:) $ x) $ y) $ zs)) $ (\ws->ws)) $ xs) $ ys
                                                 --   
                                                 --   
                                                 --   Example: when tvndelay = 2,
                                                 --
                                                 --   The priority of
                                                 --   
                                                 -- > \xs -> foldr (\x y -> x+y) 0 xs
                                                 --   
                                                 --   is 5,
                                                 --   because there are five @$@'s in
                                                 --   
                                                 -- > \xs -> ((foldr $ (\x y -> ((+) $ x) $ y)) $ 0) xs
                                                 --   
                                                 --   The priority of
                                                 --   
                                                 -- > \xs ys -> foldr (\x y zs -> x : y zs) (\ws->ws) xs ys
                                                 --   
                                                 --   is 8,
                                                 --   because there are eight @$@'s in
                                                 --   
                                                 -- > \xs ys -> (((foldr $ (\x y zs -> (((:) $ x) $ y) $ zs)) $ (\ws->ws)) $ xs) $$ ys
                                                 --   
                                                 --   where @$$@ denotes the function application caused by expanding a type variable into a function type.
                  , tv1     :: Bool              -- ^ If this option is @True@, the return type of functions returning a type variable (e.g. @b@ in @foldr::(a->b->b)->b->[a]->b@)
                                                 --   can only be replaced with @Eval t => t@ and @Eval t => u -> t@, while if @False@ with @Eval t => t@, @Eval t => u->t@, @Eval t => u->v->t@, etc., where @Eval t@ means t cannot be replaced with a function.
                                                 --   The restriction can be amended if the tuple constructor and destructors are available.
                  , tv0     :: Bool
#ifdef TFRANDOM
                  , stdgen  :: TFGen             -- ^ The random seed.
#else
                  , stdgen  :: StdGen            -- ^ The random seed.
#endif
                  , nrands  :: [Int]             -- ^ number of random samples at each depth, for each type, for the filter applied during synthesis (used by ProgGenSF, &c.).
                  , fcnrand :: Int -> Int        -- ^ number of random samples at each depth, for each type, for the filter applied after synthesis (used by filterThenF, &c.).
                  }

-- | default options
--
-- > options = Opt{ primopt = Nothing
-- >              , memodepth = 10
-- >              , memoCondPure = \ _type depth -> 0<depth
-- >              , memoCond = \ _type depth -> return $ if depth < 10 then Ram else Recompute
-- >              , execute = unsafeExecute
-- >              , timeout = Just 20000
-- >              , forcibleTimeout = False
-- >              , guess   = False
-- >              , contain = True
-- >              , constrL = False
-- >              , tv1     = False
#ifdef TFRANDOM
-- >              , stdgen  = seedTFGen (3497676378205993723,16020016691208771845,6545968067796471226,2770936286170065919)
#else
-- >              , stdgen  = mkStdGen 123456
#endif
-- >              , nrands  = repeat 5
-- >              , fcnrand = (6+)
-- >              }

options :: Opt a
options = Opt{ primopt = Nothing
             , memodepth = 10
             , memoCondPure = \ _type depth -> 0<depth
             , memoCond = \ _ty d -> return $ if d<10 then Ram else Recompute
             , execute = unsafeExecute
             , timeout = Just 20000
             , forcibleTimeout = False 
             , guess   = False
             , contain = True
             , constrL = False
             , tvndelay = 1
             , tv1     = False
             , tv0    = False
#ifdef TFRANDOM
             , stdgen  = seedTFGen (3497676378205993723,16020016691208771845,6545968067796471226,2770936286170065919)
#else
             , stdgen  = mkStdGen 123456
#endif
             , nrands  = nrnds
             , fcnrand = (6+)
             }

-- reducer (opt,_,_,_,_) = execute opt


forget :: Opt a -> Opt ()
forget opt = case primopt opt of Nothing -> opt{primopt = Nothing}
                                 Just _  -> opt{primopt = Just ()}


nrnds = map fnrnds [0..]
chopRnds :: [[a]] -> [[a]]
chopRnds = zipWith take nrnds

{-
fnrnds n | n <= 5    = 5
         | n < 10    = 10-n
         | otherwise = 1
-}
fnrnds _ = 5
{-
fnrnds n | n < 13    = 13-n
         | otherwise = 1
-}
