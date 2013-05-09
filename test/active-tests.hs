{-# LANGUAGE FlexibleContexts #-}
module Main where

import Control.Applicative
import Control.Monad   (when)
import Data.Semigroup

import System.Exit     (exitFailure)

import Test.QuickCheck
import Text.Printf     (printf)

import Data.Active hiding (choose)
import Data.VectorSpace
import Data.AffineSpace

main :: IO ()
main = do
    results <- mapM (\(s,t) -> printf "%-40s" s >> t) tests
    when (not . all isSuccess $ results) $ exitFailure
  where
    isSuccess (Success{}) = True
    isSuccess _ = False
    qc x = quickCheckWithResult (stdArgs { maxSuccess = 200 }) x
    tests = [ ("era/start",                   qc prop_era_start          )
            , ("era/end",                     qc prop_era_end            )
            , ("duration",                    qc prop_duration           )
            , ("shiftDyn/start",              qc prop_shiftDynamic_start )
            , ("shiftDyn/end",                qc prop_shiftDynamic_end   )
            , ("shiftDyn/fun",                qc prop_shiftDynamic_fun   )
            , ("active/semi-hom",             qc prop_active_semi_hom    )
            , ("ui/id",                       qc prop_ui_id              )
            , ("stretch/start",               qc prop_stretch_start      )
            , ("stretch/dur",                 qc prop_stretch_dur        )
            , ("stretchTo/dur",               qc prop_stretchTo_dur      )
--            , ("during/const",                qc prop_during_const       )
            , ("during/start",                qc prop_during_start       )
            , ("during/end",                  qc prop_during_end         )
            , ("shift/start",                 qc prop_shift_start        )
            , ("shift/end",                   qc prop_shift_end          )
--            , ("backwards",                   qc prop_backwards          )
            , ("atTime/start",                qc prop_atTime_start       )
            , ("atTime/fun",                  qc prop_atTime_fun         )
            ]

instance Arbitrary Any where
  arbitrary = Any <$> arbitrary

instance Arbitrary Time where
  arbitrary = fromRational <$> arbitrary

instance CoArbitrary Time where
  coarbitrary t = coarbitrary (toRational t)

data UnitTime = UnitTime Time deriving Show

instance Arbitrary UnitTime where
  arbitrary = elements [UnitTime i
                     | i <- [0,0.1..1]
                     ]

instance Arbitrary Duration where
  arbitrary = (fromRational . abs) <$> arbitrary

{-
instance (Clock t, Arbitrary (Diff t), CoArbitrary t, Arbitrary t, Arbitrary a) => Arbitrary (Dynamic t a) where
  arbitrary = do
    s <- arbitrary
    d <- arbitrary
    mkDynamic <$> pure s <*> pure (s .+^ d) <*> arbitrary

instance Show t => Show (Dynamic t a) where
  show (Dynamic e f) = "<" ++ show e ++ ">"
-}

instance (Clock t, CoArbitrary t, Arbitrary t, Arbitrary a) => Arbitrary (Active t a) where
  arbitrary = do s <- arbitrary
                 e <- arbitrary
                 beh <- arbitrary
                 return $ mkActive s e beh

instance (CoArbitrary t, Arbitrary a) => Arbitrary (Behavior t a) where
  arbitrary = do f <- arbitrary
                 return $ mkBehavior f

instance (Show t, Show a) => Show (Active t a) where
  show = onActive (\ s e b -> "<<" ++ show (s,e) ++ ":" ++ show b ++ ">>")

instance (Show t, Show a) => Show (Behavior t a) where
  show _ = "<B>"


prop_era_start :: Time -> Time -> Bool
prop_era_start t1 t2 = start (mkEra t1 t2) == t1

prop_era_end :: Time -> Time -> Bool
prop_era_end t1 t2 = end (mkEra t1 t2) == t2

prop_duration :: Time -> Time -> Bool
prop_duration t1 t2 = duration (mkEra t1 t2) == (t2 .-. t1)

prop_shiftDynamic_start :: Duration -> Active Time Bool -> Bool
prop_shiftDynamic_start dur dyn
  = (start . era) (shift dur dyn) == ((start . era) dyn .+^ dur)

prop_shiftDynamic_end :: Duration -> Active Time Bool -> Bool
prop_shiftDynamic_end dur dyn
  = (end . era) (shift dur dyn) == ((end . era) dyn .+^ dur)

prop_shiftDynamic_fun :: Duration -> Active Time Bool -> Time -> Bool
prop_shiftDynamic_fun dur dyn t
  = runActive dyn t == runActive (shift dur dyn) (t .+^ dur)

prop_active_semi_hom :: Active Time Any -> Active Time Any -> Time -> Bool
prop_active_semi_hom a1 a2 t =
  runActive a1 t <> runActive a2 t == runActive (a1 <> a2) t

prop_ui_id :: UnitTime -> Bool
prop_ui_id (UnitTime t) = runActive (ui :: Active Time Time) t == t


prop_stretch_start :: Rational -> Active Time Bool -> Bool
prop_stretch_start r a
  = (start $ activeEra a) == (start $ activeEra (stretch r a))

prop_stretch_dur :: Rational -> Active Time Bool -> Bool
prop_stretch_dur r a
  = (((r *^) . duration) $ activeEra a) == (duration $ activeEra (stretch r a))


{-
prop_stretch_fun :: Rational -> Blind (Active Bool) -> Time -> Bool
prop_stretch_fun r (Blind a) t
  = runActive a t    runActive (stretch r t)
-}

prop_stretchTo_dur :: Positive Duration -> Active Time Bool -> Property
prop_stretchTo_dur (Positive dur) a
  = ((duration $ activeEra a) /= 0)
    ==> (duration $ activeEra (stretchTo dur a)) == dur

{-
prop_during_const :: Active Time Bool -> Active Time Bool -> Property
prop_during_const a1 a2 =
  (isConstant a1 || isConstant a2) ==> (start <$> activeEra (a1 `during` a2)) == (start <$> activeEra a1)
-}

prop_during_start :: Active Time Bool -> Active Time Bool -> Bool
prop_during_start a1 a2 =
  (start $ activeEra (a1 `during` a2)) == (start $ activeEra a2)

prop_during_end :: Active Time Bool -> Active Time Bool -> Bool
prop_during_end a1 a2 =
  (end $ activeEra (a1 `during` a2)) == (end $ activeEra a2)

prop_shift_start :: Duration -> Active Time Bool -> Bool
prop_shift_start d a =
  ((.+^ d) . start $ activeEra a) == (start $ activeEra (shift d a))

prop_shift_end :: Duration -> Active Time Bool -> Bool
prop_shift_end d a =
  ((.+^ d) . end $ activeEra a) == (end $ activeEra (shift d a))

prop_atTime_start :: Time -> Active Time Bool -> Bool
prop_atTime_start t a =
    (start $ activeEra (atTime t a)) == t

prop_atTime_fun :: Time -> Active Time Bool -> Duration -> Bool
prop_atTime_fun t a d =
    runActive (atTime t a) (t .+^ d) == runActive a (s .+^ d)
  where s = start (activeEra a)
