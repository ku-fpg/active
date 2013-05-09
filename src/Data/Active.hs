{-# LANGUAGE DeriveFunctor
           , GeneralizedNewtypeDeriving
           , TypeSynonymInstances
           , MultiParamTypeClasses
           , TypeFamilies
           , FlexibleInstances
           , FlexibleContexts
           , ScopedTypeVariables
  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Active
-- Copyright   :  (c) 2011 Brent Yorgey
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
--
-- Inspired by the work of Kevin Matlage and Andy Gill (/Every/
-- /Animation Should Have a Beginning, a Middle, and an End/, Trends
-- in Functional Programming,
-- 2010. <http://ittc.ku.edu/csdl/fpg/node/46>), this module defines a
-- simple abstraction for working with time-varying values.  A value
-- of type @Active a@ is either a constant value of type @a@, or a
-- time-varying value of type @a@ (/i.e./ a function from time to
-- @a@) with specific start and end times.  Since active values
-- have start and end times, they can be aligned, sequenced,
-- stretched, or reversed.
--
-- In a sense, this is sort of like a stripped-down version of
-- functional reactive programming (FRP), without the reactivity.
--
-- The original motivating use for this library is to support making
-- animations with the diagrams framework
-- (<http://projects.haskell.org/diagrams>), but the hope is that it
-- may find more general utility.
--
-- There are two basic ways to create an @Active@ value.  The first is
-- to use 'mkActive' to create one directly, by specifying a start and
-- end time and a function of time.  More indirectly, one can use the
-- 'Applicative' instance together with the unit interval 'ui', which
-- takes on values from the unit interval from time 0 to time 1, or
-- 'interval', which creates an active over an arbitrary interval.
--
-- For example, to create a value of type @Active Double@ which
-- represents one period of a sine wave starting at time 0 and ending
-- at time 1, we could write
--
-- > mkActive 0 1 (\t -> sin (fromTime t * tau))
--
-- or
--
-- > (sin . (*tau)) <$> ui
--
-- 'pure' can also be used to create @Active@ values which are
-- constant and have no start or end time.  For example,
--
-- > mod <$> (floor <$> interval 0 100) <*> pure 7
--
-- cycles repeatedly through the numbers 0-6.
--
-- Note that the \"idiom bracket\" notation supported by the SHE
-- preprocessor (<http://personal.cis.strath.ac.uk/~conor/pub/she/>,
-- <http://hackage.haskell.org/package/she>) can make for somewhat
-- more readable 'Applicative' code.  For example, the above example
-- can be rewritten using SHE as
--
-- > {-# OPTIONS_GHC -F -pgmF she #-}
-- >
-- > ... (| mod (| floor (interval 0 100) |) ~7 |)
--
-- There are many functions for transforming and composing active
-- values; see the documentation below for more details.
--
--
-- With careful handling, this module should be suitable to generating
-- deep embeddings if 'Active' values.
--
-----------------------------------------------------------------------------

module Data.Active where
{-
       ( -- * Representing time

         -- ** Time and duration

         Time, Clock(..)
       , Duration, Waiting(..)

         -- ** Eras

       , Era, mkEra
       , start, end, duration

         -- * Deadlines

       , Deadline(..)

         -- * Dynamic values
       , Dynamic(..), mkDynamic, onDynamic

       , shiftDynamic
       , transitionDeadline

         -- * Active values
         -- $active
       , Active, mkActive, fromDynamic, isConstant, isDynamic

       , onActive, modActive, runActive

       , activeEra, setEra, atTime

       , activeStart, activeEnd

         -- * Combinators

         -- ** Special active values

       , ui, interval

         -- ** Transforming active values

       , stretch, stretchTo, during
       , shift, backwards

       , snapshot

         -- ** Working with values outside the era
       , clamp, clampBefore, clampAfter
       , trim, trimBefore, trimAfter

         -- ** Composing active values

       , after

       , (->>)

       , (|>>), movie

         -- * Deadlines

         , activeDeadline

         -- * Discretization

       , discrete
       , simulate

         -- * Fractionals

       , FractionalOf(..)

       ) where
-}

import Control.Applicative
import Control.Arrow ((&&&))
import Control.Newtype

import Data.Array
import Data.Maybe

import Data.Functor.Apply
import Data.Semigroup hiding (First(..))
import Data.Monoid (First(..))

import Data.VectorSpace hiding ((<.>))
import Data.AffineSpace

------------------------------------------------------------
-- Clock
------------------------------------------------------------
-- | A class that abstracts over time.

class ( AffineSpace t
      , Waiting (Diff t)
      ) => Clock t where

  -- | Convert any value of a 'Real' type (including @Int@, @Integer@,
  --   @Rational@, @Float@, and @Double@) to a 'Time'.
  toTime :: Real a => a -> t
  -- | Convert a 'Time' to a value of any 'Fractional' type (such as
  --   @Rational@, @Float@, or @Double@).
  fromTime :: (FractionalOf t a) => t -> a

  firstTime :: t -> t -> t
  lastTime  :: t -> t -> t

class (FractionalOf w (Scalar w), VectorSpace w) => Waiting w where
  -- | Convert any value of a 'Real' type (including @Int@, @Integer@,
  --   @Rational@, @Float@, and @Double@) to a 'Duration'.
  toDuration :: Real a => a -> w

  -- | Convert a 'Duration' to any other 'Fractional' type (such as
  --   @Rational@, @Float@, or @Double@).
  fromDuration :: (FractionalOf w a) => w -> a

class Fractional a => FractionalOf v a where
        toFractionalOf :: v -> a

class Clock t => Deadline t a where
        -- choose time-now deadline-time (if before / at deadline) (if after deadline)
        choose :: t -> t -> a -> a -> a

------------------------------------------------------------
-- Time
------------------------------------------------------------

-- | An abstract type for representing /points in time/.  Note that
--   literal numeric values may be used as @Time@s, thanks to the the
--   'Num' and 'Fractional' instances.  'toTime' and 'fromTime' are
--   also provided for convenience in converting between @Time@ and
--   other numeric types.
newtype Time = Time { unTime :: Rational }
  deriving ( Eq, Ord, Show, Read, Enum, Num, Fractional, Real, RealFrac )

instance Newtype Time Rational where
  pack   = Time
  unpack = unTime

instance AffineSpace Time where
  type Diff Time = Duration
  (Time t1) .-. (Time t2) = Duration (t1 - t2)
  (Time t) .+^ (Duration d) = Time (t + d)

instance Clock Time where
  toTime = fromRational . toRational
  fromTime = fromRational . unTime
  firstTime = min
  lastTime = max

instance Fractional a => FractionalOf Time a where
  toFractionalOf (Time d) = fromRational d

instance Deadline Time a where
        -- choose tm deadline (if before / at deadline) (if after deadline)
        choose t1 t2 a b = if t1 <= t2 then a else b

-- | An abstract type representing /elapsed time/ between two points
--   in time.  Note that durations can be negative. Literal numeric
--   values may be used as @Duration@s thanks to the 'Num' and
--   'Fractional' instances. 'toDuration' and 'fromDuration' are also
--   provided for convenience in converting between @Duration@s and
--   other numeric types.
newtype Duration = Duration { unDuration :: Rational }
  deriving ( Eq, Ord, Show, Read, Enum, Num, Fractional, Real, RealFrac
           , AdditiveGroup)

instance Newtype Duration Rational where
  pack   = Duration
  unpack = unDuration

instance VectorSpace Duration where
  type Scalar Duration = Rational
  s *^ (Duration d) = Duration (s * d)

instance Waiting Duration where
  toDuration = fromRational . toRational
  fromDuration = toFractionalOf

instance Fractional a => FractionalOf Duration a where
  toFractionalOf (Duration d) = fromRational d

-- | An @Era@ is a concrete span of time, that is, a pair of times
--   representing the start and end of the era. @Era@s form a
--   semigroup: the combination of two @Era@s is the smallest @Era@
--   which contains both.  They do not form a 'Monoid', since there is
--   no @Era@ which acts as the identity with respect to this
--   combining operation.
--
--   @Era@ is abstract. To construct @Era@ values, use 'mkEra'; to
--   deconstruct, use 'start' and 'end'.
newtype Era t = Era (Min t, Max t)
  deriving (Show)

-- AJG: I explicitly implement this to make sure we use min and max,
-- and not compare (which does not reify into a deep embedded structure).
instance Clock t => Semigroup (Era t) where
  Era (Min min1,Max max1) <> Era (Min min2,Max max2)
    = Era (Min (firstTime min1 min2),Max (lastTime max1 max2))

-- | Create an 'Era' by specifying start and end 'Time's.
mkEra :: t -> t -> Era t
mkEra s e = Era (Min s, Max e)

-- | Get the start 'Time' of an 'Era'.
start :: Era t -> t
start (Era (Min t, _)) = t

-- | Get the end 'Time' of an 'Era'.
end :: Era t -> t
end (Era (_, Max t)) = t

-- | Compute the 'Duration' of an 'Era'.
duration :: (Clock t) => Era t -> Diff t
duration = (.-.) <$> end <*> start


------------------------------------------------------------
-- Dynamic
------------------------------------------------------------
{-
-- | A @Dynamic a@ can be thought of as an @a@ value that changes over
--   the course of a particular 'Era'.  It's envisioned that @Dynamic@
--   will be mostly an internal implementation detail and that
--   'Active' will be most commonly used.  But you never know what
--   uses people might find for things.

data Dynamic t a = Dynamic { era        :: Era t
                           , runDynamic :: t -> a
                           }
  deriving (Functor)

-- | 'Dynamic' is an instance of 'Apply' (/i.e./ 'Applicative' without
--   'pure'): a time-varying function is applied to a time-varying
--   value pointwise; the era of the result is the combination of the
--   function and value eras.  Note, however, that 'Dynamic' is /not/
--   an instance of 'Applicative' since there is no way to implement
--   'pure': the era would have to be empty, but there is no such
--   thing as an empty era (that is, 'Era' is not an instance of
--   'Monoid').

instance (Clock t) => Apply (Dynamic t) where
  (Dynamic d1 f1) <.> (Dynamic d2 f2) = Dynamic (d1 <> d2) (f1 <.> f2)

-- | @'Dynamic' a@ is a 'Semigroup' whenever @a@ is: the eras are
--   combined according to their semigroup structure, and the values
--   of type @a@ are combined pointwise.  Note that @'Dynamic' a@ cannot
--   be an instance of 'Monoid' since 'Era' is not.
instance (Clock t, Semigroup a) => Semigroup (Dynamic t a) where
  Dynamic d1 f1 <> Dynamic d2 f2 = Dynamic (d1 <> d2) (f1 <> f2)

-- | Create a 'Dynamic' from a start time, an end time, and a
--   time-varying value.
mkDynamic :: t -> t -> (t -> a) -> Dynamic t a
mkDynamic s e = Dynamic (mkEra s e)

-- | Fold for 'Dynamic'.
onDynamic :: (t -> t -> (t -> a) -> b) -> Dynamic t a -> b
onDynamic f (Dynamic e d) = f (start e) (end e) d

-- | Shift a 'Dynamic' value by a certain duration.
shiftDynamic :: (Clock t) => Diff t -> Dynamic t a -> Dynamic t a
shiftDynamic sh =
  onDynamic $ \s e d ->
    mkDynamic
      (s .+^ sh)
      (e .+^ sh)
      (\t -> d (t .-^ sh))

-- | take the first value until a deadline, then take the second value, inside a Dynamic.
transitionDeadline :: Deadline t a => t -> Dynamic t (a -> a -> a)
transitionDeadline dl = mkDynamic dl dl (\ t -> choose t dl)
-}
------------------------------------------------------------
--  Active
------------------------------------------------------------

-- $active
-- For working with time-varying values, it is convenient to have an
-- 'Applicative' instance: '<*>' lets us apply time-varying
-- functions to time-varying values; 'pure' allows treating constants
-- as time-varying values which do not vary.  However, as explained in
-- its documentation, 'Dynamic' cannot be made an instance of
-- 'Applicative' since there is no way to implement 'pure'.  The
-- problem is that all 'Dynamic' values must have a finite start and
-- end time.  The solution is to adjoin a special constructor for
-- pure/constant values with no start or end time, giving us 'Active'.

-- | There are two types of @Active@ values:
--
--   * An 'Active' can simply be a 'Dynamic', that is, a time-varying
--     value with start and end times.
--
--   * An 'Active' value can also be a constant: a single value,
--     constant across time, with no start and end times.
--
--   The addition of constant values enable 'Monoid' and 'Applicative'
--   instances for 'Active'.

data Active t a = Active   { era       :: Era t
                           , behavior  :: Behavior t a
                           }
  deriving (Functor)

type Transition t a = Active t a       -- proposed name for Active

instance (Clock t) => Apply (Active t) where
  (Active d1 f1) <.> (Active d2 f2) = Active (d1 <> d2) (f1 <.> f2)

instance Newtype (MaybeApply f a) (Either (f a) a) where
  pack   = MaybeApply
  unpack = runMaybeApply

-- | Ideally this would be defined in the @newtype@ package.  If it is
--   ever added we can remove it from here.
over2 :: (Newtype n o, Newtype n' o', Newtype n'' o'')
      => (o -> n) -> (o -> o' -> o'') -> (n -> n' -> n'')
over2 _ f n1 n2 = pack (f (unpack n1) (unpack n2))

-- | Active values over a type with a 'Semigroup' instance are also an
--   instance of 'Semigroup'.  Two active values are combined
--   pointwise; the resulting value is constant iff both inputs are.
instance (Clock t, Semigroup a) => Semigroup (Active t a) where
  Active d1 f1 <> Active d2 f2 = Active (d1 <> d2) (f1 <> f2)

-- | Create a dynamic 'Active' from a start time, an end time, and a
--   time-varying value.
mkActive :: (Clock t) => t -> t -> (Behavior t a) -> Active t a
mkActive s e f = Active (mkEra s e) (clamp (mkEra s e) f)

-- | Fold for 'Active's.  Process an 'Active a', given a function to
--   apply if it is a pure (constant) value, and a function to apply if
--   it is a 'Dynamic'.
onActive :: (t -> t -> Behavior t a -> b) -> Active t a -> b
onActive f (Active e b) = f (start e) (end e) b

-- | Modify an 'Active' value using a case analysis to see whether it
--   is constant or dynamic.
modActive :: (Clock t) => (Behavior t a -> Behavior t b) -> Active t a -> Active t b
modActive f = onActive (\ t1 t2 b -> mkActive t1 t2 (f b))

-- | Interpret an 'Active' value as a function from time.
runActive :: Active t a -> (t -> a)
runActive = onActive (\ _ _ b -> runBehavior b)

-- | Get the value of an @Active a@ at the beginning of its era.
activeStart :: Active t a -> a
activeStart = onActive (\ s _ d -> runBehavior d s)

-- | Get the value of an @Active a@ at the end of its era.
activeEnd :: Active t a -> a
activeEnd = onActive (\ _ e d -> runBehavior d e)

-- | Get the 'Era' of an 'Active' value (or 'Nothing' if it is
--   a constant/pure value).
activeEra :: Active t a -> Era t
activeEra = onActive (\ s e _ -> mkEra s e)

-- | Shift a 'Active' value by a certain duration.
shiftActive :: (Clock t) => Diff t -> Active t a -> Active t a
shiftActive sh =
  onActive $ \s e d ->
    mkActive
      (s .+^ sh)
      (e .+^ sh)
      (modBehavior id (\ f t -> f (t .-^ sh)) d)


------------------------------------------------------------
--  Behavior
------------------------------------------------------------

newtype Behavior t a = Behavior (MaybeApply ((->) t) a)
  deriving (Functor, Apply, Applicative)

instance Newtype (Behavior t a) (MaybeApply ((->) t) a) where
  pack              = Behavior
  unpack (Behavior m) = m

instance (Clock t, Semigroup a) => Semigroup (Behavior t a) where
  (<>) = (over2 Behavior . over2 MaybeApply) combine
   where
    combine (Right m1) (Right m2)
      = Right (m1 <> m2)

    combine (Left f) (Right m)
      = Left (f <> const m)

    combine (Right m) (Left f)
      = Left (const m <> f)

    combine (Left d1) (Left d2)
      = Left (d1 <> d2)

instance (Clock t, Monoid a, Semigroup a) => Monoid (Behavior t a) where
  mempty  = Behavior (MaybeApply (Right mempty))
  mappend = (<>)

-- | Create a dynamic 'Active' from a start time, an end time, and a
--   time-varying value.
mkBehavior :: (t -> a) -> Behavior t a
mkBehavior f = Behavior (MaybeApply (Left f))

-- | Fold for 'Behavior's.  Process an 'Behavior t a', given a function to
--   apply if it is a pure (constant) value, and a function to apply if
--   it is a 'Dynamic'.
onBehavior :: (a -> b) -> ((t -> a) -> b) -> Behavior t a -> b
onBehavior f _ (Behavior (MaybeApply (Right a))) = f a
onBehavior _ f (Behavior (MaybeApply (Left d)))  = f d

-- | Modify an 'Active' value using a case analysis to see whether it
--   is constant or dynamic.
modBehavior :: (Clock t) => (a -> b) -> ((t -> a) -> (t -> b)) -> Behavior t a -> Behavior t b
modBehavior f g = onBehavior (pure . f) (mkBehavior . g)

-- | Interpret an 'Active' value as a function from time.
runBehavior :: Behavior t a -> (t -> a)
runBehavior = onBehavior const ($)

-- | take the first value until a deadline, then take the second value, inside an 'Active'.
behaviorDeadline :: Deadline t a => t -> Behavior t (a -> a -> a)
behaviorDeadline dl = mkBehavior (\ t -> choose t dl)

------------------------------------------------------------
--  Combinators
------------------------------------------------------------

-- | @ui@ represents the /unit interval/, which takes on the value @t@
--   at time @t@, and has as its era @[0,1]@. It is equivalent to
--   @'interval' 0 1@, and can be visualized as follows:
--
--   <<http://www.cis.upenn.edu/~byorgey/hosted/ui.png>>
--
--   On the x-axis is time, and the value that @ui@ takes on is on the
--   y-axis.  The shaded portion represents the era.  Note that the
--   value of @ui@ (as with any active) is still defined outside its
--   era, and this can make a difference when it is combined with
--   other active values with different eras.  Applying a function
--   with 'fmap' affects all values, both inside and outside the era.
--   To manipulate values outside the era specifically, see 'clamp'
--   and 'trim'.
--
--   To alter the /values/ that @ui@ takes on without altering its
--   era, use its 'Functor' and 'Applicative' instances.  For example,
--   @(*2) \<$\> ui@ varies from @0@ to @2@ over the era @[0,1]@.  To
--   alter the era, you can use 'stretch' or 'shift'.
-- TODO: Num=>Clock
ui :: (Clock t, FractionalOf t a) => Active t a
ui = interval (toTime 0) (toTime 1)

-- | @interval a b@ is an active value starting at time @a@, ending at
--   time @b@, and taking the value @t@ at time @t@.
interval :: (Clock t, FractionalOf t a) => t -> t -> Active t a
interval a b = mkActive a b (clamp (mkEra a b) $ mkBehavior fromTime)

-- | @stretch s act@ \"stretches\" the active @act@ so that it takes
--   @s@ times as long (retaining the same start time).
stretch :: (Clock t) => Rational -> Active t a -> Active t a
stretch 0 = onActive $ \ s e d -> mkActive s s $ clamp (mkEra s s) d
stretch str = onActive $ \s e d ->
    mkActive s (s .+^ (fromRational str *^ (e .-. s)))
        (modBehavior id (\ f t -> f (s .+^ ((t .-. s) ^/ fromRational str))) d)

-- | @stretchTo d@ 'stretch'es an 'Active' so it has duration @d@.
--   Has no effect if (1) @d@ is non-positive, or (2) the 'Active'
--   value is constant, or (3) the 'Active' value has zero duration.
-- [AJG: conditions (1) and (3) no longer true: to consider changing]

stretchTo :: (Deadline t a) => Diff t -> Active t a -> Active t a
stretchTo diff = onActive $ \s e d ->
    mkActive s (s .+^ diff)
        (onBehavior pure
                (\ f -> mkBehavior $ \ t ->
                        choose (s .+^ diff) s
                               (f s)      -- avoiding dividing by zero
                               (f (s .+^ (((t .-. s) ^/ (fromDuration diff / fromDuration (e .-. s)))))))
                d)

-- | @a1 \`during\` a2@ 'stretch'es and 'shift's @a1@ so that it has the
--   same era as @a2@.
during :: (Deadline t a) => Active t a -> Active t a -> Active t a
during a1 a2 = (\(d,s) -> stretchTo d . atTime s $ a1)
                 ((duration &&& start) $ activeEra a2)

-- | @shift d act@ shifts the start time of @act@ by duration @d@.
--   Has no effect on constant values.
shift :: (Clock t) => Diff t -> Active t a -> Active t a
shift sh = shiftActive sh

-- | Reverse an active value so the start of its era gets mapped to
--   the end and vice versa.  For example, @backwards 'ui'@ can be
--   visualized as
--
--   <<http://www.cis.upenn.edu/~byorgey/hosted/backwards.png>>
backwards :: (Clock t) => Active t a -> Active t a
backwards = onActive $ \s e d -> mkActive s e
      (modBehavior id (\ f t -> f (s .+^ (e .-. t))) d)

-- | Take a \"snapshot\" of an active value at a particular time,
--   resulting in a constant behavior.
snapshot :: (Clock t) => t -> Active t a -> Behavior t a
snapshot t a = pure (runActive a t)

-- | 'clamp' a behavior to inside an era. All 'Behavior's
-- inside Active *must* be clamped.
clamp :: (Clock t) => Era t -> Behavior t a -> Behavior t a
clamp e = modBehavior id (\ f t -> f (lastTime (start e) (firstTime (end e) t)))

-- | Set the era of an 'Behavior' value.
capture :: (Clock t) => Era t -> Behavior t a -> Active t a
capture er = mkActive (start er) (end er) . clamp er

observe :: (Clock t) => Active t a -> Behavior t a
observe = onActive $ \ s e d -> d

-- | @atTime t a@ is an active value with the same behavior as @a@,
--   shifted so that it starts at time @t@.  If @a@ is constant it is
--   returned unchanged.
atTime :: Clock t => t -> Active t a -> Active t a
atTime t a = (\e -> shift (t .-. start e) a) (activeEra a)

-- | @a1 \`after\` a2@ produces an active that behaves like @a1@ but is
--   shifted to start at the end time of @a2@.  If either @a1@ or @a2@
--   are constant, @a1@ is returned unchanged.
after :: Clock t => Active t a -> Active t a -> Active t a
after a1 a2 = ((`atTime` a1) . end) (activeEra a2)

infixr 5 ->>

-- XXX illustrate

-- | Sequence/overlay two 'Active' values: shift the second to start
--   immediately after the first (using 'after'), then compose them
--   (using '<>').
(->>) :: (Clock t, Semigroup a) => Active t a -> Active t a -> Active t a
a1 ->> a2 = a1 <> (a2 `after` a1)


-- XXX illustrate

-- | \"Splice\" two 'Active' values together: shift the second to
--   start immediately after the first (using 'after'), and produce
--   the value which acts like the first up to the common end/start
--   point, then like the second after that.
(|>>) :: (Deadline t a) => Active t a -> Active t a -> Active t a
a1 |>> a2 = turn <.> a1 <.> a3
  where
       a3 = a2 `after` a1
       dl = end $ activeEra a1
       turn = capture (activeEra a1 <> activeEra a3)
                      (behaviorDeadline dl)

-- XXX implement 'movie' with a balanced fold

-- | Splice together a list of active values using '|>>'.  The list
--   must be nonempty.
--movie :: (Deadline t a) => [Active t a] -> Active t a
--movie = foldr1 (|>>)


------------------------------------------------------------
--  Discretization
------------------------------------------------------------

-- | Create an @Active@ which takes on each value in the given list in
--   turn during the time @[0,1]@, with each value getting an equal
--   amount of time.  In other words, @discrete@ creates a \"slide
--   show\" that starts at time 0 and ends at time 1.  The first
--   element is used prior to time 0, and the last element is used
--   after time 1.
--
--   It is an error to call @discrete@ on the empty list.
discrete :: (Clock t, FractionalOf t Rational) => [a] -> Active t a
discrete [] = error "Data.Active.discrete must be called with a non-empty list."
discrete xs = f <$> ui
  where f (t :: Rational)
            | t <= 0    = arr ! 0
            | t >= 1    = arr ! (n-1)
            | otherwise = arr ! floor (t * fromIntegral n)
        n   = length xs
        arr = listArray (0, n-1) xs

-- | @simulate r act@ simulates the 'Active' value @act@, returning a
--   list of \"snapshots\" taken at regular intervals from the start
--   time to the end time.  The interval used is determined by the
--   rate @r@, which denotes the \"frame rate\", that is, the number
--   of snapshots per unit time.
--
--   If the 'Active' value is constant (and thus has no start or end
--   times), a list of length 1 is returned, containing the constant
--   value.
simulate :: (Clock t, FractionalOf t Rational) => Rational -> Active t a -> [a]
simulate rate =
  onActive (\ s' e' d -> map (runBehavior d . toTime)
                      (let s, e :: Rational
                           s = fromTime $ s'
                           e = fromTime $ e'
                       in  [s, s + 1^/rate .. e]
                      )
           )

