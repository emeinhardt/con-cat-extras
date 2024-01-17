{-# LANGUAGE TypeOperators #-}
-- | Provides a @Functor@ typeclass like in @Control.Functor.Constrained@ but
-- without the functional dependencies.

module Control.Functor.Constrained.Extras
  ( Functor'
  , fmap'
  , NatTrans
  , nmap
  ) where

-- import Prelude qualified as P
import Prelude hiding
  ( id
  , (.)
  , fst
  , snd
  , curry
  , uncurry
  , const
  , foldMap
  , flip
  )

-- import Data.Constraint.Trivial
--   ( -- Unconstrained0
--     Unconstrained
--   , Unconstrained2
--   -- , Unconstrained3
--   )

-- import Data.Functor.Const ( Const(Const, getConst) )
-- import Data.Functor.Identity
--   ( Identity(Identity)
--   , runIdentity
--   )

import Control.Category.Constrained
  ( Category ( Object
             -- , id
             -- , (.)
             )
  -- , Cartesian ( PairObjects
  --             , UnitObject
  --             , swap
  --             , attachUnit
  --             , detachUnit
  --             , regroup
  --             , regroup'
  --             )
  -- , ObjectPair
  -- , Curry ( MorphObjects
  --         , uncurry
  --         , curry
  --         , apply
  --         )
  -- , ObjectMorphism
  -- , type (+)
  -- , CoCartesian ( SumObjects
  --               , ZeroObject
  --               , coSwap
  --               , attachZero
  --               , detachZero
  --               , coRegroup
  --               , coRegroup'
  --               , maybeAsSum
  --               , maybeFromSum
  --               , boolAsSum
  --               , boolFromSum
  --               )
  -- , ObjectSum
  -- , HasAgent ( AgentVal
  --            , alg
  --            , ($~)
  --            )
  -- , CatTagged
  )
-- import Control.Arrow.Constrained
--   ( Morphism ( (***)
--              , first
--              , second
--              )
--   , PreArrow ( (&&&)    -- (△)
--              , fst      -- exl
--              , snd      -- exr
--              , terminal -- it
--              )
--   , WellPointed ( PointObject
--                 , globalElement -- unitArrow
--                 , unit
--                 , const         -- const
--                 )
--   , ObjectPoint
--   , MorphChoice ( (+++)
--                 , left
--                 , right
--                 )
--   , PreArrChoice ( (|||) -- (▽)
--                  , initial
--                  , coFst -- inl
--                  , coSnd -- inr
--                  )
--   , SPDistribute ( distribute   -- distl
--                  , unDistribute -- distr
--                  , boolAsSwitch
--                  , boolFromSwitch
--                  )
--   , (>>>)
--   , (<<<)
--   , choose
--   , ifThenElse
--   )


{- | A functor @φ@ from @r@ to @t@
    1. should map every object @a@ of @r@ to an object @φ a@ of @t@.
    2. should map every morphism @a `r` b@ to a morphism @φ a `t` φ b@.

   #1 is taken care of in Haskell by the data constructors of @φ@; #2 is the job of the definition
   of @fmap@ in the @Functor'@ instance for @φ@, and every definition for @fmap@ should ensure the
   following equalities hold:

   @
     fmap (g ∘ f) = fmap g ∘ fmap f
     fmap id = id
   @
  -}
class (Category r, Category t
      ) ⇒ Functor' φ r t where
  fmap' ∷ ∀ a b. (Object r a, Object t (φ a), Object r b, Object t (φ b))
       ⇒ (a `r` b) → (φ a `t` φ b)

instance (Functor φ) ⇒ Functor' φ (->) (->) where
  fmap' = fmap


class (Functor' φ r t, Functor' γ r t, Category r, Category t
      ) ⇒ NatTrans r t φ γ where
  nmap ∷ (∀ a b. (Object r a, Object r b, Object t (φ a), Object t (γ b) )
       ⇒ a `r` b → (φ a `t` γ b))


