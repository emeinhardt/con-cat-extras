{-# LANGUAGE TypeOperators #-}
-- | Combinators for Cartesian/Cartesian closed categories.

module Control.CCC
 ( -- * Cartesian categories
   dup
 , const2
   -- * Cartesian closed categories
 , const2'
 , dupAp
 , (%)
 , o
 , o'
 , sc
 , sc'
 , sub
 , sub'
 -- , flip
 -- , flip'
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

-- import Data.Void (Void)
-- import Data.Coerce (Coercible, coerce)
-- import Data.Type.Coercion (Coercion (Coercion), coerceWith)
-- import Data.Type.Equality
--   ( (:~:)(Refl)
--   , castWith
--   -- , apply
--   , inner
--   , outer)
-- import Data.Kind (Type)
-- import Data.Proxy
--   ( Proxy(Proxy)
--   -- , asProxyTypeOf
--   )
-- import GHC.Base (Constraint)
-- import GHC.Generics (Generic)
-- import Data.Constraint.Trivial
--   ( -- Unconstrained0
--     Unconstrained
--   , Unconstrained2
--   -- , Unconstrained3
--   )
-- import Data.Tagged (Tagged(Tagged))

-- import Data.Functor.Const ( Const(Const, getConst) )
-- import Data.Functor.Identity
--   ( Identity(Identity)
--   , runIdentity
--   )

import Control.Category.Constrained
  ( Category ( Object
             , id
             , (.)
             )
  , Cartesian ( PairObjects
              , UnitObject
              , swap
              , attachUnit
              , detachUnit
              , regroup
              , regroup'
              )
  , ObjectPair
  , Curry ( MorphObjects
          , uncurry
          , curry
          , apply
          )
  , ObjectMorphism
  , type (+)
  , CoCartesian ( SumObjects
                , ZeroObject
                , coSwap
                , attachZero
                , detachZero
                , coRegroup
                , coRegroup'
                , maybeAsSum
                , maybeFromSum
                , boolAsSum
                , boolFromSum
                )
  , ObjectSum
  , HasAgent ( AgentVal
             , alg
             , ($~)
             )
  , CatTagged
  )
import Control.Arrow.Constrained
  ( Morphism ( (***)
             , first
             , second
             )
  , PreArrow ( (&&&)    -- (△)
             , fst      -- exl
             , snd      -- exr
             , terminal -- it
             )
  , WellPointed ( PointObject
                , globalElement -- unitArrow
                , unit
                , const         -- const
                )
  , ObjectPoint
  , MorphChoice ( (+++)
                , left
                , right
                )
  , PreArrChoice ( (|||) -- (▽)
                 , initial
                 , coFst -- inl
                 , coSnd -- inr
                 )
  , SPDistribute ( distribute   -- distl
                 , unDistribute -- distr
                 , boolAsSwitch
                 , boolFromSwitch
                 )
  , (>>>)
  , (<<<)
  , choose
  , ifThenElse
  )





-- -- This can help type inference sometimes. See the 'Curry' instance for
-- -- 'FreeBCC' for an example that I haven't figured out how to get GHC to
-- -- typecheck without this.
-- class    Object k a ⇒ Object' k a
-- instance Object k a ⇒ Object' k a



-- Some combinators for Cartesian/Cartesian closed categories

-- | The diagonal morphism.
dup ∷ ∀ k a.
    ( PreArrow k
    , ObjectPair k a a
    )
    -- ( PreArrow k
    -- -- , ObjectPair k a a
    -- , PairObjects k a a
    -- , Object k a
    -- , Object k (a,a)
    -- )
    ⇒ a `k` (a,a)
dup = id &&& id

-- | The uncurried /K/ combinator.
const2 ∷ ∀ k a b u.
       ( PreArrow k
       , u ~ UnitObject k
       , ObjectPair k a b
       , ObjectPair k a u
       )
       -- ( PreArrow k
       -- , u ~ UnitObject k
       -- -- , ObjectPair k a b
       -- , PairObjects k a b
       -- , Object k a
       -- , Object k b
       -- , Object k (a,b)
       -- -- , ObjectPair k a u
       -- , PairObjects k a u
       -- , Object k u
       -- , Object k (a,u)
       -- )
       ⇒ (a,b) `k` a
const2 = detachUnit
       . (id *** terminal)

-- | The curried /K/ combinator.
const2' ∷ ∀ k a b u.
        ( PreArrow k
        , Curry k
        , u ~ UnitObject k
        , ObjectPair k a b
        , ObjectPair k a u
        , ObjectMorphism k b a
        )
        -- ( PreArrow k
        -- , Curry k
        -- , u ~ UnitObject k
        -- -- , ObjectPair k a b
        -- , PairObjects k a b
        -- , Object k a
        -- , Object k b
        -- , Object k (a,b)
        -- -- , ObjectPair k a u
        -- , PairObjects k a u
        -- , Object k u
        -- , Object k (a,u)
        -- -- , ObjectMorphism k b a
        -- , MorphObjects k b a
        -- , Object k (k b a)
        -- )
        ⇒  a
       `k` (b `k` a)
const2' = curry const2


type DupAp k a b =
  ( PreArrow k
  , Curry k
  , ObjectPair k a a
  , PairObjects k a a
  , Object k (a,a)
  , ObjectPair k a b
  , ObjectPair k b a
  , ObjectPair k (k a b) a
  , ObjectPair k b (k a b, a)
  , ObjectMorphism k a b
  , ObjectMorphism k a (a,b)
  )


-- | Map a morphism to a variant that also produces a copy of its input.
dupAp ∷ ∀ k a b.
      ( DupAp k a b )
      -- ( PreArrow k
      -- , Curry k
      -- , ObjectPair k a a
      -- , PairObjects k a a
      -- , Object k (a,a)
      -- , ObjectPair k a b
      -- , ObjectPair k b a
      -- , ObjectPair k (k a b) a
      -- , ObjectPair k b (k a b, a)
      -- , ObjectMorphism k a b
      -- , ObjectMorphism k a (a,b)
      -- )
      -- ( PreArrow k
      -- , Curry k
      -- -- , ObjectPair k a a
      -- -- , PairObjects k a a
      -- , Object k a
      -- -- , Object k (a,a)
      -- -- , ObjectPair k a b
      -- , PairObjects k a b
      -- , Object k b
      -- , Object k (a,b)
      -- -- , ObjectPair k b a
      -- , PairObjects k b a
      -- , Object k (b,a)
      -- -- , ObjectPair k (k a b) a
      -- , PairObjects k (k a b) a
      -- , Object k (k a b)
      -- -- , ObjectPair k b (k a b, a)
      -- , PairObjects k b (k a b, a)
      -- , Object k (k a b, a)
      -- , Object k (b, (k a b, a))
      -- -- , ObjectMorphism k a b
      -- , MorphObjects k a b
      -- -- , ObjectMorphism k a (a,b)
      -- , MorphObjects k a (a,b)
      -- , Object k (k a (a, b))
      -- )
      ⇒  (a `k` b)
     `k` (a `k` (a,b))
dupAp = curry
      $ swap
      . second snd
      . (apply &&& id)


-- | Infix operator for 'apply'
(%) ∷ ∀ k a b.
    ( Curry k
    -- , ObjectPair k (k a b) a
    , PairObjects k (k a b) a
    , Object k (k a b)
    , Object k a
    , Object k (k a b, a)
    -- , ObjectMorphism k a b )
    , MorphObjects k a b
    , Object k b
    )
    ⇒ (a `k` b, a)
   `k` b
(%) = apply


-- | Constraints sufficient for internal composition to be defined.
type InternalComp' k a b c =
  ( Morphism k
  , Curry k
  , ObjectPair k (k a b) a
  , ObjectPair k (k b c) b
  , ObjectPair k (k b c) (k a b)
  , ObjectPair k (k b c) (k a b, a)
  , ObjectPair k (k b c, k a b) a
  , ObjectMorphism k a b
  , ObjectMorphism k b c
  , ObjectMorphism k a c
  , ObjectMorphism k (k b c, k a b) (k a c)
  )

type InternalComp k a b c =
  ( Morphism k, Curry k
  -- , ObjectPair k (k a b) a
  , PairObjects k (k a b) a
  , Object k (k a b)
  , Object k a
  , Object k b
  -- , ObjectPair k (k b c) b
  , PairObjects k (k b c) b
  , Object k (k b c)
  , Object k (k b c, b)
  -- , ObjectPair k (k b c) (k a b)
  , PairObjects k (k b c) (k a b)
  -- , ObjectPair k (k b c) (k a b, a)
  , PairObjects k (k b c) (k a b, a)
  , Object k (k a b, a)
  , Object k (k b c, (k a b, a))
  -- , ObjectPair k (k b c, k a b) a
  , PairObjects k (k b c, k a b) a
  , Object k ((k b c, k a b), a)
  -- , ObjectMorphism k a b
  , MorphObjects k a b
  -- , ObjectMorphism k b c
  , MorphObjects k b c
  -- , ObjectMorphism k a c
  , MorphObjects k a c
  , Object k c
  -- , ObjectMorphism k (k b c, k a b) (k a c)
  , MorphObjects k (k b c, k a b) (k a c)
  , Object k (k a c)
  , Object k (k b c, k a b)
  )

-- | Uncurried internal composition.
o ∷ ∀ k a b c.
  ( InternalComp' k a b c )
  -- ( Morphism k, Curry k
  -- , ObjectPair k (k a b) a
  -- , ObjectPair k (k b c) b
  -- , ObjectPair k (k b c) (k a b)
  -- , ObjectPair k (k b c) (k a b, a)
  -- , ObjectPair k (k b c, k a b) a
  -- , ObjectMorphism k a b
  -- , ObjectMorphism k b c
  -- , ObjectMorphism k a c
  -- , ObjectMorphism k (k b c, k a b) (k a c)
  -- )
  -- ( Morphism k
  -- , Curry k
  -- , PairObjects k (k a b) a
  -- , Object k (k a b)
  -- , Object k a
  -- , Object k b
  -- , PairObjects k (k b c) b
  -- , Object k (k b c)
  -- , Object k (k b c, b)
  -- , PairObjects k (k b c) (k a b)
  -- , PairObjects k (k b c) (k a b, a)
  -- , Object k (k a b, a)
  -- , Object k (k b c, (k a b, a))
  -- , PairObjects k (k b c, k a b) a
  -- , Object k ((k b c, k a b), a)
  -- , MorphObjects k a b
  -- , MorphObjects k b c
  -- , MorphObjects k a c
  -- , Object k c
  -- , Object k (k a c)
  -- , Object k (k b c, k a b)
  -- )
  ⇒  (b `k` c, a `k` b)
 `k` (a `k` c)
o = curry
  $ apply
  . (id *** apply)
  . regroup'

-- | Curried internal composition.
o' ∷ ∀ k a b c.
   ( InternalComp' k a b c
   , ObjectMorphism k (k a b) (k a c)
   )
   -- ( Morphism k
   -- , Curry k
   -- , PairObjects k (k a b) a
   -- , Object k (k a b)
   -- , Object k a
   -- , Object k b
   -- , PairObjects k (k b c) b
   -- , Object k (k b c)
   -- , Object k (k b c, b)
   -- , PairObjects k (k b c) (k a b)
   -- , PairObjects k (k b c) (k a b, a)
   -- , Object k (k a b, a)
   -- , Object k (k b c, (k a b, a))
   -- , PairObjects k (k b c, k a b) a
   -- , Object k ((k b c, k a b), a)
   -- , MorphObjects k a b
   -- , MorphObjects k b c
   -- , MorphObjects k a c
   -- , Object k c
   -- , Object k (k a c)
   -- , Object k (k b c, k a b)
   -- , MorphObjects k (k a b) (k a c)
   -- , Object k (k (k a b) (k a c))
   -- )
   ⇒  (b `k` c)
  `k` ((a `k` b) `k` (a `k` c))
o' = curry o

-- | Left-to-right (uncurried) composition ("semicolon").
sc ∷ ∀ k a b c.
   ( InternalComp k a b c
   , ObjectMorphism k (k b c, k a b) (k a c)
   , ObjectPair k (k a b) (k b c)
   )
   -- ( Morphism k, Curry k
   -- , ObjectPair k (k a b) a
   -- , ObjectPair k (k b c) b
   -- , ObjectPair k (k b c) (k a b)
   -- , ObjectPair k (k b c) (k a b, a)
   -- , ObjectPair k (k b c, k a b) a
   -- , ObjectMorphism k a b
   -- , ObjectMorphism k b c
   -- , ObjectMorphism k a c
   -- , ObjectMorphism k (k b c, k a b) (k a c)
   -- , Object k (k a b, k b c)
   -- , PairObjects k (k a b) (k b c)
   -- )
  -- ( Morphism k
  -- , Curry k
  -- , PairObjects k (k a b) a
  -- , Object k (k a b)
  -- , Object k a
  -- , Object k b
  -- , PairObjects k (k b c) b
  -- , Object k (k b c)
  -- , Object k (k b c, b)
  -- , PairObjects k (k b c) (k a b)
  -- , PairObjects k (k b c) (k a b, a)
  -- , Object k (k a b, a)
  -- , Object k (k b c, (k a b, a))
  -- , PairObjects k (k b c, k a b) a
  -- , Object k ((k b c, k a b), a)
  -- , MorphObjects k a b
  -- , MorphObjects k b c
  -- , MorphObjects k a c
  -- , Object k c
  -- , Object k (k a c)
  -- , Object k (k b c, k a b)
  -- , Object k (k a b, k b c)
  -- , PairObjects k (k a b) (k b c)
  -- )
   ⇒  (a `k` b, b `k` c)
  `k` (a `k` c)
sc = o . swap

-- | Left-to-right (curried) composition ("semicolon").
sc' ∷ ∀ k a b c.
   ( InternalComp k a b c
   , ObjectPair k (k a b) (k b c)
   , ObjectMorphism k (k b c) (k a c)
   , Object k (k (k b c, k a b) (k a c))
   )
   -- ( Morphism k, Curry k
   -- , PairObjects k (k a b) a
   -- , Object k (k a b)
   -- , Object k a
   -- , Object k b
   -- , PairObjects k (k b c) b
   -- , Object k (k b c)
   -- , Object k (k b c, b)
   -- , PairObjects k (k b c) (k a b)
   -- , PairObjects k (k b c) (k a b, a)
   -- , Object k (k a b, a)
   -- , Object k (k b c, (k a b, a))
   -- , PairObjects k (k b c, k a b) a
   -- , Object k ((k b c, k a b), a)
   -- , MorphObjects k a b
   -- , MorphObjects k b c
   -- , MorphObjects k a c
   -- , Object k c
   -- , Object k (k a c)
   -- , Object k (k b c, k a b)
   -- , Object k (k a b, k b c)
   -- , PairObjects k (k a b) (k b c)
   -- , MorphObjects k (b `k` c) (a `k` c)
   -- , Object k ((b `k` c) `k` (a `k` c))
   -- )
   ⇒ (a `k` b)
  `k` ((b `k` c) `k` (a `k` c))
sc' = curry sc

-- -- | Uncurried internal blackbird combinator, aka (when curried) @.:@ or @.*@ in
-- -- @Hask@. Synonym for internal composition 'o'.
-- bb ∷ ∀ k a b c d.
--    ( InternalComp k (a,b) c d )
--    ⇒ (c `k` d, (a,b) `k` c)
--   `k` ((a,b) `k` d)
-- bb = o

-- -- | Curried internal blackbird combinator, aka @.:@ or @.*@ in @Hask@.
-- -- Synonym for curried internal composition 'o''.
-- bb' ∷ ∀ k a b c d.
--     ( InternalComp k (a,b) c d
--     , MorphObjects k (k (a, b) c) (k (a, b) d)
--     , Object k (k (k (a, b) c) (k (a, b) d))
--     )
--     ⇒ (c `k` d)
--    `k` (((a,b) `k` c) `k` ((a,b) `k` d))
-- bb' = o'



-- TODO @sub@ or @sub'@ should be equivalent to some use of <*> from
-- Control.Functor.Constrained.

-- | The uncurried /S/ combinator, aka (when curried) @<*>@ in @Hask@.
sub ∷ ∀ k a b c.
    ( InternalComp' k a (a,b) c
    , DupAp k a b
    , ObjectPair k (k (a, b) c) (k a b)
    )
    -- ( PreArrow k
    -- , Curry k
    -- , PairObjects k (k a b) a
    -- , Object k (k a b)
    -- , Object k a
    -- , Object k b
    -- , Object k (k a b, a)
    -- , MorphObjects k a b
    -- , MorphObjects k a c
    -- , Object k c
    -- , Object k (k a c)
    -- , PairObjects k (k a (a, b)) a
    -- , Object k (k a (a, b))
    -- , Object k (a, b)
    -- , PairObjects k (k (a, b) c) (a, b)
    -- , Object k (k (a, b) c)
    -- , Object k (k (a, b) c, (a, b))
    -- , PairObjects k (k (a, b) c) (k a (a, b))
    -- , PairObjects k (k (a, b) c) (k a (a, b), a)
    -- , Object k (k a (a, b), a)
    -- , Object k (k (a, b) c, (k a (a, b), a))
    -- , PairObjects k (k (a, b) c, k a (a, b)) a
    -- , Object k ((k (a, b) c, k a (a, b)), a)
    -- , MorphObjects k a (a, b)
    -- , MorphObjects k (a, b) c
    -- , Object k (k (a, b) c, k a (a, b))
    -- , PairObjects k b a
    -- , Object k (b,a)
    -- , PairObjects k a b
    -- , PairObjects k b (k a b, a)
    -- , PairObjects k (k (a,b) c) (k a b)
    -- , Object k (k (a, b) c, k a b)
    -- , Object k (b, (k a b, a))
    -- )
    ⇒ ((a,b) `k` c, a `k` b)
   `k` (a `k` c)
sub = o . second dupAp

-- | The curried /S/ combinator, aka @<*>@ in @Hask@.
sub' ∷ ∀ k a b c.
     ( InternalComp' k a (a,b) c
     , DupAp k a b
     , ObjectPair k (k (a, b) c) (k a b)
     , ObjectMorphism k (k a b) (k a c)
     )
     -- ( PreArrow k
     -- , Curry k
     -- , Object k (k (a, b) c)
     -- , Object k (k a c)
     -- , Object k a
     -- , MorphObjects k a c
     -- , Object k c
     -- , PairObjects k (k a (a, b)) a
     -- , Object k (k a (a, b))
     -- , Object k (a, b)
     -- , PairObjects k (k (a, b) c) (a, b)
     -- , Object k (k (a, b) c, (a, b))
     -- , PairObjects k (k (a, b) c) (k a (a, b))
     -- , PairObjects k (k (a, b) c) (k a (a, b), a)
     -- , Object k (k a (a, b), a)
     -- , Object k (k (a, b) c, (k a (a, b), a))
     -- , PairObjects k (k (a, b) c, k a (a, b)) a
     -- , Object k ((k (a, b) c, k a (a, b)), a)
     -- , MorphObjects k a (a, b)
     -- , MorphObjects k (a, b) c
     -- , Object k (k (a, b) c, k a (a, b))
     -- , MorphObjects k a b
     -- , PairObjects k b a
     -- , Object k (b,a)
     -- , PairObjects k a b
     -- , PairObjects k (k a b) a
     -- , PairObjects k b (k a b, a)
     -- , PairObjects k (k (a,b) c) (k a b)
     -- , MorphObjects k (k a b) (k a c)
     -- , Object k (k (a, b) c, k a b)
     -- , Object k (k a b)
     -- , Object k (k (k a b) (k a c))
     -- , Object k (k a b, a)
     -- , Object k (b, (k a b, a))
     -- , Object k b
     -- )
     ⇒  ((a, b) `k` c)
    `k` ((a `k` b) `k` (a `k` c))
sub' = curry sub


flip ∷ ∀ k a b c.
     ( Curry k
     -- ,
     )
     ⇒  ((a,b) `k` c)
    `k` ((b,a) `k` c)
flip = undefined
-- flip = sc' swap  -- error: "Could not deduce k ~ (->)"
-- flip = sc' _  -- error: "Could not deduce k ~ (->)"
--               -- also: "Found hole: _ ∷ k (b, a) (a, b)"
-- flip = (curry ((curry ((apply . (id *** apply)) . regroup')) . swap)) swap

-- o = curry ((apply . (id *** apply)) . regroup')
-- sc = o . swap
-- sc' = curry sc
-- flip = sc'                swap
--      = (curry sc)         swap
--      = (curry (o . swap)) swap
--      = (curry (o                                             . swap)) swap
--      = (curry ((curry ((apply . (id *** apply)) . regroup')) . swap)) swap

-- f ∷ x → y
-- swap_ ∷ z → x
-- sc'_  ∷ (z → x) → (x → y) → (z → y)
-- .: sc'_

flip' ∷ ∀ k a b c.
      ( Cartesian k
      , Curry k
      )
      ⇒  (a `k` (b `k` c))
     `k` (b `k` (a `k` c))
flip' = undefined
-- flip' = curry . flip . uncurry

-- flip_ ∷ ((a,b) → c) → ((b,a) → c)
-- -- flip_ f = f . swap
-- -- flip_ = (. swap)
-- flip_ = sc' swap

