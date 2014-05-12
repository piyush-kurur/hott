{-# OPTIONS --without-K #-}

--
-- A pointed type a type together with a point in it. This module
-- defines the universe of pointed types which we denote by Type● ℓ.
-- Like the type universe Type ℓ, it is an inhabitant of Type (ℓ + 1).
--

module hott.core.universe.pointed where

open import hott.core.pair
open import hott.core.functions
open import hott.core.universe

-- The pointed type is nothing but a dependent pair where the first
-- component is itself a type.
Type● : (ℓ : Level) → Type (lsuc ℓ)
Type● ℓ = Σ (Type ℓ) id

-- The level 0 of pointed types.
Type∙  = Type● lzero

private
  one   = lsuc lzero
  two   = lsuc one
  three = lsuc two
  four  = lsuc three
  five  = lsuc four
  six   = lsuc five
  seven = lsuc six
  eight = lsuc seven
  nine  = lsuc eight

Type∙₀ = Type● lzero
Type∙₁ = Type● one
Type∙₂ = Type● two
Type∙₃ = Type● three
Type∙₄ = Type● four
Type∙₅ = Type● five
Type∙₆ = Type● six
Type∙₇ = Type● seven
Type∙₈ = Type● eight
Type∙₉ = Type● nine
