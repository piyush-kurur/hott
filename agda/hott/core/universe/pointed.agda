{-# OPTIONS --without-K #-}

--
-- A pointed type is a type together with a point in it. This module
-- defines the universe of pointed types which we denote by Type● ℓ.
-- Like the type universe Type ℓ, it is an inhabitant of Type (ℓ + 1).
--
-- Editing notes:
--     ● : \ci followed by selecting the 1 option
--     ∙ : \.

module hott.core.universe.pointed where

open import hott.core.pair
open import hott.core.functions
open import hott.core.universe

-- The pointed type is nothing but a dependent pair where the first
-- component is itself a type.
Type● : (ℓ : Level) → Type (lsuc ℓ)
Type● ℓ = Σ id

-- The level 0 of pointed types.
Type∙  = Type● lzero

Type∙₀ = Type● lzero
Type∙₁ = Type● lone
Type∙₂ = Type● ltwo
Type∙₃ = Type● lthree
Type∙₄ = Type● lfour
Type∙₅ = Type● lfive
Type∙₆ = Type● lsix
Type∙₇ = Type● lseven
Type∙₈ = Type● leight
Type∙₉ = Type● lnine

--
-- Topologically pointed types are spaces with a distinguished point
-- called the base. We give function to recover the space and the base
-- point from it. These are essentially the projections but we give
-- better names for it.
--

space : ∀{ℓ} → Type● ℓ → Type ℓ
space = fst

base : ∀{ℓ} → (A● : Type● ℓ) → space A●
base = snd
