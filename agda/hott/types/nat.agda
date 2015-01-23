{-# OPTIONS --without-K #-}

module hott.types.nat where

open import hott.core.universe
open import hott.core.equality
open import hott.functions

data ℕ : Type₀ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- Addition.
_+_   : ℕ → ℕ → ℕ
0       + y = y
succ x  + y = succ (x + y)

-- Multiplication
_*_   : ℕ → ℕ → ℕ
zero   * y = zero
succ x * y = y + (x * y)

-- The interated fucntion
iterate : ∀{ℓ} {A : Type ℓ} → (A → A) → ℕ → A → A
iterate _ zero     = id
iterate f (succ n) = f ∘ iterate f n
