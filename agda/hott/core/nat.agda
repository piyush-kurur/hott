{-# OPTIONS --without-K #-}

module hott.core.nat where

open import hott.core.universe
open import hott.core.equality

data ℕ : Type₀ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC  succ #-}

-- Addition.
_+_   : ℕ → ℕ → ℕ
0       + y = y
succ x  + y = succ (x + y)

-- Multiplication
_*_   : ℕ → ℕ → ℕ
zero   * y = zero
succ x * y = y + (x * y)
