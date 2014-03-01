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

_+_   : ℕ → ℕ → ℕ
zero    + y = y
succ x  + y = succ (x + y)

-- 0 is the right identity of addition.
x+0≡x : ∀(x : ℕ) → x + 0 ≡ x
x+0≡x  zero             = refl
x+0≡x (succ n)
  = begin succ n + zero ≡ succ (n + zero) by refl
                        ≡ succ n          by ap succ (x+0≡x (n))
  ∎

-- Alternate from of 0 being right identity.
x≡x+0 : ∀(x : ℕ) → x ≡ x + 0
x≡x+0 n = x+0≡x n ⁻¹

0+x≡x : ∀ (x : ℕ) → 0 + x ≡ x
0+x≡x n = refl

x≡0+x : ∀ (x : ℕ) → x ≡ 0 + x
x≡0+x n = refl

x+y≡y+x : ∀ (x y : ℕ) → x + y ≡ y + x
x+y≡y+x zero    n        = x≡x+0 (n)
x+y≡y+x n       zero     = x+0≡x (n)
x+y≡y+x (succ m) (succ n)
  = begin succ m + succ n
          ≡ succ (m + succ n)   by definition
          ≡ succ (succ n + m)   by ap succ (x+y≡y+x m (succ n))
          ≡ succ (succ (n + m)) by definition
          ≡ succ (succ (m + n)) by ap succ (ap succ (x+y≡y+x n m))
          ≡ succ (succ m + n)   by ap succ definition
          ≡ succ (n + succ m)   by ap succ (x+y≡y+x (succ m) n)
          ≡ succ n + succ m     by definition
  ∎
