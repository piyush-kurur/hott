{-# OPTIONS --without-K #-}

-- Some basic theorms about natural numbers.
module hott.types.nat.theorems where

open import hott.core
open import hott.functions
open import hott.types.nat

-- 0 is the right identity of addition.
x+0≡x : ∀(x : ℕ) → x + 0 ≡ x
x+0≡x  0                = begin 0 + 0 ≡ 0 by definition ∎
x+0≡x (succ n)
  = begin succ n + 0 ≡ succ (n + 0) by definition
                     ≡ succ n       by ap succ (x+0≡x (n))
  ∎

-- Alternate from of 0 being right identity.
x≡x+0 : ∀(x : ℕ) → x ≡ x + 0
x≡x+0 n = x+0≡x n ⁻¹

-- This is really refl but it is better to use these when proving
-- properties about ℕ. One does not have to remember which is
-- definitional equality and which is not.
0+x≡x : ∀ (x : ℕ) → 0 + x ≡ x
0+x≡x n = begin 0 + n ≡ n by definition ∎

-- This is really refl but it is better to use these when proving
-- properties about ℕ. One does not have to remember which is
-- definitional equality and which is not.
x≡0+x : ∀ (x : ℕ) → x ≡ 0 + x
x≡0+x n = begin n ≡ 0 + n by definition ∎

-- Commutativity of addition.
x+y≡y+x : ∀ (x y : ℕ) → x + y ≡ y + x
x+y≡y+x 0 n
        = begin 0 + n ≡ n     by  definition
                      ≡ n + 0 by  x≡x+0 (n)
          ∎
x+y≡y+x n 0
        = begin n + 0 ≡ n      by x+0≡x (n)
                      ≡ 0 + n  by definition
          ∎
x+y≡y+x (succ m) (succ n)
  = begin succ m + succ n
          ≡ succ (m + succ n)   by definition
          ≡ succ (succ n + m)   by applying succ on x+y≡y+x m (succ n)
          ≡ succ (succ (n + m)) by definition
          ≡ succ (succ (m + n)) by applying succ ∘ succ on (x+y≡y+x n m)
          ≡ succ (succ m + n)   by applying succ on definition
          ≡ succ (n + succ m)   by applying succ on x+y≡y+x (succ m) n
          ≡ succ n + succ m     by definition
  ∎
-- Associativity of +
x+[y+z]≡[x+y]+z : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
x+[y+z]≡[x+y]+z zero      y z
                = begin 0 + (y + z)
                        ≡ y + z        by definition
                        ≡ (0 + y) + z  by definition
                ∎
x+[y+z]≡[x+y]+z (succ x)  y z
  = begin succ x + (y + z)
          ≡ succ (x + (y  + z)) by definition
          ≡ succ ((x + y) + z) by applying succ on x+[y+z]≡[x+y]+z x y z
          ≡ succ (x + y)  + z  by definition
          ≡ (succ x + y)  + z  by definition
  ∎
