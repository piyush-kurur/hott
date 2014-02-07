{-# OPTIONS --without-K #-}

-- The universe of all types
module hott.core.universe where

open import Level

-- We give an new name for Set
Type : (ℓ : Level) → Set (suc ℓ)
Type ℓ = Set ℓ

private
  one   = suc zero
  two   = suc one
  three = suc two
  four  = suc three
  five  = suc four
  six   = suc five
  seven = suc six
  eight = suc seven
  nine  = suc eight

Type₀ = Type zero
Type₁ = Type one
Type₂ = Type two
Type₃ = Type three
Type₄ = Type four
Type₅ = Type five
Type₆ = Type six
Type₇ = Type seven
Type₈ = Type eight
Type₉ = Type nine
