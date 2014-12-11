{-# OPTIONS --without-K #-}

-- This module implements the dependent Σ-type.
module hott.core.sigma where

open import hott.core.universe
open import hott.core.functions

record Σ {ℓ₀ ℓ₁}
         {A : Type ℓ₀}
         (B : A → Type ℓ₁) : Type (ℓ₀ ⊔ ℓ₁) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁


-- The product type is just the non-dependent Σ-type.
_×_ : ∀{ℓ₀ ℓ₁} (A : Type ℓ₀)
       (B : Type ℓ₁) →  Type (ℓ₀ ⊔ ℓ₁)
A × B = Σ λ (_ : A) → B

-- Since the , constructor is infixr, we can write (a , (b , c)) as
-- just (a , b , c). The convention that we follow for tuples is that
-- of a list. We assign the paring function the least precedence
-- because we would like to write all other stuff inside the tuple
-- naturally e.g. (p ≡ q , q ≡ r) etc. We ensure that no other
-- operator has 0 precedence.
infixr 0 _,_
infixr 0 _×_

-- The projection to the first component.
fst : ∀{ℓ₀ ℓ₁} {A : Type ℓ₀} {B : A → Type ℓ₁}
    → Σ B → A
fst = Σ.proj₁

-- The projection to the second component.
snd : ∀{ℓ₀ ℓ₁} {A : Type ℓ₀} {B : A → Type ℓ₁}
    → (σ : Σ B) →  B (fst σ)
snd = Σ.proj₂
