{-# OPTIONS --without-K #-}

-- This module implements the dependent pair type Σ.
module hott.core.pair where

open import hott.core.universe
open import hott.core.functions

data Σ {ℓ₀ ℓ₁}
       {A : Type ℓ₀}
       (B : A → Type ℓ₁) : Type (ℓ₀ ⊔ ℓ₁) where
  _,_ : (a : A) → (b : B a) → Σ B


-- Non-dependent Σ type.
_×_ : ∀{ℓ₀ ℓ₁} (A : Type ℓ₀)
       (B : Type ℓ₁) →  Type (ℓ₀ ⊔ ℓ₁)
A × B = Σ (λ (x : A) → B)

-- The , constructor is infixr means we can write (a , (b , c)) as
-- just (a , b , c). The convention that we follow for tuples is that
-- of a list. We assign the paring function the least precedence
-- because we would like to write all other stuf inside the tuple
-- naturally. For example, to give a proof of and of two stuff we can
-- say (p ≡ q , q ≡ r) etc. We ensure that no other operator has 0
-- precedence.
infixr 0 _,_
infixr 0 _×_

-- The projection to the first component.
fst : ∀{ℓ₀ ℓ₁} {A : Type ℓ₀} {B : A → Type ℓ₁}
    → Σ B → A
fst (a , b) = a

-- The projection to the second component.
snd : ∀{ℓ₀ ℓ₁} {A : Type ℓ₀} {B : A → Type ℓ₁}
    → (σ : Σ B) →  B (fst σ)
snd (a , b) = b
