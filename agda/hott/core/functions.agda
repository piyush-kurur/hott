{-# OPTIONS --without-K #-}

module hott.core.functions where

open import Level
open import hott.core.universe

-- Composition of functions.
_∘_ : ∀ {ℓ₀ ℓ₁ ℓ₂ : Level} → {A : Type ℓ₀} {B : Type ℓ₁} {C : Type ℓ₂}
    → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

-- We want compostion to have very high precedence.
infixr 100 _∘_

-- The constant function.
constant : ∀ {ℓ₀ ℓ₁}{A : Type ℓ₀}{B : Type ℓ₁} → A → B → A
constant a b = a

-- Alternate syntax for dependent function type.
∏ : ∀{ℓ₀ ℓ₁}(A : Type ℓ₀)(B : A → Type ℓ₁) → Type (ℓ₀ ⊔ ℓ₁)
∏ A B = (a : A) → B(a)
