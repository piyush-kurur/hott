{-# OPTIONS --without-K #-}

module hott.core.functions where

open import hott.core.universe
open import hott.core.nat
open import hott.core.equality

-- Composition of functions.
_∘_ : ∀ {ℓ₀ ℓ₁ ℓ₂ : Level} → {A : Type ℓ₀} {B : Type ℓ₁} {C : Type ℓ₂}
    → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

-- The identity function.
id : ∀{ℓ} {A : Type ℓ} → A → A
id x = x

-- The interated fucntion
iterate : ∀{ℓ} {A : Type ℓ} → (A → A) → ℕ → A → A
iterate _ zero     = id
iterate f (succ n) = f ∘ iterate f n


-- We want compostion to have very high precedence.
infixr 100 _∘_

-- The constant function.
constant : ∀ {ℓ₀ ℓ₁}{A : Type ℓ₀}{B : Type ℓ₁} → A → B → A
constant a b = a

-- Alternate syntax for dependent function type.
Π : ∀{ℓ₀ ℓ₁}{A : Type ℓ₀}(B : A → Type ℓ₁) → Type (ℓ₀ ⊔ ℓ₁)
Π {_}{_}{A} B = (a : A) → B(a)

-- One should use f ~ g to mean that f and g are homotopic.
_~_   : ∀{ℓ₀ ℓ₁}{A : Type ℓ₀}{B : Type ℓ₁} (f g : A → B) → Type (ℓ₁ ⊔ ℓ₀)
f ~ g = Π  λ x → f x ≡ g x

infixr 1   _~_
