{-# OPTIONS --without-K #-}

module hott.types.coproduct where

open import hott.core.universe

data _∐_ {ℓ₀ ℓ₁ : Level}
         (A : Type ℓ₀)
         (B : Type ℓ₁) : Type (ℓ₀ ⊔ ℓ₁)  where

     inl : (a : A) → A ∐ B -- left  introduction
     inr : (b : B) → A ∐ B -- right introduction

-- A more suggestive way of building elements of nested co-product
-- types. For example if we have a : A, b : B and c : C then the
-- expressions, a ∣∙, ∙∣ b ∣∙ and ∙∣ ∙∣ c are elements inl a, inr (inl
-- b) and inr (inr c) of A ∐ B ∐ C respectively.

_∣∙ : {ℓ₀ ℓ₁ : Level}{A : Type ℓ₀}{B : Type ℓ₁}
    → A → A ∐ B
_∣∙ = inl

∙∣_ : {ℓ₀ ℓ₁ : Level}{A : Type ℓ₀}{B : Type ℓ₁}
   → B → A ∐ B
∙∣_ = inr

infixr 0 ∙∣_
infixr 0 _∣∙

-- A more suggestive way of building a case by case analysis.
-- For example, one can just write f1 ∣ f2 ∣ f3
_∣_ : {a b c : Level}
      {A : Type a}
      {B : Type b}
      {C : Type c}
    → (A → C)
    → (B → C)
    → (A ∐ B → C)

(f ∣ g) (inl a) = f a
(f ∣ g) (inr b) = g b

infixr 0 _∐_
infixr 0 _∣_


-- Case by case analysis.
either : {ℓ₀ ℓ₁ ℓ₃ : Level}
         {A : Type ℓ₀}{B : Type ℓ₁}{C : Type ℓ₃}
       → (A → C) → (B → C) → (A ∐ B → C)
either f g (inl a) = f a
either f g (inr b) = g b
