{-# OPTIONS --without-K #-}

-- Some basic theorems on paths and path compositions.
module hott.core.equality.theorems where

open import hott.core

-- The path refl is the left identity under path concatnation.
refl∙p≡p : ∀ {ℓ} {A : Type ℓ}  {x y : A}
                      → ∀ (p : x ≡ y)
                      → refl ∙ p ≡ p
refl∙p≡p refl = refl

-- Alternate form of refl being left identity.
p≡refl∙p : ∀ {ℓ} {A : Type ℓ}  {x y : A}
         → ∀ (p : x ≡ y)
         → p ≡ refl ∙ p
p≡refl∙p p = refl∙p≡p p ⁻¹

-- The path refl is the right identity under path concatnation.
p∙refl≡p : ∀ {ℓ} {A : Type ℓ}  {x y : A}
         → ∀ (p : x ≡ y)
         → p ∙ refl ≡ p

p∙refl≡p refl = refl

-- Alternate form of refl being the right identity.
p≡p∙refl : ∀ {ℓ} {A : Type ℓ}  {x y : A}
         → ∀ (p : x ≡ y)
         → p ≡ p ∙ refl

p≡p∙refl p = p∙refl≡p p ⁻¹

-- The inverse of inverse is identity
p⁻¹⁻¹≡p  : ∀ {ℓ} {A : Type ℓ}  {x y : A}
         → ∀ (p : x ≡ y)
         → (p ⁻¹)⁻¹ ≡ p
p⁻¹⁻¹≡p refl = refl

-- Alternate form of the theorem inverse of inverse is identity.
p≡p⁻¹⁻¹  : ∀ {ℓ} {A : Type ℓ}  {x y : A}
         → ∀ (p : x ≡ y)
         → p ≡ (p ⁻¹)⁻¹
p≡p⁻¹⁻¹ p = p⁻¹⁻¹≡p p ⁻¹


-- Inverse is actually right inverse.
p∙p⁻¹≡refl : ∀ {ℓ} {A : Type ℓ}  {x y : A}
          → ∀ (p : x ≡ y)
          → p ∙ p ⁻¹ ≡ refl
p∙p⁻¹≡refl refl = refl

-- Inverse is actually left inverse.
p⁻¹∙p≡refl : ∀ {ℓ} {A : Type ℓ}  {x y : A}
          → ∀ (p : x ≡ y)
          → p ⁻¹ ∙ p ≡ refl
p⁻¹∙p≡refl refl = refl


-- The associativity of path composition.
assoc :  ∀ {ℓ} {A : Type ℓ}  {u v w x : A}
      → (p : u ≡ v)
      → (q : v ≡ w)
      → (r : w ≡ x)
      → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc refl refl refl = refl
