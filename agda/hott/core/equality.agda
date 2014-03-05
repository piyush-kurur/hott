{-# OPTIONS --without-K #-}
module hott.core.equality where

open import Level
open import hott.core.universe

-- | The equality type. In hott we think of the equality type as paths
-- between two points in the space A.
data _≡_ {ℓ} {A : Type ℓ} (x : A) : (y : A) → Type ℓ where
  refl : x ≡ x

-- Induction principle for ≡ type.
induction≡ : {ℓ₀ ℓ₁ : Level} {A : Type ℓ₀}
         → (D : {x y : A} (p : x ≡ y) → Type ℓ₁)
         → (d : {x : A} → D {x} {x} refl)
         → {x y : A} → (p : x ≡ y) → D p

induction≡ D d refl = d

-- In hott view point, this function takes the inverse of the path
-- from x to y. As a relation you are proving that ≡ is symmetric.
_⁻¹ : ∀{ℓ} {A : Type ℓ} {x y : A}
    → x ≡ y → y ≡ x
refl ⁻¹ = refl


-- The path composition. This means transitivity of the ≡ relation.
_∘_ : ∀ {ℓ} {A : Type ℓ}  {x y z : A}
    → x ≡ y → y ≡ z → x ≡ z
refl ∘ refl = refl


infixr 0 _≡_
infixr 1 _∘_
infixl 2 _⁻¹

-- The path refl is the left identity under path concatnation.
refl∘p≡p : ∀ {ℓ} {A : Type ℓ}  {x y : A}
                      → ∀ (p : x ≡ y)
                      → refl ∘ p ≡ p
refl∘p≡p refl = refl

-- Alternate form of refl being left identity.
p≡refl∘p : ∀ {ℓ} {A : Type ℓ}  {x y : A}
         → ∀ (p : x ≡ y)
         → p ≡ refl ∘ p
p≡refl∘p p = refl∘p≡p p ⁻¹

-- The path refl is the right identity under path concatnation.
p∘refl≡p : ∀ {ℓ} {A : Type ℓ}  {x y : A}
         → ∀ (p : x ≡ y)
         → p ∘ refl ≡ p

p∘refl≡p refl = refl

-- Alternate form of refl being the right identity.
p≡p∘refl : ∀ {ℓ} {A : Type ℓ}  {x y : A}
         → ∀ (p : x ≡ y)
         → p ≡ p ∘ refl

p≡p∘refl p = p∘refl≡p p ⁻¹

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
p∘p⁻¹≡refl : ∀ {ℓ} {A : Type ℓ}  {x y : A}
          → ∀ (p : x ≡ y)
          → p ∘ p ⁻¹ ≡ refl
p∘p⁻¹≡refl refl = refl

-- Inverse is actually left inverse.
p⁻¹∘p≡refl : ∀ {ℓ} {A : Type ℓ}  {x y : A}
          → ∀ (p : x ≡ y)
          → p ⁻¹ ∘ p ≡ refl
p⁻¹∘p≡refl refl = refl


-- The associativity of path composition.
assoc :  ∀ {ℓ} {A : Type ℓ}  {u v w x : A}
      → (p : u ≡ v)
      → (q : v ≡ w)
      → (r : w ≡ x)
      → (p ∘ q) ∘ r ≡ p ∘ (q ∘ r)
assoc refl refl refl = refl

-- The functional congruence, i.e. likes gives likes on application of
-- a function. In the HoTT perspective this says that functions are
-- functors.
ap : ∀ {ℓ₀ ℓ₁} {A : Type ℓ₀}  {B : Type ℓ₁} {x y : A}
     → ∀ (f : A → B)
     → x ≡ y → f x ≡ f y
ap f refl = refl

-- Equational reasoning
-- To prove x_0 = x_n by a sequence of proofs
-- x_0 = x_1
-- x_1 = x_2
-- ... you can use the following syntax
--
-- begin x_0 ≅ x_1 by p1
--           ≅ x_2 by p2
--       ....
--           ≅ x_n by pn
-- ∎
--
begin_ : ∀ {ℓ} {A : Type ℓ}
       → (x : A)
       → x ≡ x
begin_ x = refl

_≡_by_ : ∀ {ℓ} {A : Type ℓ} {x y}
       → x ≡ y
       → (z : A)
       → y ≡ z
       → x ≡ z
p ≡ z by q = p ∘ q

_∎ : ∀ {ℓ} {A : Type ℓ} {x y : A}
   → (x ≡ y)
   → (x ≡ y)
proof ∎ = proof

-- In equational proofs, it is more readable to use by definition
-- than by refl
definition : ∀{ℓ} {A : Type ℓ} {x : A} → x ≡ x
definition = refl

infixl 2 begin_
infixl 1 _≡_by_
infixl 0 _∎
