{-# OPTIONS --without-K #-}
module hott.core.equality where

open import Level
open import hott.core.universe

-- | The equality type. In hott we think of the equality type as paths
-- between two points in the space A.
data _≡_ {ℓ} {A : Type ℓ} (x : A) : (y : A) → Type ℓ where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl    #-}

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

-- The functional congruence, i.e. likes gives likes on application of
-- a function. In the HoTT perspective this says that functions are
-- functors.
ap : ∀ {ℓ₀ ℓ₁} {A : Type ℓ₀}  {B : Type ℓ₁} {x y : A}
     → ∀ (f : A → B)
     → x ≡ y → f x ≡ f y
ap f refl = refl


infixr 0 _≡_
infixr 1 _∘_
infixl 2 _⁻¹

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
