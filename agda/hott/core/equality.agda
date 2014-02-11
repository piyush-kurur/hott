{-# OPTIONS --without-K #-}
module hott.core.equality where

open import Level
open import hott.core.universe

-- | The equality type. In hott we think of the equality type as paths
-- between two points in the space A.
data _≡_ {ℓ} {A : Type ℓ} : (x y : A) → Type (suc ℓ) where
  refl : ∀ {x} → x ≡ x

-- In hott view point, this function takes the inverse of the path
-- from x to y. As a relation you are proving that ≡ is symmetric.
inv : ∀ {ℓ} {A : Type ℓ} {x y : A}
    → x ≡ y → y ≡ x
inv refl = refl


-- The path composition. This means transitivity of the ≡ relation.
_∘_ : ∀ {ℓ} {A : Type ℓ}  {x y z : A}
    → x ≡ y → y ≡ z → x ≡ z
refl ∘ refl = refl


infixr 0 _≡_
infixr 1 _∘_

-- Proving that the refl path is the identity under path concatnation.
refl-is-left-identity : ∀ {ℓ} {A : Type ℓ}  {x y : A}
                      → ∀ (p : x ≡ y)
                      → p ∘ refl ≡ p
refl-is-left-identity refl = refl

refl-is-right-identity : ∀ {ℓ} {A : Type ℓ}  {x y : A}
                       → ∀ (p : x ≡ y)
                       → refl ∘ p ≡ p

refl-is-right-identity refl = refl


-- Inverse is actually right inverse.
p∘p₁≡refl : ∀ {ℓ} {A : Type ℓ}  {x y : A}
          → ∀ (p : x ≡ y)
          → p ∘ inv p ≡ refl
p∘p₁≡refl refl = refl

-- Inverse is actually left inverse.
p₁∘p≡refl : ∀ {ℓ} {A : Type ℓ}  {x y : A}
          → ∀ (p : x ≡ y)
          → inv p ∘ p ≡ refl
p₁∘p≡refl refl = refl


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

_≅_by_ : ∀ {ℓ} {A : Type ℓ} {x y}
       → x ≡ y
       → (z : A)
       → y ≡ z
       → x ≡ z
p ≅ z by q = p ∘ q

_∎ : ∀ {ℓ} {A : Type ℓ} {x y : A}
   → (x ≡ y)
   → (x ≡ y)
proof ∎ = proof

infixl 2 begin_
infixl 1 _≅_by_
infixl 0 _∎
