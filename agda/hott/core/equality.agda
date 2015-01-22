{-# OPTIONS --without-K #-}
module hott.core.equality where

open import hott.core.universe

-- | The equality type. In hott we think of the equality type as paths
-- between two points in the space A. To simplify the types we first
-- fix the common parameters.

module common {a : Level}{A : Type a} where


  data _≡_ (x : A) : (y : A) → Type a where
    refl : x ≡ x

  -- Induction principle for ≡ type.
  induction≡ : {ℓ : Level}
             → (D : {x y : A} (p : x ≡ y) → Type ℓ)
             → (d : {x : A} → D {x} {x} refl)
             → {x y : A} → (p : x ≡ y) → D p
  induction≡ D d refl = d

  -- In hott view point, this function takes the inverse of the path
  -- from x to y. As a relation you are proving that ≡ is symmetric.
  _⁻¹ : ∀{x y}
      → x ≡ y → y ≡ x
  refl ⁻¹ = refl

  -- The path composition. This means transitivity of the ≡ relation.
  _∙_ : ∀ {x y z}
      → x ≡ y → y ≡ z → x ≡ z
  refl ∙ refl = refl


  infixr 1 _≡_

  -- Precedence of multiplication
  infixl 70 _∙_

  -- Precedence of exponentiation.
  infixl 90 _⁻¹
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

  -- In equational proofs, it is more readable to use by definition
  -- than by refl
  definition : ∀{x} → x ≡ x
  definition = refl

  begin_ : (x : A)
         → x ≡ x
  begin_ x = refl

  _≡_by_ : ∀ {x y : A}
         → x ≡ y
         → (z : A)
         → y ≡ z
         → x ≡ z
  p ≡ z by q = p ∙ q

  _∎ : ∀{x y : A}
     → (x ≡ y)
     → (x ≡ y)
  proof ∎ = proof

  infixl 2 begin_
  infixl 1 _≡_by_
  infixl 0 _∎


  -- We now capture path transportation in the following submodule.
  module Transport {ℓ : Level} where
    -- Path transportation.
    transport : ∀ {x y : A}
              → x ≡ y
              → {P : A → Type ℓ}
              → P x → P y
    transport refl = λ z → z

    -- Another symbol for transport. Use it when you do not want to
    -- specify P.
    _⋆ : {P : A → Type ℓ}
     → {x y : A}
     → x ≡ y
     → P x → P y
    p ⋆ = transport p

  open Transport public

open common public


{-# BUILTIN EQUALITY _≡_     #-}
{-# BUILTIN REFL     refl    #-}


-- The functional congruence, i.e. likes gives likes on application of
-- a function. In the HoTT perspective this says that functions are
-- functors.
ap : ∀ {a b : Level} {A : Type a}{B : Type b} {x y : A}
     → (f : A → B)
     → x ≡ y → (f x) ≡ (f y)
ap f refl = refl

-- The dependent version of ap. This requires transport for its
-- definition.
apd : ∀{a b : Level }{A : Type a}{B : A → Type b}
    → (f : (a : A) → B a)
    → {x y : A}
    → (p : x ≡ y)
    → (p ⋆) (f x) ≡ f y
apd f refl = refl

-- Better syntax fro ap in equational reasoning.
applying_on_ : ∀{ℓ₀ ℓ₁}{A : Type ℓ₀}{B : Type ℓ₁}
             → (f : A → B)
             → {x y : A}
             → (p : x ≡ y)
             → f x ≡ f y
applying_on_ f a = ap f a

-- Better syntax for dependent version of applying on both sides.
transporting_over_ : ∀{ℓ₀ ℓ₁}{A : Type ℓ₀}{B : A → Type ℓ₁}
                   → (f : (a : A) → B(a)){x y : A}
                   → (p : x ≡ y)
                   → (p ⋆) (f x) ≡ f y
transporting f over p = apd f p

infixr 2 applying_on_
infixr 2 transporting_over_
