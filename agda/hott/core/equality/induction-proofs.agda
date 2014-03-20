{-# OPTIONS --without-K #-}

--
-- This module defines/proves some basic functions/theorem using only
-- the induction principle of the equality types the way they are done
-- in the HoTT book.  The functions defined/theorems proved in this
-- module is often exposed in a better way from the main equality
-- module, the word better means simpler definitions/proofs.  This
-- module is thus not meant for use in "production" hott.
--

module hott.core.equality.induction-proofs where

open import hott.core

-- The symmetry of ≡ defined in terms of the induction principle
sym : ∀{ℓ} {A : Type ℓ} {x y : A}
    → x ≡ y → y ≡ x
sym {ℓ} {A}  = induction≡ D d
  where
    D : {u v : A} → u ≡ v → Type ℓ
    D {u} {v} _ = v ≡ u
    d : {u : A} → D {u} refl
    d  = refl

-- The transitivity of ≡.
trans : ∀{ℓ} {A : Type ℓ} {x y z : A}
      → x ≡ y → y ≡ z → x ≡ z
trans {ℓ} {A} xEy = induction≡ D d xEy
  where
    D : {u v : A} → u ≡ v → Type ℓ
    D {u} {v} _ = {w : A} → v ≡ w → u ≡ w

    d : {u : A} → D {u} refl
    d uEw = uEw

symIsInv : ∀{ℓ} {A : Type ℓ} {x y : A}
         → (p : x ≡ y) → sym p ≡ p ⁻¹
symIsInv refl = refl
