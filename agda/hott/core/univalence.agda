{-# OPTIONS --without-K #-}

module hott.core.univalence  where

open import hott.core.universe
open import hott.core.functions
open import hott.core.equality
open import hott.core.sigma


-- The core idea of univalence is to "identify" isomorphic types as
-- equal. Of course the normal definition of isomorphism is that there
-- should be a map from A to B that is witnesses the equivalence of the
-- two type. This is captured by the following record.

record _≃_  {ℓ : Level}(A B : Type ℓ) : Type (lsuc ℓ) where
  constructor IdentifyTypesVia
  field
    equiv     : (A → B)  -- The equivalence
    left-inv  : (B → A)  -- its left inverse
    right-inv : (B → A)  -- and its right inverse

    -- The proofs of the fact that the left and right inverses are actually
    -- left and right inverses.
    left-inv∘equiv~idA  : left-inv ∘ equiv ~ id
    iso∘right-equiv~idB : equiv    ∘ right-inv ~ id

-- Of course a type should be equivalent to itself via identity.
A≃A : {ℓ : Level}{A : Type ℓ} → A ≃ A
A≃A {ℓ} {A} = IdentifyTypesVia id id id (λ _ →  refl) (λ _ → refl)

-- Now we consider the univalence axiom.
postulate Univalence : {ℓ : Level}{A B : Type ℓ} → (A ≃ B) ≃ (A ≡ B)
