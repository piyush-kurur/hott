{-# OPTIONS --without-K #-}

module hott.core.univalence  where

open import hott.core.universe
open import hott.functions
open import hott.core.equality
open import hott.core.sigma


-- The core idea of univalence is to "identify" isomorphic types as
-- equal. Of course the normal definition of isomorphism is that there
-- should be a map from A to B that is witnesses the equivalence of the
-- two type. This is captured by the following record.
record _≃_  {a b : Level}(A : Type a)(B : Type b) : Type (a ⊔ b) where

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

-- Equal types are equivalent.
≡→≃ : {ℓ : Level}{A B : Type ℓ} → A ≡ B → A ≃ B
≡→≃ refl = A≃A


-- For the converse we need the univalence. However Univalence says
-- something. Not only can we infer A ≡ B from A ≃ B via the postulate
-- ua, this map together with ≡→≃ gives an equivalence of types.
module Univalence {ℓ : Level}{A B : Type ℓ} where

  -- The main axiom is to identify A ≃ B with A ≡ B
  postulate ua : A ≃ B → A ≡ B

  -- Now we are ready for the univalence axiom.
  UnivalenceAxiom : (A ≃ B) ≃ (A ≡ B)
  UnivalenceAxiom = IdentifyTypesVia ua ≡→≃ ≡→≃ linv-prf rinv-prf
    where postulate rinv-prf :  ua ∘ ≡→≃ ~ id
          postulate linv-prf :  ≡→≃ ∘ ua ~ id

  -- The next function helps in clean use of the univalence
  -- axioms in equational reasoning.
  --
  --
  -- begin ...
  --       ≡    B by univalence
  --       ...
  --
  -- provided an appropriate instance of A ≃ B is available in the
  -- vicinity.
  --
  univalence : ⦃ a≃b : A ≃ B ⦄ → A ≡ B
  univalence ⦃ a≃b ⦄ = ua a≃b

open Univalence public
