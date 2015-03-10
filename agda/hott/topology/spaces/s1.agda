{-# OPTIONS --without-K #-}
module hott.topology.spaces.s1 where


open import hott.core

-- The universe where we work.
𝒰 = Type₀

module Definition where
  private data SInternal : 𝒰 where
               pointInternal : SInternal
  S₁ : 𝒰
  S₁ = SInternal

  point : S₁
  point = pointInternal

  postulate loop : point ≡ point

  -- the induction principle for s₁
  ind-S₁ : {ℓ : Level}{B : S₁ → Type ℓ}
         → (b : B point)
         → (b ≡ b)
         → (x : S₁) → B x
  ind-S₁ b x pointInternal = b

open Definition
