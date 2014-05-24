{-# OPTIONS --without-K #-}

module hott.topology.loopspace where

open import hott.core


-- The pointed loop space

Ω∙ : ∀{ℓ} → Type● ℓ → Type● ℓ
Ω∙ (A , a) = (a ≡ a , refl)

-- The loops space. It is obtained by suppressing the base point of
-- the corresponding pointed loop space.
Ω : ∀{ℓ} → Type● ℓ → Type ℓ
Ω = space ∘ Ω∙

--

-- The iterated pointed loop space

Ω̂∙ : ∀{ℓ}  → ℕ → Type● ℓ → Type● ℓ
Ω̂∙ = iterate Ω∙


-- The iterated loop space. It is obtained by suppressing the base
-- point of the iterated pointed loop space.

Ω̂ : ∀{ℓ}  → ℕ → Type● ℓ → Type ℓ
Ω̂ n = space ∘ Ω̂∙ n

-- Some short hands


Ω²∙ : ∀{ℓ} → Type● ℓ → Type● ℓ; Ω²∙ = Ω̂∙ 2
Ω³∙ : ∀{ℓ} → Type● ℓ → Type● ℓ; Ω³∙ = Ω̂∙ 3
Ω⁴∙ : ∀{ℓ} → Type● ℓ → Type● ℓ; Ω⁴∙ = Ω̂∙ 4
Ω⁵∙ : ∀{ℓ} → Type● ℓ → Type● ℓ; Ω⁵∙ = Ω̂∙ 5
Ω⁶∙ : ∀{ℓ} → Type● ℓ → Type● ℓ; Ω⁶∙ = Ω̂∙ 6
Ω⁷∙ : ∀{ℓ} → Type● ℓ → Type● ℓ; Ω⁷∙ = Ω̂∙ 7
Ω⁸∙ : ∀{ℓ} → Type● ℓ → Type● ℓ; Ω⁸∙ = Ω̂∙ 8
Ω⁹∙ : ∀{ℓ} → Type● ℓ → Type● ℓ; Ω⁹∙ = Ω̂∙ 9


Ω² : ∀{ℓ} → Type● ℓ → Type ℓ; Ω² = Ω̂ 2
Ω³ : ∀{ℓ} → Type● ℓ → Type ℓ; Ω³ = Ω̂ 3
Ω⁴ : ∀{ℓ} → Type● ℓ → Type ℓ; Ω⁴ = Ω̂ 4
Ω⁵ : ∀{ℓ} → Type● ℓ → Type ℓ; Ω⁵ = Ω̂ 5
Ω⁶ : ∀{ℓ} → Type● ℓ → Type ℓ; Ω⁶ = Ω̂ 6
Ω⁷ : ∀{ℓ} → Type● ℓ → Type ℓ; Ω⁷ = Ω̂ 7
Ω⁸ : ∀{ℓ} → Type● ℓ → Type ℓ; Ω⁸ = Ω̂ 8
Ω⁹ : ∀{ℓ} → Type● ℓ → Type ℓ; Ω⁹ = Ω̂ 9
