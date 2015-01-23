{-# OPTIONS --without-K #-}

open import hott.core
open import hott.core.theorems
open import hott.functions

-- An important theorem in topology is to show the 2-dimensional loop
-- space is abelian. To avoid notational clutter we parameterize the
-- common variables as module parameters.

module hott.topology.loopspace.eckmann-hilton {ℓ : Level}{A : Type ℓ}{a : A}
       where


  -- Let us give a name to the trivial loop at a
  reflₐ : a ≡ a
  reflₐ = refl {ℓ}{A}{a}

  open import hott.topology.loopspace

  -- Eckmann-Hilton : (α β : Ω² (A , a)) → α ∙ β ≡ β ∙ α


  -- This uses the wiskering technique. Consider the following paths
  --    ____ p₀ ___   ____ p₁ ____
  --   /           \ /            \
  --  a₀    α₀     a₁      α₁     a₁
  --   \           / \            /
  --    --- q₀ ----   ---- q₁ ----
  --
  -- The 2-dimensional α₀ and α₀ paths cannot be composed in general
  -- as the end point of α₀ (i.e. q₀) is not the starting point of α₁
  -- (i.e. p₁). However, because the paths are 2-dimenional paths we
  -- can compose them horizontally which we denote by ⋆. We
  -- encapsulate this composition inside a module called wiskering.
  --



  module wiskering {x y : A}{p q : x ≡ y} where
    _∙ᵣ_ : {z : A} (α : p ≡ q)(r : y ≡ z) → p ∙ r ≡ q ∙ r
    α ∙ᵣ refl = p∙refl≡p p ∙ α ∙ p≡p∙refl q

    _∙ₗ_ : {w : A}(r : w ≡ x)(β : p ≡ q) → r ∙ p ≡ r ∙ q
    refl ∙ₗ β = refl∙p≡p p ∙ β ∙ p≡refl∙p q


  open wiskering


--------   Lemmas on wiskering ------------------------------------

  -- The next two lemma specialises the wiskering when one of the
  -- paths is refl.
  α∙ᵣrefl≡α : (α : reflₐ ≡ reflₐ) → α ∙ᵣ reflₐ ≡ α
  α∙ᵣrefl≡α α =
    begin α ∙ᵣ refl ≡ refl ∙ α ∙ refl by  definition
                    ≡ α ∙ refl        by  applying flip _∙_ refl
                                      on refl∙p≡p α
                    ≡ α by p∙refl≡p α
    ∎

  refl∙ₗβ≡β : (β : reflₐ ≡ reflₐ) → reflₐ ∙ₗ β ≡ β
  refl∙ₗβ≡β β =
    begin refl ∙ₗ β ≡ refl ∙ β ∙ refl by definition
                    ≡ β ∙ refl        by applying flip _∙_ refl
                                      on refl∙p≡p β
                    ≡ β by p∙refl≡p β
    ∎

---------- End of lemma on wiskering -----------------------------

  -- With wiskering we can now define two different horizontal
  -- composition of higher order paths.
  module horizontal {a₀ a₁ a₂ : A}{p q : a₀ ≡ a₁}{r s : a₁ ≡ a₂} where

    _⋆_  : (α : p ≡ q)
         → (β : r ≡ s)
         → p ∙ r ≡ q ∙ s -- α₀ ⋆ α₁

    α ⋆ β = (α ∙ᵣ r) ∙ (q ∙ₗ β)

    _⋆′_ : (α : p ≡ q)
         → (β : r ≡ s)
         → p ∙ r ≡ q ∙ s

    α ⋆′ β = (p ∙ₗ β) ∙ (α ∙ᵣ s)

  open horizontal

  -- The shows that either ways of horizontal composition gives the
  -- same higher homotopy. Here we need to induct on all α β an
  ⋆≡⋆′ : {p : a ≡ a}{r : a ≡ a}
         (α : p ≡ reflₐ) (β : reflₐ ≡ r )
        → α ⋆ β ≡ α ⋆′ β
  ⋆≡⋆′ refl refl = refl

  -- The specialisation of the above lemma for elements in the second
  -- loop space.
  ⋆≡⋆′-refl : {α β : Ω² (A , a)} → α ⋆ β ≡ α ⋆′ β
  ⋆≡⋆′-refl {α} {β} = ⋆≡⋆′ α β

  -- When every path is refl horizontal compositions α ⋆ β and α ⋆′ β
  -- reduce to α ∙ β and β ∙ α respectively. The proofs are given at
  -- the end.
  α⋆β≡α∙β : {α β : Ω² (A , a)} → α ⋆ β ≡ α ∙ β
  α⋆′β≡β∙α : {α β : Ω² (A , a)} → α ⋆′ β ≡ β ∙ α

  -- From which we get the Eckmann-Hilton theorem.
  Eckmann-Hilton : (α β : Ω² (A , a)) → α ∙ β ≡ β ∙ α
  Eckmann-Hilton α β = begin α ∙ β ≡ α ⋆  β by α⋆β≡α∙β ⁻¹
                                   ≡ α ⋆′ β by ⋆≡⋆′-refl
                                   ≡ β ∙ α  by α⋆′β≡β∙α

  -- Proofs.
  α⋆β≡α∙β {α}{β} =
    begin α ⋆ β ≡ (α ∙ᵣ refl) ∙ (refl ∙ₗ β)
                     by definition
                ≡ (α ∙ᵣ refl) ∙ β
                     by applying _∙_ (α ∙ᵣ refl) on refl∙ₗβ≡β β
                ≡ α ∙ β
                     by applying flip _∙_ β on α∙ᵣrefl≡α α
    ∎
  α⋆′β≡β∙α {α}{β} =
    begin α ⋆′ β ≡ (refl ∙ₗ β) ∙ (α ∙ᵣ refl)
                         by definition
                 ≡ (refl ∙ₗ β) ∙ α
                         by applying _∙_ (refl ∙ₗ β) on α∙ᵣrefl≡α α
                 ≡ β ∙ α
                         by applying flip _∙_ α on refl∙ₗβ≡β β
    ∎
