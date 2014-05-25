{-# OPTIONS --without-K #-}

open import hott.core

-- An important theorem in topology is to show the 2-dimensional loop
-- space is abelian. To avoid notational clutter we parameterize the
-- common variables as module parameters.

module hott.topology.loopspace.eckmann-hilton {ℓ : Level}{A : Type ℓ}{a : A} where

  open import hott.topology.loopspace

  Eckmann-Hilton : (α β : Ω² (A , a)) → α ∙ β ≡ β ∙ α

  -- This uses the wiskering technique. Consider the following paths
  --    ____ p ____   _____ r ____
  --   /           \ /            \
  --  u      α      v        β     w
  --   \           / \            /
  --    ---- q-----   ----- s ----
  --
  -- The 2-dimensional α and β paths cannot be composed in general as
  -- the end point of α (i.e. q) is not the starting point of β
  -- (i.e. r). However, because the paths are 2-dimenional paths we
  -- can compose them horizontally which we denote by ⋆. We
  -- encapsulate this composition inside a module called wiskering.
  --


  module wiskering ⦃ a₀ a₁ a₂ : A ⦄ ⦃ p₀ q₀ : a₀ ≡ a₁ ⦄ ⦃ p₁ q₁ : a₁ ≡ a₂ ⦄ where

    -- Our goal is to define the horizontal composition given below
    _⋆_  : (α₀ : p₀ ≡ q₀)
         → (α₁ : p₁ ≡ q₁)
         → p₀ ∙ p₁ ≡ q₀ ∙ q₁

    -- The idea is to "slide" one 1-d path at a time starting from p₀
    -- using the 2-d path α₀. For this fix an aribitrary path γ₁ from
    -- a₁ to a₂ and consider the single argument function that takes
    -- any path γ₀ from a₀ to a₁ and appends γ₁ to it. By applying
    -- this to α₀ we can slide from p₀ ∙ γ₁ to q₀ ∙ γ₁.  The function
    -- is defined below. The ⟦⟧ indicates the place where we need to
    -- put the argument.
    ⟦⟧∙_   : (γ₁ : a₁ ≡ a₂)
           → (γ₀ : a₀ ≡ a₁)
           → (a₀ ≡ a₂)
    ⟦⟧∙ γ₁ = λ γ₀ → γ₀ ∙ γ₁

    -- The next function is similar to the previous function but used
    -- to slide the second 1-d path around α₁.
    _∙⟦⟧   : (γ₀ : a₀ ≡ a₁ )
           → (γ₁ : a₁ ≡ a₂)
           → (a₀ ≡ a₂)
    γ₀ ∙⟦⟧ = λ γ₁ → γ₀ ∙ γ₁

    -- Finally we have the horizontal composition.
    α₀ ⋆ α₁ = begin p₀ ∙ p₁ ≡ q₀ ∙ p₁ by applying ⟦⟧∙ p₁ on α₀
                                      -- sliding along α₀
                            ≡ q₀ ∙ q₁ by applying q₀ ∙⟦⟧ on α₁
                                      -- sliding aloing α₁
              ∎

    -- The operator ⋆′ in the book is obtained by sliding in a
    -- different order. We do not need to define that but we give
    -- definition none the less for illustration.
    --
    _⋆′_ : (α₀ : p₀ ≡ q₀)
         → (α₁ : p₁ ≡ q₁)
         → p₀ ∙ p₁ ≡ q₀ ∙ q₁
    --
    α₀ ⋆′ α₁ = begin p₀ ∙ p₁ ≡ p₀ ∙ q₁ by applying p₀ ∙⟦⟧ on α₁
                                       -- sliding along α₁
                             ≡ q₀ ∙ q₁ by applying ⟦⟧∙ q₁ on α₀
                                       -- sliding along α₀
               ∎

    -- End of module wiskering.

  -- We now consider the horizontal composition in the case when the
  -- end points a₀, a₁ and a₂ are all a and the paths p₀, p₁, q₀ and
  -- q₁ are all refl.
  AllPathsAreRefl : a ≡ a; AllPathsAreRefl = refl
  private open wiskering

  -- In this case the horizontal composition and vertical composition
  -- satisfies the following identities.
  private α∙β≡α⋆β : (α β : Ω² (A , a)) → α ∙ β ≡ α ⋆ β
  private α⋆β≡β∙α : (α β : Ω² (A , a)) → α ⋆ β ≡ β ∙ α

  α∙β≡α⋆β refl refl = refl
  α⋆β≡β∙α refl refl = refl

  -- Finally, we are at the proof.
  Eckmann-Hilton α β = begin α ∙ β ≡ α ⋆ β by α∙β≡α⋆β α β
                                   ≡ β ∙ α by α⋆β≡β∙α α β

                       ∎
