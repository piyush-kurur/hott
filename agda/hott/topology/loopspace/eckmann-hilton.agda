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
  module wiskering ⦃ u v w : A ⦄ ⦃ p q : u ≡ v ⦄ ⦃ r s : v ≡ w ⦄ where

    -- First we define the horizontal compositions
    _⋆_  : p ≡ q → r ≡ s → p ∙ r ≡ q ∙ s

    α ⋆ β = begin p ∙ r ≡ q ∙ r by applying (λ x → x ∙ r) on α
                        ≡ q ∙ s by applying (λ x → q ∙ x) on β
            ∎

  -- We now consider the horizontal composition in the case when the
  -- end points u, v and w are all a and the paths p, q, r and s are
  -- all refl.
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
