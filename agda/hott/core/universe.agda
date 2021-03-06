{-# OPTIONS --without-K #-}

-- The universe of all types
module hott.core.universe where

open import Agda.Primitive public using (Level; lzero; lsuc; _⊔_)

-- We give an new name for Set
Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ

lone   : Level; lone   = lsuc lzero
ltwo   : Level; ltwo   = lsuc lone
lthree : Level; lthree = lsuc ltwo
lfour  : Level; lfour  = lsuc lthree
lfive  : Level; lfive  = lsuc lfour
lsix   : Level; lsix   = lsuc lfive
lseven : Level; lseven = lsuc lsix
leight : Level; leight = lsuc lseven
lnine  : Level; lnine  = lsuc leight

Type₀ = Type lzero
Type₁ = Type lone
Type₂ = Type ltwo
Type₃ = Type lthree
Type₄ = Type lfour
Type₅ = Type lfive
Type₆ = Type lsix
Type₇ = Type lseven
Type₈ = Type leight
Type₉ = Type lnine
