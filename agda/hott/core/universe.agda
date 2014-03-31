{-# OPTIONS --without-K #-}

-- The universe of all types
module hott.core.universe where

postulate
  Level : Set
  lzero : Level
  lsuc  : Level → Level
  _⊔_   : Level → Level → Level

{-# COMPILED_TYPE Level ()            #-}
{-# COMPILED      lzero          ()   #-}
{-# COMPILED      lsuc (\ _   -> ())  #-}
{-# COMPILED      _⊔_  (\ _ _ -> ())  #-}

{-# BUILTIN LEVEL       Level  #-}
{-# BUILTIN LEVELZERO   lzero  #-}
{-# BUILTIN LEVELSUC    lsuc   #-}
{-# BUILTIN LEVELMAX    _⊔_    #-}

-- We give an new name for Set
Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ

private
  one   = lsuc lzero
  two   = lsuc one
  three = lsuc two
  four  = lsuc three
  five  = lsuc four
  six   = lsuc five
  seven = lsuc six
  eight = lsuc seven
  nine  = lsuc eight

Type₀ = Type lzero
Type₁ = Type one
Type₂ = Type two
Type₃ = Type three
Type₄ = Type four
Type₅ = Type five
Type₆ = Type six
Type₇ = Type seven
Type₈ = Type eight
Type₉ = Type nine
