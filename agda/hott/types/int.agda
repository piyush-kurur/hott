module hott.types.int where


open import hott.functions
open import hott.core
import hott.types.nat as nat

open nat using (ℕ)

data ℤ : Type₀ where
  zero : ℤ
  +ve  : ℕ → ℤ
  -ve  : ℕ → ℤ

fromNat : ℕ → ℤ
fromNat nat.zero = zero
fromNat (nat.succ n) = +ve n

neg : ℤ → ℤ
neg zero = zero
neg (+ve n) = -ve n
neg (-ve n) = +ve n


suc : ℤ → ℤ
suc zero                 = +ve 0
suc (+ve x)              = +ve (nat.succ x)
suc (-ve 0)              = zero
suc (-ve (nat.succ x))   = -ve x


pred : ℤ → ℤ
pred zero                 = -ve 0
pred (-ve x)              = -ve (nat.succ x)
pred (+ve 0)              = zero
pred (+ve (nat.succ x))   = +ve x


suc∘pred~id : suc ∘ pred ~ id
suc∘pred~id zero               = refl
suc∘pred~id (+ve 0)            = refl
suc∘pred~id (+ve (nat.succ x)) = refl
suc∘pred~id (-ve x)            = refl


pred∘suc~id : pred ∘ suc ~ id
pred∘suc~id zero               = refl
pred∘suc~id (+ve x)            = refl
pred∘suc~id (-ve 0)            = refl
pred∘suc~id (-ve (nat.succ x)) = refl
