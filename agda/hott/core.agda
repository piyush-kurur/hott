-- Exposes the core of hott
module hott.core where

-- Other useful modules from the stdlib

open import Level public using (_⊔_; Level)

-- The basic types of hott

open import hott.core.equality  public -- Equality type
open import hott.core.functions public -- Basic function operation
open import hott.core.nat       public -- Natural numbers
open import hott.core.universe  public -- The type universe
