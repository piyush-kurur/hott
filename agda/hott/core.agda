{-# OPTIONS --without-K #-}

-- Exposes the core of hott
module hott.core where

-- Other useful modules from the stdlib

-- The basic types of hott

open import hott.core.equality  public -- Equality type
open import hott.core.functions public -- Basic function operation
open import hott.core.nat       public -- Natural numbers
open import hott.core.pair      public -- Dependent pairs
open import hott.core.universe  public -- The type universe
