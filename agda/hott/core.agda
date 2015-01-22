{-# OPTIONS --without-K #-}

-- Exposes the core of hott
module hott.core where

-- The basic types of hott

open import hott.core.equality  public -- Equality type
open import hott.core.functions public -- Basic function operation
open import hott.core.sigma     public -- Dependent pairs
open import hott.core.coproduct public -- Co-product
open import hott.core.universe  public -- Universes
open import hott.core.universe.pointed public
                                       -- and the pointed ones.
