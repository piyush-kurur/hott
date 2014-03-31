-- A placeholder module so that we can write a main. Agda compilation
-- does not work without a main so batch compilation is bound to give
-- errors. For travis builds, we want batch compilation and this is
-- module can be imported to serve that purpose. There is nothing
-- useful that can be achieved from this module though.

module io.placeholder where

open import hott.core.universe

postulate
  Unit      : Type₀
  IO        : Type₀ → Type₀
  dummyMain : IO Unit

{-# COMPILED_TYPE Unit       ()           #-}
{-# COMPILED_TYPE IO         IO           #-}
{-# COMPILED      dummyMain  (return ())  #-}
{-# BUILTIN       IO         IO           #-}
