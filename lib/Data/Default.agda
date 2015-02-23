{-# OPTIONS --without-K #-}
module Data.Default where

record Default {a} (A : Set a) : Set a where
  field
    dflt : A
open Default {{...}} public
