{-# OPTIONS --without-K #-}
module Irrelevance.NP where

open import Irrelevance public

import Level

record Irr {a} (A : Set a) : Set a where
  constructor irr
  field
    .cert : A

open Irr public
