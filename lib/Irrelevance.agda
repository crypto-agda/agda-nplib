{-# OPTIONS --universe-polymorphism #-}
module Irrelevance where

import Level

record Irr {a} (A : Set a) : Set a where
  constructor irr
  field
    .cert : A

open Irr public
