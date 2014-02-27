{-# OPTIONS --without-K #-}
module Data.RGB where

open import Type

data RGB : ★ where
  `R `G `B : RGB

[R:_G:_B:_] : ∀ {ℓ}{C : RGB → ★_ ℓ}(r : C `R)(g : C `G)(b : C `B)(rgb : RGB) → C rgb
[R: r G: g B: b ] `R = r
[R: r G: g B: b ] `G = g
[R: r G: g B: b ] `B = b
