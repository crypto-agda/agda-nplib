module Function.Param.Unary.NP where

open import Type.Param.Unary
open import Data.Two.Param.Unary
open import Function.NP
open import Function.Param.Unary public

[Endo] : ∀ {a} → ([★] {a} a [→] [★] _) Endo
[Endo] Aₚ = Aₚ [→] Aₚ

[Cmp] : ∀ {a} → ([★] {a} a [→] [★] _) Cmp
[Cmp] Aₚ = Aₚ [→] Aₚ [→] [𝟚]
