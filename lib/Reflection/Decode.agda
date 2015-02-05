module Reflection.Decode where

open import Opaque
open import Data.Maybe.NP hiding (map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Zero using (𝟘)
open import Data.One using (𝟙; 0₁)
open import Data.Two using (𝟚; 0₂; 1₂; [0:_1:_])
open import Data.Vec using (Vec) -- ; []; _∷_)
open import Data.List using (List; []; _∷_)
open import Data.Product.NP hiding (map)
open import Reflection.NP

Decode-Term : ∀ {a} → Set a → Set a
Decode-Term A = Term → Maybe A

pattern `𝟘 = def (quote 𝟘) []

pattern `𝟙  = def (quote 𝟙) []
pattern `0₁ = con (quote 0₁) []

decode-𝟙 : Decode-Term 𝟙
decode-𝟙 `0₁ = just 0₁
decode-𝟙 _   = nothing

pattern `𝟚  = def (quote 𝟚) []
pattern `0₂ = con (quote 0₂) []
pattern `1₂ = con (quote 1₂) []

decode-𝟚 : Decode-Term 𝟚
decode-𝟚 `0₂ = just 0₂
decode-𝟚 `1₂ = just 1₂
decode-𝟚 _   = nothing

decode-ℕ : Decode-Term ℕ
decode-ℕ (lit (nat n)) = just n
-- these two should not happen anymore:
decode-ℕ `zero         = just 0
decode-ℕ (`suc t)      = map? suc (decode-ℕ t)
decode-ℕ _             = nothing

pattern `Maybe t = defᵛʳ (quote Maybe) t
pattern `nothing = con (quote Maybe.nothing) []
pattern `just  t = conᵛʳ (quote Maybe.just) t

decode-Maybe : ∀ {a} {A : Set a} → Decode-Term A → Decode-Term (Maybe A)
decode-Maybe decode-A `nothing  = just nothing
decode-Maybe decode-A (`just t) = map? just (decode-A t)
decode-Maybe decode-A _         = nothing

pattern `List t = defᵛʳ (quote List) t
pattern `[] = con (quote List.[]) []
pattern _`∷_ t u = con (quote List._∷_) (argᵛʳ t ∷ argᵛʳ u ∷ [])

decode-List : ∀ {a} {A : Set a} → Decode-Term A → Decode-Term (List A)
decode-List decode-A `[]      = just []
decode-List decode-A (t `∷ u) = ⟪ _∷_ · decode-A t · decode-List decode-A u ⟫?
decode-List decode-A _        = nothing

pattern `Vec t u = def (quote Vec) (argᵛʳ t ∷ argᵛʳ u ∷ [])
pattern `v[]      = con (quote Vec.[]) []
pattern _`v∷_ t u = con (quote Vec._∷_) (argᵛʳ t ∷ argᵛʳ u ∷ [])

{-
decode-Vec : ∀ {a} {A : ★_ a} {n} → Decode-Term A → Decode-Term (Vec A n)
decode-Vec decode-A `[]      = just []
decode-Vec decode-A (t `∷ u) = ⟪ _∷_ · decode-A t · decode-Vec decode-A u ⟫?
decode-Vec decode-A _        = nothing
-}

pattern `Σ t u = def (quote Σ) (argᵛʳ t ∷ argᵛʳ u ∷ [])
pattern _`,_ t u = con (quote Σ._,_) (argᵛʳ t ∷ argᵛʳ u ∷ [])
pattern `fst t = defᵛʳ (quote fst) t
pattern `snd t = defᵛʳ (quote snd) t

module _ {a b} {A : Set a} {B : A → Set b}
         (decode-A : Decode-Term A)
         (decode-B : (x : A) → Decode-Term (B x))
         where
    decode-Σ : Decode-Term (Σ A B)
    decode-Σ (t `, u) = decode-A t   >>=? λ x →
                        decode-B x u >>=? λ y →
                        just (x , y)
    decode-Σ _        = nothing
