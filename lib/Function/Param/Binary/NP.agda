module Function.Param.Binary.NP where

open import Type.Param.Binary
open import Data.Two.Param.Binary
open import Function.NP
open import Function.Param.Binary public

⟦id⟧ : (∀⟨ Aᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ Aᵣ ⟦→⟧ Aᵣ) id id
⟦id⟧ _ xᵣ = xᵣ

⟦∘′⟧ : (∀⟨ Aᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ ∀⟨ Cᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ (Bᵣ ⟦→⟧ Cᵣ) ⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ (Aᵣ ⟦→⟧ Cᵣ)) _∘′_ _∘′_
⟦∘′⟧ _ _ _ fᵣ gᵣ xᵣ = fᵣ (gᵣ xᵣ)

⟦Endo⟧ : ∀ {a} → (⟦★⟧ {a} {a} a ⟦→⟧ ⟦★⟧ _) Endo Endo
⟦Endo⟧ Aᵣ = Aᵣ ⟦→⟧ Aᵣ

⟦Cmp⟧ : ∀ {a} → (⟦★⟧ {a} {a} a ⟦→⟧ ⟦★⟧ _) Cmp Cmp
⟦Cmp⟧ Aᵣ = Aᵣ ⟦→⟧ Aᵣ ⟦→⟧ ⟦𝟚⟧
