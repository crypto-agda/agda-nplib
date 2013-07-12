{-# OPTIONS --without-K #-}
{-# OPTIONS --copatterns #-}

open import Level
open import Type hiding (★)
open import Function
open import Data.Product hiding (map)

module Category.Monad.Continuation.Record {t} where 

record Cont {a} (T : ★ t) (A : ★ a) : ★ (a ⊔ t) where
  field
    runCont : (A → T) → T 

open Cont

module _ {T : ★ t} where
    M : ∀ {a} → ★ a → ★ _
    M = Cont T

    module _ {a b} {A : ★ a} {B : ★ b} where
        map : (A → B) → (M A → M B)
        runCont (map f mx) k = runCont mx λ x → k (f x)

        _>>=_ : M A → (A → M B) → M B
        runCont (mx >>= f) k = runCont mx λ x → runCont (f x) k

    module _ {a} {A : ★ a} where
        return : A → M A
        runCont (return x) k = k x

        join : M (M A) → M A
        join mmx = mmx >>= id

        module _ {b} {B : ★ b} where
            _⊛_ : M (A → B) → M A → M B
            mf ⊛ mx = mf >>= λ f → map f mx

        module _ {b} {B : A → ★ b} where
            _⟨,⟩_ : M A → (∀ {x} → M (B x)) → M (Σ A B)
            runCont (fA ⟨,⟩ fB) f = runCont fA (runCont fB ∘ curry f)

        module _ {b} {B : ★ b} where
            _⟨,⟩′_ : M A → M B → M (A × B)
            mx ⟨,⟩′ my = mx ⟨,⟩ my

    module _ {a b c} {A : ★ a} {B : ★ b} {C : ★ c} where
        ⟪_·_·_⟫ : (A → B → C) → M A → M B → M C
        ⟪ f · mx · my ⟫ = map f mx ⊛ my
