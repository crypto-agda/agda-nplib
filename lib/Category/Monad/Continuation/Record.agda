{-# OPTIONS --copatterns #-}

open import Level
open import Type hiding (★)
open import Function
open import Data.Product hiding (map)

module Category.Monad.Continuation.Record {t} (T : ★ t) where 

record Cont {a} (A : ★ a) : ★ (a ⊔ t) where
  field
    runCont : (A → T) → T 

open Cont

module _ {a b} {A : ★ a} {B : ★ b} where
    map : (A → B) → (Cont A → Cont B)
    runCont (map f mx) k = runCont mx λ x → k (f x)

    _>>=_ : Cont A → (A → Cont B) → Cont B
    runCont (mx >>= f) k = runCont mx λ x → runCont (f x) k

module _ {a} {A : ★ a} where
    return : A → Cont A
    runCont (return x) k = k x

    join : Cont (Cont A) → Cont A
    join mmx = mmx >>= id

    module _ {b} {B : ★ b} where
        _⊛_ : Cont (A → B) → Cont A → Cont B
        mf ⊛ mx = mf >>= λ f → map f mx

    module _ {b} {B : A → ★ b} where
        _⟨,⟩_ : Cont A → (∀ {x} → Cont (B x)) → Cont (Σ A B)
        runCont (fA ⟨,⟩ fB) f = runCont fA (runCont fB ∘ curry f)

    module _ {b} {B : ★ b} where
        _⟨,⟩′_ : Cont A → Cont B → Cont (A × B)
        mx ⟨,⟩′ my = mx ⟨,⟩ my

module _ {a b c} {A : ★ a} {B : ★ b} {C : ★ c} where
    ⟪_·_·_⟫ : (A → B → C) → Cont A → Cont B → Cont C
    ⟪ f · mx · my ⟫ = map f mx ⊛ my
