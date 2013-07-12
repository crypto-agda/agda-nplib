{-# OPTIONS --without-K #-}
open import Level
open import Type hiding (★)
open import Function
open import Data.Product hiding (map)

module Category.Monad.Continuation.Alias {t} where 

Cont : ∀ {a} → ★ t → ★ a → ★ _
Cont T A = (A → T) → T 

module _ {T : ★ t} where
    M : ∀ {a} → ★ a → ★ _
    M = Cont T

    module _ {a b} {A : ★ a} {B : ★ b} where
        map : (A → B) → (M A → M B)
        map f mx k = mx λ x → k (f x)

        _>>=_ : M A → (A → M B) → M B
        (mx >>= f) k = mx λ x → (f x) k

    module _ {a} {A : ★ a} where
        return : A → M A
        return x k = k x

        join : M (M A) → M A
        join mmx = mmx >>= id

        module _ {b} {B : ★ b} where
            _⊛_ : M (A → B) → M A → M B
            mf ⊛ mx = mf >>= λ f → map f mx

        module _ {b} {B : A → ★ b} where
            _⟨,⟩_ : M A → (∀ {x} → M (B x)) → M (Σ A B)
            (fA ⟨,⟩ fB) f = fA (fB ∘ curry f)

        module _ {b} {B : ★ b} where
            _⟨,⟩′_ : M A → M B → M (A × B)
            mx ⟨,⟩′ my = mx ⟨,⟩ my

    module _ {a b c} {A : ★ a} {B : ★ b} {C : ★ c} where
        ⟪_·_·_⟫ : (A → B → C) → M A → M B → M C
        ⟪ f · mx · my ⟫ = map f mx ⊛ my
