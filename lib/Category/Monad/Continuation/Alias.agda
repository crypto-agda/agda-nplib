open import Level
open import Type -- hiding (★)
open import Function
open import Data.Product hiding (map)

module Category.Monad.Continuation.Alias {t} (T : ★_ t) where 

Cont : ∀ {a} → ★_ a → ★_ _
Cont A = (A → T) → T 

module _ {a b} {A : ★_ a} {B : ★_ b} where
    map : (A → B) → (Cont A → Cont B)
    map f mx k = mx λ x → k (f x)

    _>>=_ : Cont A → (A → Cont B) → Cont B
    (mx >>= f) k = mx λ x → (f x) k

module _ {a} {A : ★_ a} where
    return : A → Cont A
    return x k = k x

    join : Cont (Cont A) → Cont A
    join mmx = mmx >>= id

    module _ {b} {B : ★_ b} where
        _⊛_ : Cont (A → B) → Cont A → Cont B
        mf ⊛ mx = mf >>= λ f → map f mx

    module _ {b} {B : A → ★_ b} where
        _⟨,⟩_ : Cont A → (∀ {x} → Cont (B x)) → Cont (Σ A B)
        (fA ⟨,⟩ fB) f = fA (fB ∘ curry f)

    module _ {b} {B : ★_ b} where
        _⟨,⟩′_ : Cont A → Cont B → Cont (A × B)
        mx ⟨,⟩′ my = mx ⟨,⟩ my

module _ {a b c} {A : ★_ a} {B : ★_ b} {C : ★_ c} where
    ⟪_·_·_⟫ : (A → B → C) → Cont A → Cont B → Cont C
    ⟪ f · mx · my ⟫ = map f mx ⊛ my
