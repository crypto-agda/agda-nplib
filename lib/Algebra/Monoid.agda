open import Function.NP
open import Data.Product.NP
open import Data.Nat
  using    (ℕ; zero)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; suc to 1+_)
open import Data.Integer
  using    (ℤ; +_; -[1+_]; _⊖_)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Relation.Binary.PropositionalEquality.NP renaming (_∙_ to _♦_)
open import Algebra.FunctionProperties.Eq
open ≡-Reasoning

module Algebra.Monoid where

record Monoid-Ops {ℓ} (M : Set ℓ) : Set ℓ where
  constructor mk
  infixl 7 _∙_

  field
    _∙_ : M → M → M
    ε   : M

  _^⁺_ : M → ℕ → M
  x ^⁺ n = nest n (_∙_ x) ε

  module FromInverseOp
         (_⁻¹   : Op₁ M)
         where
    infixl 7 _/_

    _/_ : M → M → M
    x / y = x ∙ y ⁻¹

    open FromOp₂ _/_ public renaming (op= to /=)

    _^⁻_ _^⁻′_ : M → ℕ → M
    x ^⁻ n = (x ^⁺ n)⁻¹
    x ^⁻′ n = (x ⁻¹)^⁺ n

    _^_ : M → ℤ → M
    x ^ -[1+ n ] = x ^⁻(1+ n)
    x ^ (+ n)    = x ^⁺ n

record Monoid-Struct {ℓ} {M : Set ℓ} (mon-ops : Monoid-Ops M) : Set ℓ where
  open Monoid-Ops mon-ops

  -- laws
  field
    assoc    : Associative _∙_
    identity : Identity  ε _∙_

  open FromOp₂ _∙_ public renaming (op= to ∙=)
  open FromAssoc _∙_ assoc public

  module _ {b} where
    ^⁺0-ε : b ^⁺ 0 ≡ ε
    ^⁺0-ε = idp

    ^⁺1-id : b ^⁺ 1 ≡ b
    ^⁺1-id = snd identity

    ^⁺2-∙ : b ^⁺ 2 ≡ b ∙ b
    ^⁺2-∙ = ap (_∙_ _) ^⁺1-id

    ^⁺-+ : ∀ m {n} → b ^⁺ (m +ℕ n) ≡ b ^⁺ m ∙ b ^⁺ n
    ^⁺-+ 0      = ! fst identity
    ^⁺-+ (1+ m) = ap (_∙_ b) (^⁺-+ m) ♦ ! assoc

    ^⁺-* : ∀ m {n} → b ^⁺(m *ℕ n) ≡ (b ^⁺ n)^⁺ m
    ^⁺-* 0 = idp
    ^⁺-* (1+ m) {n}
      = b ^⁺ (n +ℕ m *ℕ n)     ≡⟨ ^⁺-+ n ⟩
        b ^⁺ n ∙ b ^⁺(m *ℕ n)  ≡⟨ ap (_∙_ (b ^⁺ n)) (^⁺-* m) ⟩
        b ^⁺ n ∙ (b ^⁺ n)^⁺ m  ∎

  comm-ε : ∀ {x} → x ∙ ε ≡ ε ∙ x
  comm-ε = snd identity ♦ ! fst identity

  module _ {c x y} (e : (x ∙ y) ≡ ε) where
    elim-assoc= : (c ∙ x) ∙ y ≡ c
    elim-assoc= = assoc ♦ ∙= idp e ♦ snd identity

    elim-!assoc= : x ∙ (y ∙ c) ≡ c
    elim-!assoc= = ! assoc ♦ ∙= e idp ♦ fst identity

  module _ {c d x y} (e : (x ∙ y) ≡ ε) where
    elim-inner= : (c ∙ x) ∙ (y ∙ d) ≡ c ∙ d
    elim-inner= = assoc ♦ ap (_∙_ c) (elim-!assoc= e)

  module FromLeftInverse
         (_⁻¹   : Op₁ M)
         (inv-l : LeftInverse ε _⁻¹ _∙_)
         where
    open FromInverseOp _⁻¹

    cancels-∙-left : LeftCancel _∙_
    cancels-∙-left {c} {x} {y} e
      = x              ≡⟨ ! fst identity ⟩
        ε ∙ x          ≡⟨ ∙= (! inv-l) idp ⟩
        c ⁻¹ ∙ c ∙ x   ≡⟨ !assoc= e ⟩
        c ⁻¹ ∙ c ∙ y   ≡⟨ ∙= inv-l idp ⟩
        ε ∙ y          ≡⟨ fst identity ⟩
        y ∎

    inv-r : RightInverse ε _⁻¹ _∙_
    inv-r = cancels-∙-left (! assoc ♦ ∙= inv-l idp ♦ ! comm-ε)

    /-∙ : ∀ {x y} → x ≡ (x / y) ∙ y
    /-∙ {x} {y}
      = x               ≡⟨ ! snd identity ⟩
        x ∙ ε           ≡⟨ ap (_∙_ x) (! inv-l) ⟩
        x ∙ (y ⁻¹ ∙ y)  ≡⟨ ! assoc ⟩
        (x / y) ∙ y     ∎

  module FromRightInverse
         (_⁻¹   : Op₁ M)
         (inv-r : RightInverse ε _⁻¹ _∙_)
         where
    open FromInverseOp _⁻¹

    cancels-∙-right : RightCancel _∙_
    cancels-∙-right {c} {x} {y} e
      = x              ≡⟨ ! snd identity ⟩
        x ∙ ε          ≡⟨ ∙= idp (! inv-r) ⟩
        x ∙ (c ∙ c ⁻¹) ≡⟨ assoc= e ⟩
        y ∙ (c ∙ c ⁻¹) ≡⟨ ∙= idp inv-r ⟩
        y ∙ ε          ≡⟨ snd identity ⟩
        y ∎

    inv-l : LeftInverse ε _⁻¹ _∙_
    inv-l = cancels-∙-right (assoc ♦ ∙= idp inv-r ♦ comm-ε)

    module _ {x y} where
      is-ε-left : x ≡ ε → x ∙ y ≡ y
      is-ε-left e = ap (λ z → z ∙ _) e ♦ fst identity

      is-ε-right : y ≡ ε → x ∙ y ≡ x
      is-ε-right e = ap (λ z → _ ∙ z) e ♦ snd identity

      ∙-/ : x ≡ (x ∙ y) / y
      ∙-/
        = x            ≡⟨ ! snd identity ⟩
          x ∙ ε        ≡⟨ ap (_∙_ x) (! inv-r) ⟩
          x ∙ (y / y)  ≡⟨ ! assoc ⟩
          (x ∙ y) / y  ∎

    module _ {x y} where
      unique-ε-left : x ∙ y ≡ y → x ≡ ε
      unique-ε-left eq
        = x            ≡⟨ ∙-/ ⟩
          (x ∙ y) / y  ≡⟨ /= eq idp ⟩
          y / y        ≡⟨ inv-r ⟩
          ε            ∎

      unique-ε-right : x ∙ y ≡ x → y ≡ ε
      unique-ε-right eq
        = y               ≡⟨ ! is-ε-left inv-l ⟩
          x ⁻¹ ∙  x ∙ y   ≡⟨ assoc ⟩
          x ⁻¹ ∙ (x ∙ y)  ≡⟨ ∙= idp eq ⟩
          x ⁻¹ ∙ x        ≡⟨ inv-l ⟩
          ε               ∎

      unique-⁻¹ : x ∙ y ≡ ε → x ≡ y ⁻¹
      unique-⁻¹ eq
        = x            ≡⟨ ∙-/ ⟩
          (x ∙ y) / y  ≡⟨ /= eq idp ⟩
          ε / y        ≡⟨ fst identity ⟩
          y ⁻¹         ∎

    open FromLeftInverse _⁻¹ inv-l hiding (inv-r)

    ε⁻¹-ε : ε ⁻¹ ≡ ε
    ε⁻¹-ε = unique-ε-left inv-l

    involutive : Involutive _⁻¹
    involutive {x}
      = cancels-∙-right
        (x ⁻¹ ⁻¹ ∙ x ⁻¹ ≡⟨ inv-l ⟩
         ε              ≡⟨ ! inv-r ⟩
         x ∙ x ⁻¹ ∎)

    ⁻¹-hom′ : ∀ {x y} → (x ∙ y)⁻¹ ≡ y ⁻¹ ∙ x ⁻¹
    ⁻¹-hom′ {x} {y} = cancels-∙-left {x ∙ y}
       ((x ∙ y) ∙ (x ∙ y)⁻¹     ≡⟨ inv-r ⟩
        ε                       ≡⟨ ! inv-r ⟩
        x ∙ x ⁻¹                ≡⟨ ap (_∙_ x) (! fst identity) ⟩
        x ∙ (ε ∙ x ⁻¹)          ≡⟨ ∙= idp (∙= (! inv-r) idp) ⟩
        x ∙ ((y ∙ y ⁻¹) ∙ x ⁻¹) ≡⟨ ap (_∙_ x) assoc ⟩
        x ∙ (y ∙ (y ⁻¹ ∙ x ⁻¹)) ≡⟨ ! assoc ⟩
        (x ∙ y) ∙ (y ⁻¹ ∙ x ⁻¹) ∎)

    elim-∙-left-⁻¹∙ : ∀ {c x y} → (c ∙ x)⁻¹ ∙ (c ∙ y) ≡ x ⁻¹ ∙ y
    elim-∙-left-⁻¹∙ {c} {x} {y}
      = (c ∙ x)⁻¹   ∙ (c ∙ y)  ≡⟨ ∙= ⁻¹-hom′ idp ⟩
        x ⁻¹ ∙ c ⁻¹ ∙ (c ∙ y)  ≡⟨ elim-inner= inv-l ⟩
        x ⁻¹ ∙ y               ∎

    elim-∙-right-/ : ∀ {c x y} → (x ∙ c) / (y ∙ c) ≡ x / y
    elim-∙-right-/ {c} {x} {y}
      = x ∙ c ∙ (y ∙ c)⁻¹  ≡⟨ ap (_∙_ _) ⁻¹-hom′  ⟩
        x ∙ c ∙ (c ⁻¹ / y) ≡⟨ elim-inner= inv-r ⟩
        x / y ∎ 

    module _ {b} where
      ^⁺suc : ∀ n → b ^⁺(1+ n) ≡ b ^⁺ n ∙ b
      ^⁺suc 0 = comm-ε
      ^⁺suc (1+ n) = ap (_∙_ b) (^⁺suc n) ♦ ! assoc

      ^⁺-comm : ∀ n → b ∙ b ^⁺ n ≡ b ^⁺ n ∙ b
      ^⁺-comm = ^⁺suc

      ^⁻suc : ∀ n → b ^⁻(1+ n) ≡ b ⁻¹ ∙ b ^⁻ n
      ^⁻suc n = ap _⁻¹ (^⁺suc n) ♦ ⁻¹-hom′

      ^⁻′-spec : ∀ n → b ^⁻′ n ≡ b ^⁻ n
      ^⁻′-spec 0 = ! ε⁻¹-ε
      ^⁻′-spec (1+ n) = ap (_∙_ (b ⁻¹)) (^⁻′-spec n)
                      ♦ ! ⁻¹-hom′
                      ♦ ap _⁻¹ (! ^⁺suc n)

      ^⁻′1-id : b ^⁻′ 1 ≡ b ⁻¹
      ^⁻′1-id = snd identity

      ^⁻1-id : b ^⁻ 1 ≡ b ⁻¹
      ^⁻1-id = ! ^⁻′-spec 1 ♦ ^⁻′1-id

      ^⁻′2-∙ : b ^⁻′ 2 ≡ b ⁻¹ ∙ b ⁻¹
      ^⁻′2-∙ = ap (_∙_ _) ^⁻′1-id

      ^⁻2-∙ : b ^⁻ 2 ≡ b ⁻¹ ∙ b ⁻¹
      ^⁻2-∙ = ! ^⁻′-spec 2 ♦ ^⁻′2-∙

record Monoid (M : Set) : Set where
  field
    mon-ops    : Monoid-Ops M
    mon-struct : Monoid-Struct mon-ops
  open Monoid-Ops    mon-ops    public
  open Monoid-Struct mon-struct public

record Commutative-Monoid-Struct {ℓ} {M : Set ℓ} (mon-ops : Monoid-Ops M) : Set ℓ where
  open Monoid-Ops mon-ops
  field
    mon-struct : Monoid-Struct mon-ops
    comm : Commutative _∙_
  open Monoid-Struct mon-struct public
  open FromAssocComm _∙_ assoc comm public
    hiding (!assoc=; assoc=; inner=)

record Commutative-Monoid (M : Set) : Set where
  field
    mon-ops    : Monoid-Ops M
    mon-comm   : Commutative-Monoid-Struct mon-ops
  open Monoid-Ops    mon-ops    public
  open Commutative-Monoid-Struct mon-comm public
  mon : Monoid M
  mon = record { mon-struct = mon-struct }

-- A renaming of Monoid with additive notation
module Additive-Monoid {M} (mon : Monoid M) = Monoid mon
    renaming ( _∙_ to _+_; ε to 0ᵐ
             ; assoc to +-assoc; identity to +-identity
             ; ∙= to +=
             )

-- A renaming of Monoid with multiplicative notation
module Multiplicative-Monoid {M} (mon : Monoid M) = Monoid mon
    renaming ( _∙_ to _*_; ε to 1ᵐ
             ; assoc to *-assoc; identity to *-identity
             ; ∙= to *=
             )

module Additive-Commutative-Monoid {M} (mon-comm : Commutative-Monoid M)
  = Commutative-Monoid mon-comm
    renaming ( _∙_ to _+_; ε to 0ᵐ
             ; assoc to +-assoc; identity to +-identity
             ; ∙= to +=
             ; assoc= to +-assoc=
             ; !assoc= to +-!assoc=
             ; inner= to +-inner=
             ; assoc-comm to +-assoc-comm
             ; interchange to +-interchange
             ; outer= to +-outer=
             )

module Multiplicative-Commutative-Monoid {M} (mon : Commutative-Monoid M) = Commutative-Monoid mon
    renaming ( _∙_ to _*_; ε to 1ᵐ
             ; assoc to *-assoc; identity to *-identity
             ; ∙= to *=
             ; assoc= to *-assoc=
             ; !assoc= to *-!assoc=
             ; inner= to *-inner=
             ; assoc-comm to *-assoc-comm
             ; interchange to *-interchange
             ; outer= to *-outer=
             )

record MonoidHomomorphism {A B : Set}
                          (monA0+ : Monoid A)
                          (monB1* : Monoid B)
                          (f : A → B) : Set where
  open Additive-Monoid monA0+
  open Multiplicative-Monoid monB1*
  field
    0-hom-1 : f 0ᵐ ≡ 1ᵐ
    +-hom-* : ∀ {x y} → f (x + y) ≡ f x * f y
-- -}
-- -}
-- -}
-- -}
