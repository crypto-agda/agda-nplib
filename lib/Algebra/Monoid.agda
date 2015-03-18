{-# OPTIONS --without-K #-}
open import Type using () renaming (Type_ to Type)
open import Level.NP
open import Function.NP
open import Data.Product.NP
open import Data.Nat
  using    (ℕ; zero)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; suc to 1+_)
import Data.Nat.Properties.Simple as ℕ°
open import Data.Integer.NP
  using    (ℤ; +_; -[1+_]; _⊖_; -_; module ℤ°)
  renaming ( _+_ to _+ℤ_; _-_ to _−ℤ_; _*_ to _*ℤ_
           ; suc to sucℤ; pred to predℤ
           )
open import Relation.Binary.PropositionalEquality.NP renaming (_∙_ to _♦_)
open import Algebra.FunctionProperties.Eq
open ≡-Reasoning

module Algebra.Monoid where

record Monoid-Ops {ℓ} (M : Type ℓ) : Type ℓ where
  constructor _,_
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

record Monoid-Struct {ℓ} {M : Type ℓ} (mon-ops : Monoid-Ops M) : Type ℓ where
  constructor _,_
  open Monoid-Ops mon-ops

  -- laws
  field
    assocs   : Associative _∙_ × Associative (flip _∙_)
    identity : Identity  ε _∙_

  assoc = fst assocs
  !assoc = snd assocs

  open FromOp₂ _∙_ public renaming (op= to ∙=)
  open FromAssoc _∙_ assoc public hiding (assocs)

  module _ {b} where
    ^⁺0-ε : b ^⁺ 0 ≡ ε
    ^⁺0-ε = idp

    ^⁺1-id : b ^⁺ 1 ≡ b
    ^⁺1-id = snd identity

    ^⁺2-∙ : b ^⁺ 2 ≡ b ∙ b
    ^⁺2-∙ = ap (_∙_ _) ^⁺1-id

    -- Together with ^⁺0-ε, ^⁺-+ shows that (b ^⁺_) is a
    -- monoid homomorphism from (ℕ,+,0) to (M,∙,ε)
    -- therefore also a group homomorphism
    ^⁺-+ : ∀ m {n} → b ^⁺ (m +ℕ n) ≡ b ^⁺ m ∙ b ^⁺ n
    ^⁺-+ 0      = ! fst identity
    ^⁺-+ (1+ m) = ap (_∙_ b) (^⁺-+ m) ♦ ! assoc

    -- Derived from ^⁺-+ in Algebra.Group
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

    ⁻¹-involutive : Involutive _⁻¹
    ⁻¹-involutive {x}
      = cancels-∙-right
        (x ⁻¹ ⁻¹ ∙ x ⁻¹ ≡⟨ inv-l ⟩
         ε              ≡⟨ ! inv-r ⟩
         x ∙ x ⁻¹ ∎)

    -- _⁻¹ is a group homomorphism, see Algebra.Group._ᵒᵖ
    ⁻¹-hom′ : ∀ {x y} → (x ∙ y)⁻¹ ≡ y ⁻¹ ∙ x ⁻¹
    ⁻¹-hom′ {x} {y} = cancels-∙-left {x ∙ y}
       ((x ∙ y) ∙ (x ∙ y)⁻¹     ≡⟨ inv-r ⟩
        ε                       ≡⟨ ! inv-r ⟩
        x ∙ x ⁻¹                ≡⟨ ap (_∙_ x) (! fst identity) ⟩
        x ∙ (ε ∙ x ⁻¹)          ≡⟨ ∙= idp (∙= (! inv-r) idp) ⟩
        x ∙ ((y ∙ y ⁻¹) ∙ x ⁻¹) ≡⟨ ap (_∙_ x) assoc ⟩
        x ∙ (y ∙ (y ⁻¹ ∙ x ⁻¹)) ≡⟨ ! assoc ⟩
        (x ∙ y) ∙ (y ⁻¹ ∙ x ⁻¹) ∎)

    ⁻¹-hom′= : ∀ {x y z t} → x ∙ y ≡ z ∙ t → y ⁻¹ ∙ x ⁻¹ ≡ t ⁻¹ ∙ z ⁻¹
    ⁻¹-hom′= e = ! ⁻¹-hom′ ♦ ap _⁻¹ e ♦ ⁻¹-hom′

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
      ^⁺-1+ : ∀ n → b ^⁺(1+ n) ≡ b ^⁺ n ∙ b
      ^⁺-1+ 0 = comm-ε
      ^⁺-1+ (1+ n) = ap (_∙_ b) (^⁺-1+ n) ♦ ! assoc

      ^-⊖ : ∀ m n → b ^(m ⊖ n) ≡ b ^⁺ m ∙ b ^⁻ n
      ^-⊖ m      0      = ! is-ε-right ε⁻¹-ε
      ^-⊖ 0      (1+ n) = ! fst identity
      ^-⊖ (1+ m) (1+ n) =
         b ^(m ⊖ n)                      ≡⟨ ^-⊖ m n ⟩
         (b ^⁺ m ∙ b ^⁻ n)               ≡⟨ ! elim-inner= inv-r ⟩
         (b ^⁺ m ∙ b) ∙ (b ⁻¹ ∙ b ^⁻ n)  ≡⟨ ∙= idp (! ⁻¹-hom′) ⟩
         (b ^⁺ m ∙ b) ∙ (b ^⁺ n ∙ b)⁻¹   ≡⟨ ∙= (! ^⁺-1+ m) (ap _⁻¹ (! ^⁺-1+ n)) ⟩
         (b ∙ b ^⁺ m) ∙ (b ∙ b ^⁺ n)⁻¹   ∎

      ^-⊖' : ∀ m n → b ^(m ⊖ n) ≡ b ^⁻ n ∙ b ^⁺ m
      ^-⊖' m      0      = ! is-ε-left ε⁻¹-ε
      ^-⊖' 0      (1+ n) = ! snd identity
      ^-⊖' (1+ m) (1+ n) =
         b ^(m ⊖ n)                      ≡⟨ ^-⊖' m n ⟩
         (b ^⁻ n ∙ b ^⁺ m)               ≡⟨ ! elim-inner= inv-l ⟩
         (b ^⁻ n ∙ b ⁻¹) ∙ (b ∙ b ^⁺ m)  ≡⟨ ∙= (! ⁻¹-hom′) idp ⟩
         (b ∙ b ^⁺ n)⁻¹ ∙ (b ∙ b ^⁺ m)   ∎

      ^⁺-comm : ∀ m n → b ^⁺ m ∙ b ^⁺ n ≡ b ^⁺ n ∙ b ^⁺ m
      ^⁺-comm 0      n = ! comm-ε
      ^⁺-comm (1+ m) n =
        b ∙ bᵐ ∙ bⁿ   ≡⟨ !assoc= (^⁺-comm m n) ⟩
        b ∙ bⁿ ∙ bᵐ   ≡⟨ ∙= (^⁺-1+ n) idp ⟩
        bⁿ ∙ b ∙ bᵐ   ≡⟨ assoc ⟩
        bⁿ ∙ (b ∙ bᵐ) ∎
        where
          bⁿ = b ^⁺ n
          bᵐ = b ^⁺ m

      ^⁺-^⁻-comm : ∀ m n → b ^⁺ m ∙ b ^⁻ n ≡ b ^⁻ n ∙ b ^⁺ m
      ^⁺-^⁻-comm m n = ! ^-⊖ m n ♦ ^-⊖' m n

      ^⁻-^⁺-comm : ∀ m n → b ^⁻ n ∙ b ^⁺ m ≡ b ^⁺ m ∙ b ^⁻ n
      ^⁻-^⁺-comm m n = ! ^-⊖' m n ♦ ^-⊖ m n

      ^⁻-comm : ∀ m n → b ^⁻ m ∙ b ^⁻ n ≡ b ^⁻ n ∙ b ^⁻ m
      ^⁻-comm m n = ⁻¹-hom′= (^⁺-comm n m)

      ^⁻-1+ : ∀ n → b ^⁻(1+ n) ≡ b ⁻¹ ∙ b ^⁻ n
      ^⁻-1+ n = ap _⁻¹ (^⁺-1+ n) ♦ ⁻¹-hom′

      ^⁻′-spec : ∀ n → b ^⁻′ n ≡ b ^⁻ n
      ^⁻′-spec 0 = ! ε⁻¹-ε
      ^⁻′-spec (1+ n) = ap (_∙_ (b ⁻¹)) (^⁻′-spec n)
                      ♦ ! ⁻¹-hom′
                      ♦ ap _⁻¹ (! ^⁺-1+ n)

      ^⁻′1-id : b ^⁻′ 1 ≡ b ⁻¹
      ^⁻′1-id = snd identity

      ^⁻1-id : b ^⁻ 1 ≡ b ⁻¹
      ^⁻1-id = ! ^⁻′-spec 1 ♦ ^⁻′1-id

      ^⁻′2-∙ : b ^⁻′ 2 ≡ b ⁻¹ ∙ b ⁻¹
      ^⁻′2-∙ = ap (_∙_ _) ^⁻′1-id

      ^⁻2-∙ : b ^⁻ 2 ≡ b ⁻¹ ∙ b ⁻¹
      ^⁻2-∙ = ! ^⁻′-spec 2 ♦ ^⁻′2-∙

      -- ^-+ is a group homomorphism defined in Algebra.Group
      -- Some properties can be derived from it.
      ^-+ : ∀ i j → b ^(i +ℤ j) ≡ b ^ i ∙ b ^ j
      ^-+ -[1+ m ] -[1+ n ] = ap _⁻¹
                               (ap (λ z → b ^⁺(1+ z)) (ℕ°.+-comm (1+ m) n)
                            ♦ ^⁺-+ {b} (1+ n) {1+ m}) ♦ ⁻¹-hom′
      ^-+ -[1+ m ]   (+ n)  = ^-⊖' n (1+ m)
      ^-+   (+ m)  -[1+ n ] = ^-⊖ m (1+ n)
      ^-+   (+ m)    (+ n)  = ^⁺-+ m

      -- GroupHomomorphism.f-pres-inv
      ^-- : ∀ i → b ^(- i) ≡ (b ^ i)⁻¹
      ^-- -[1+ n ] = ! ⁻¹-involutive
      ^-- (+ 0)    = ! ε⁻¹-ε
      ^-- (+ 1+ n) = idp

      -- GroupHomomorphism.f-−-/
      ^-− : ∀ i j → b ^(i −ℤ j) ≡ b ^ i / b ^ j
      ^-− i j = ^-+ i (- j) ♦ ∙= idp (^-- j)

      ^-suc : ∀ i → b ^(sucℤ i) ≡ b ∙ b ^ i
      ^-suc i = ^-+ (+ 1) i ♦ ∙= (snd identity) idp

      ^-pred : ∀ i → b ^(predℤ i) ≡ b ⁻¹ ∙ b ^ i
      ^-pred i = ^-+ (- + 1) i ♦ ap (λ z → z ⁻¹ ∙ b ^ i) (snd identity)

      ^-comm : ∀ i j → b ^ i ∙ b ^ j ≡ b ^ j ∙ b ^ i
      ^-comm -[1+ m ] -[1+ n ] = ^⁻-comm (1+ m) (1+ n)
      ^-comm -[1+ m ]   (+ n)  = ! ^⁺-^⁻-comm n (1+ m)
      ^-comm   (+ m)  -[1+ n ] = ^⁺-^⁻-comm m (1+ n)
      ^-comm   (+ m)    (+ n)  = ^⁺-comm m n

{-
      ^-* : ∀ i j → b ^(i *ℤ j) ≡ (b ^ j)^ i
      ^-* i j = {!!}
      -}

record Monoid {ℓ}(M : Type ℓ) : Type ℓ where
  constructor _,_
  field
    mon-ops    : Monoid-Ops M
    mon-struct : Monoid-Struct mon-ops
  open Monoid-Ops    mon-ops    public
  open Monoid-Struct mon-struct public

record Commutative-Monoid-Struct {ℓ} {M : Type ℓ} (mon-ops : Monoid-Ops M) : Type ℓ where
  constructor _,_
  open Monoid-Ops mon-ops
  field
    mon-struct : Monoid-Struct mon-ops
    comm : Commutative _∙_
  open Monoid-Struct mon-struct public
  open FromAssocComm _∙_ assoc comm public
    hiding (!assoc=; assoc=; inner=; assocs)

record Commutative-Monoid {ℓ}(M : Type ℓ) : Type ℓ where
  constructor _,_
  field
    mon-ops    : Monoid-Ops M
    mon-comm   : Commutative-Monoid-Struct mon-ops
  open Monoid-Ops    mon-ops    public
  open Commutative-Monoid-Struct mon-comm public
  mon : Monoid M
  mon = record { mon-struct = mon-struct }

-- A renaming of Monoid with additive notation
module Additive-Monoid {ℓ}{M : Type ℓ} (mon : Monoid M) = Monoid mon
    renaming ( _∙_ to _+_; ε to 0ᵐ
             ; assoc to +-assoc; identity to +-identity
             ; !assoc to +-!assoc
             ; ∙= to +=
             ; _^⁺_ to _⊗⁺_
             )

-- A renaming of Monoid with multiplicative notation
module Multiplicative-Monoid {ℓ}{M : Type ℓ} (mon : Monoid M) = Monoid mon
    renaming ( _∙_ to _*_; ε to 1ᵐ
             ; assoc to *-assoc; identity to *-identity
             ; !assoc to *-!assoc
             ; ∙= to *=
             )

module Additive-Commutative-Monoid {ℓ}{M : Type ℓ} (mon-comm : Commutative-Monoid M)
  = Commutative-Monoid mon-comm
    renaming ( _∙_ to _+_; ε to 0ᵐ
             ; assoc to +-assoc; identity to +-identity
             ; !assoc to +-!assoc
             ; ∙= to +=
             ; assoc= to +-assoc=
             ; !assoc= to +-!assoc=
             ; inner= to +-inner=
             ; assoc-comm to +-assoc-comm
             ; interchange to +-interchange
             ; outer= to +-outer=
             )

module Multiplicative-Commutative-Monoid
     {ℓ}{M : Type ℓ} (mon : Commutative-Monoid M) = Commutative-Monoid mon
    renaming ( _∙_ to _*_; ε to 1ᵐ
             ; assoc to *-assoc; identity to *-identity
             ; !assoc to *-!assoc
             ; ∙= to *=
             ; assoc= to *-assoc=
             ; !assoc= to *-!assoc=
             ; inner= to *-inner=
             ; assoc-comm to *-assoc-comm
             ; interchange to *-interchange
             ; outer= to *-outer=
             )

record MonoidHomomorphism {a}{A : Type a}{b}{B : Type b}
                          (monA0+ : Monoid A)
                          (monB1* : Monoid B)
                          (f : A → B) : Type(a ⊔ b) where
  constructor _,_
  open Additive-Monoid monA0+
  open Multiplicative-Monoid monB1*
  field
    0-hom-1 : f 0ᵐ ≡ 1ᵐ
    +-hom-* : ∀ {x y} → f (x + y) ≡ f x * f y

  hom-iterated⁺ : ∀ {x} n → f (x ⊗⁺ n) ≡ f x ^⁺ n
  hom-iterated⁺ 0      = 0-hom-1
  hom-iterated⁺ (1+ n) = +-hom-* ♦ *= idp (hom-iterated⁺ n)

module Monoidᵒᵖ {ℓ}{M : Type ℓ} where
  _ᵒᵖ-ops : Monoid-Ops M → Monoid-Ops M
  (_∙_ , ε) ᵒᵖ-ops = flip _∙_ , ε

  _ᵒᵖ-struct : {mon : Monoid-Ops M} → Monoid-Struct mon → Monoid-Struct (mon ᵒᵖ-ops)
  (assocs , identities) ᵒᵖ-struct = (swap assocs , swap identities)

  _ᵒᵖ : Monoid M → Monoid M
  (ops , struct)ᵒᵖ = _ , struct ᵒᵖ-struct

  ᵒᵖ∘ᵒᵖ-id : ∀ {mon} → (mon ᵒᵖ) ᵒᵖ ≡ mon
  ᵒᵖ∘ᵒᵖ-id = idp

module _ {a}{A : Type a}(_∙_ : Op₂ A)(assoc : Associative _∙_) where
  from-assoc = FromAssoc.assocs _∙_ assoc

ℕ+-mon-ops : Monoid-Ops ℕ
ℕ+-mon-ops = _+ℕ_ , 0

ℕ+-mon-struct : Monoid-Struct ℕ+-mon-ops
ℕ+-mon-struct = from-assoc _+ℕ_ (λ {x}{y}{z} → ℕ°.+-assoc x y z)
              , ((λ{x} → idp) , (λ{x} → ℕ°.+-right-identity x))

ℕ+-mon : Monoid ℕ
ℕ+-mon = ℕ+-mon-ops , ℕ+-mon-struct

module ℕ+-mon = Additive-Monoid ℕ+-mon

ℕ*-mon-ops : Monoid-Ops ℕ
ℕ*-mon-ops = _*ℕ_ , 1

ℕ*-mon-struct : Monoid-Struct ℕ*-mon-ops
ℕ*-mon-struct = (from-assoc _*ℕ_ (λ {x}{y}{z} → ℕ°.*-assoc x y z))
              , ( (λ{x} → ℕ°.+-comm x 0)
                , (λ{x} → ℕ°.*-comm x 1 ♦ ℕ°.+-comm x 0))

ℕ*-mon : Monoid ℕ
ℕ*-mon = _ , ℕ*-mon-struct

module ℕ*-mon = Multiplicative-Monoid ℕ*-mon

ℤ+-mon-ops : Monoid-Ops ℤ
ℤ+-mon-ops = _+ℤ_ , + 0

ℤ+-mon-struct : Monoid-Struct ℤ+-mon-ops
ℤ+-mon-struct = (from-assoc _+ℤ_ (λ {x}{y}{z} → ℤ°.+-assoc x y z))
              , (λ{x} → fst ℤ°.+-identity x)
              , (λ{x} → snd ℤ°.+-identity x)

ℤ+-mon : Monoid ℤ
ℤ+-mon = _ , ℤ+-mon-struct

module ℤ+-mon = Additive-Monoid ℤ+-mon

module MonoidHomomorphism^ {ℓ}{M : Type ℓ} (mon : Monoid M) where
  open Monoid mon

  ^⁺-hom : ∀ {b} → MonoidHomomorphism ℕ+-mon mon (_^⁺_ b)
  ^⁺-hom = idp , λ {x}{y} → ^⁺-+ x

--import Data.Vec.NP as V
{-
module _ {A B : Type} where
  (f : Vec  : Vec M n) → f ⊛ x (∀ i → )

module VecMonoid {M : Type} (mon : Monoid M) where
  open V
  open Monoid mon

  module _ n where
    ×-mon-ops : Monoid-Ops (Vec M n)
    ×-mon-ops = zipWith _∙_ , replicate ε

    ×-mon-struct : Monoid-Struct ×-mon-ops
    ×-mon-struct = (λ {x}{y}{z} → {!replicate ? ⊛ ?!}) , {!!} , {!!}
-}

module MonoidProduct {a}{A : Type a}{b}{B : Type b}
                     (monA0+ : Monoid A)(monB1* : Monoid B) where
  open Additive-Monoid monA0+
  open Multiplicative-Monoid monB1*

  ×-mon-ops    : Monoid-Ops (A × B)
  ×-mon-ops    = zip _+_ _*_ , 0ᵐ , 1ᵐ

  ×-mon-struct : Monoid-Struct ×-mon-ops
  ×-mon-struct = (ap₂ _,_ +-assoc *-assoc , ap₂ _,_ +-!assoc *-!assoc)
               , ap₂ _,_ (fst +-identity) (fst *-identity)
               , ap₂ _,_ (snd +-identity) (snd *-identity)

  ×-mon : Monoid (A × B)
  ×-mon = ×-mon-ops , ×-mon-struct

  open Monoid ×-mon public
-- -}
-- -}
-- -}
-- -}
