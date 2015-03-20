{-# OPTIONS --without-K #-}
-- Like Algebra.FunctionProperties but specialized to _≡_
-- Using implict arguments for derived definitions

-- These properties can (for instance) be used to define algebraic
-- structures.

open import Level
open import Function.NP using (_$⟨_⟩_; flip; Π; Πⁱ; Op₁; Op₂; nest)
open import Data.Nat.Base using (ℕ)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; suc to 1+_)
import Data.Nat.Properties.Simple as ℕ°
open import Data.Integer.NP
  using    (ℤ; +_; -[1+_]; _⊖_; -_; module ℤ°)
  renaming ( _+_ to _+ℤ_; _-_ to _−ℤ_; _*_ to _*ℤ_
           ; suc to sucℤ; pred to predℤ
           )
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.NP
open import Relation.Binary.PropositionalEquality.NP renaming (_∙_ to _♦_)
import Algebra.FunctionProperties.NP
open ≡-Reasoning

-- The properties are specified using the following relation as
-- "equality".

module Algebra.FunctionProperties.Eq {a} {A : Set a} where

module Implicits where
  open Algebra.FunctionProperties.NP Πⁱ {a}{a}{A} _≡_ public

  module _ {b}{B : Set b} where
    open Morphisms {B = B} _≡_ public

    module _ {f : A → B} where
      Injective-¬Conflict : Injective f → ¬(Conflict f)
      Injective-¬Conflict inj (x , y , x≢y , fx≡fy) = x≢y (inj fx≡fy)

      Conflict-¬Injective : Conflict f → ¬(Injective f)
      Conflict-¬Injective = flip Injective-¬Conflict

  module FromOp₂ (op : Op₂ A) where

    private
      infixl 6 _∙_
      _∙_ : Op₂ A
      _∙_ = op

    module _ {x x' y y'}(p : x ≡ x')(q : y ≡ y') where
      op= : x ∙ y ≡ x' ∙ y'
      op= = ap (_∙_ x) q ♦ ap (λ z → z ∙ y') p

    private
      ∙= = op=

    infix 8 _^¹⁺_
    _^¹⁺_ : A → ℕ → A
    x ^¹⁺ n = nest n (_∙_ x) x

    module FromComm
             (comm  : Commutative _∙_)
             {x y x' y' : A}
             (e : (y ∙ x) ≡ (y' ∙ x'))
           where
      comm= : x ∙ y ≡ x' ∙ y'
      comm= = comm ♦ e ♦ comm

    module FromAssoc
             (assoc : Associative _∙_)
           where

      assocs : Associative _∙_ × Associative (flip _∙_)
      assocs = assoc , ! assoc

      module _ {c x y x' y' : A}
               (e : (x ∙ y) ≡ (x' ∙ y')) where
        assoc= : x ∙ (y ∙ c) ≡ x' ∙ (y' ∙ c)
        assoc= = ! assoc ♦ op= e idp ♦ assoc

        !assoc= : (c ∙ x) ∙ y ≡ (c ∙ x') ∙ y'
        !assoc= = assoc ♦ op= idp e ♦ ! assoc

      module _ {c d x y x' y' : A}
               (e : (x ∙ y) ≡ (x' ∙ y')) where
        inner= : (c ∙ x) ∙ (y ∙ d) ≡ (c ∙ x') ∙ (y' ∙ d)
        inner= = assoc= (!assoc= e)

    module FromAssocComm
             (assoc : Associative _∙_)
             (comm  : Commutative _∙_)
           where
      open FromAssoc assoc public
      open FromComm  comm  public

      module _ {x y z} where
        assoc-comm : x ∙ (y ∙ z) ≡ y ∙ (x ∙ z)
        assoc-comm = assoc= comm

        !assoc-comm : (x ∙ y) ∙ z ≡ (x ∙ z) ∙ y
        !assoc-comm = !assoc= comm

      interchange : Interchange _∙_ _∙_
      interchange = assoc= (!assoc= comm)

      module _ {c d x y x' y' : A}
               (e : (x ∙ y) ≡ (x' ∙ y')) where
        outer= : (x ∙ c) ∙ (d ∙ y) ≡ (x' ∙ c) ∙ (d ∙ y')
        outer= = ∙= comm comm ♦ assoc= (!assoc= e) ♦ ∙= comm comm

  module FromMonoidOps (ε : A) (op : Op₂ A) where

    private
      infixl 6 _∙_
      _∙_ : Op₂ A
      _∙_ = op

    open FromOp₂ _∙_ renaming (op= to ∙=) -- hiding (module FromAssoc)

    infix 8 _^⁺_
    _^⁺_ : A → ℕ → A
    x ^⁺ n = nest n (_∙_ x) ε

    module FromRightIdentity (idr : RightIdentity ε _∙_) where

      module _ {b} where
        ^⁺-^¹⁺ : ∀ n → b ^⁺ (1+ n) ≡ b ^¹⁺ n
        ^⁺-^¹⁺ 0 = idr
        ^⁺-^¹⁺ (1+ n) = ∙= idp (^⁺-^¹⁺ n)

        ^⁺0-ε : b ^⁺ 0 ≡ ε
        ^⁺0-ε = idp

        ^⁺1-id : b ^⁺ 1 ≡ b
        ^⁺1-id = idr

        ^⁺2-∙ : b ^⁺ 2 ≡ b ∙ b
        ^⁺2-∙ = ^⁺-^¹⁺ 1

        ^⁺3-∙ : b ^⁺ 3 ≡ b ∙ (b ∙ b)
        ^⁺3-∙ = ^⁺-^¹⁺ 2

        ^⁺4-∙ : b ^⁺ 4 ≡ b ∙ (b ∙ (b ∙ b))
        ^⁺4-∙ = ^⁺-^¹⁺ 3

    module FromRightIdentityAssoc
             (idr   : RightIdentity ε _∙_)
             (assoc : Associative _∙_) where
      open FromRightIdentity idr public
      module _ {c x y}(e : x ∙ y ≡ ε) where
        elim-assoc= : (c ∙ x) ∙ y ≡ c
        elim-assoc= = assoc ♦ ∙= idp e ♦ idr

    module FromLeftIdentityAssoc
             (idl : LeftIdentity ε _∙_)
             (assoc : Associative _∙_) where

      -- Together with ^⁺0-ε, ^⁺-+ shows that (b ^⁺_) is a
      -- monoid homomorphism from (ℕ,+,0) to (M,∙,ε)
      -- therefore also a group homomorphism
      ^⁺-+ : ∀ m {n b} → b ^⁺ (m +ℕ n) ≡ b ^⁺ m ∙ b ^⁺ n
      ^⁺-+ 0      = ! idl
      ^⁺-+ (1+ m) = ap (_∙_ _) (^⁺-+ m) ♦ ! assoc

      -- Derived from ^⁺-+ in Algebra.Group
      ^⁺-* : ∀ m {n b} → b ^⁺(m *ℕ n) ≡ (b ^⁺ n)^⁺ m
      ^⁺-* 0 = idp
      ^⁺-* (1+ m) {n} {b}
        = b ^⁺ (n +ℕ m *ℕ n)     ≡⟨ ^⁺-+ n ⟩
          b ^⁺ n ∙ b ^⁺(m *ℕ n)  ≡⟨ ap (_∙_ (b ^⁺ n)) (^⁺-* m) ⟩
          b ^⁺ n ∙ (b ^⁺ n)^⁺ m  ∎

      module _ {c x y} (e : x ∙ y ≡ ε) where
        elim-!assoc= : x ∙ (y ∙ c) ≡ c
        elim-!assoc= = ! assoc ♦ ∙= e idp ♦ idl

      module _ {c d x y} (e : (x ∙ y) ≡ ε) where
        elim-inner= : (c ∙ x) ∙ (y ∙ d) ≡ c ∙ d
        elim-inner= = assoc ♦ ap (_∙_ c) (elim-!assoc= e)

    {-
    module FromIdentitiesAssoc
             (idl : LeftIdentity ε _∙_)
             (idr : RightIdentity ε _∙_)
             (assoc : Associative _∙_) where
      open FromLeftIdentityAssoc  idl assoc public
      open FromRightIdentityAssoc idr assoc public
    -}

    module FromInverseOp
           (_⁻¹   : Op₁ A)
           where
      infixl 7 _/_

      _/_ : A → A → A
      x / y = x ∙ y ⁻¹

      open FromOp₂ _/_ public using () renaming (op= to /=)

      _^⁻_ _^⁻′_ : A → ℕ → A
      x ^⁻ n = (x ^⁺ n)⁻¹
      x ^⁻′ n = (x ⁻¹)^⁺ n

      _^_ : A → ℤ → A
      x ^ -[1+ n ] = x ^⁻(1+ n)
      x ^ (+ n)    = x ^⁺ n

      module FromIdentitiesAssoc
             (idl : LeftIdentity ε _∙_)
             (idr : RightIdentity ε _∙_)
             (assoc : Associative _∙_)
           where
        open FromAssoc assoc
        open FromLeftIdentityAssoc idl assoc

        comm-ε : ∀ {x} → x ∙ ε ≡ ε ∙ x
        comm-ε = idr ♦ ! idl

        module _ {x y} where
          is-ε-left : x ≡ ε → x ∙ y ≡ y
          is-ε-left e = ap (λ z → z ∙ _) e ♦ idl

          is-ε-right : y ≡ ε → x ∙ y ≡ x
          is-ε-right e = ap (λ z → _ ∙ z) e ♦ idr

        module FromLeftInverse (inv-l : LeftInverse ε _⁻¹ _∙_) where
          cancels-∙-left : LeftCancel _∙_
          cancels-∙-left {c} {x} {y} e
            = x              ≡⟨ ! idl ⟩
              ε ∙ x          ≡⟨ ∙= (! inv-l) idp ⟩
              c ⁻¹ ∙ c ∙ x   ≡⟨ !assoc= e ⟩
              c ⁻¹ ∙ c ∙ y   ≡⟨ ∙= inv-l idp ⟩
              ε ∙ y          ≡⟨ idl ⟩
              y ∎

          inv-r : RightInverse ε _⁻¹ _∙_
          inv-r = cancels-∙-left (! assoc ♦ ∙= inv-l idp ♦ ! comm-ε)

          /-∙ : ∀ {x y} → x ≡ (x / y) ∙ y
          /-∙ {x} {y}
            = x               ≡⟨ ! idr ⟩
              x ∙ ε           ≡⟨ ap (_∙_ x) (! inv-l) ⟩
              x ∙ (y ⁻¹ ∙ y)  ≡⟨ ! assoc ⟩
              (x / y) ∙ y     ∎

        module FromRightInverse
               (inv-r : RightInverse ε _⁻¹ _∙_)
               where

          cancels-∙-right : RightCancel _∙_
          cancels-∙-right {c} {x} {y} e
            = x              ≡⟨ ! idr ⟩
              x ∙ ε          ≡⟨ ∙= idp (! inv-r) ⟩
              x ∙ (c ∙ c ⁻¹) ≡⟨ assoc= e ⟩
              y ∙ (c ∙ c ⁻¹) ≡⟨ ∙= idp inv-r ⟩
              y ∙ ε          ≡⟨ idr ⟩
              y ∎

          inv-l : LeftInverse ε _⁻¹ _∙_
          inv-l = cancels-∙-right (assoc ♦ ∙= idp inv-r ♦ comm-ε)

          module _ {x y} where
            ∙-/ : x ≡ (x ∙ y) / y
            ∙-/
              = x            ≡⟨ ! idr ⟩
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
                ε / y        ≡⟨ idl ⟩
                y ⁻¹         ∎

          open FromLeftInverse inv-l hiding (inv-r)

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
              x ∙ x ⁻¹                ≡⟨ ap (_∙_ x) (! idl) ⟩
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
            ^-⊖ 0      (1+ n) = ! idl
            ^-⊖ (1+ m) (1+ n) =
               b ^(m ⊖ n)                      ≡⟨ ^-⊖ m n ⟩
               (b ^⁺ m ∙ b ^⁻ n)               ≡⟨ ! elim-inner= inv-r ⟩
               (b ^⁺ m ∙ b) ∙ (b ⁻¹ ∙ b ^⁻ n)  ≡⟨ ∙= idp (! ⁻¹-hom′) ⟩
               (b ^⁺ m ∙ b) ∙ (b ^⁺ n ∙ b)⁻¹   ≡⟨ ∙= (! ^⁺-1+ m) (ap _⁻¹ (! ^⁺-1+ n)) ⟩
               (b ∙ b ^⁺ m) ∙ (b ∙ b ^⁺ n)⁻¹   ∎

            ^-⊖' : ∀ m n → b ^(m ⊖ n) ≡ b ^⁻ n ∙ b ^⁺ m
            ^-⊖' m      0      = ! is-ε-left ε⁻¹-ε
            ^-⊖' 0      (1+ n) = ! idr
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
            ^⁻′1-id = idr

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
                                  ♦ ^⁺-+ (1+ n) {1+ m}) ♦ ⁻¹-hom′
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
            ^-suc i = ^-+ (+ 1) i ♦ ∙= idr idp

            ^-pred : ∀ i → b ^(predℤ i) ≡ b ⁻¹ ∙ b ^ i
            ^-pred i = ^-+ (- + 1) i ♦ ap (λ z → z ⁻¹ ∙ b ^ i) idr

            ^-comm : ∀ i j → b ^ i ∙ b ^ j ≡ b ^ j ∙ b ^ i
            ^-comm -[1+ m ] -[1+ n ] = ^⁻-comm (1+ m) (1+ n)
            ^-comm -[1+ m ]   (+ n)  = ! ^⁺-^⁻-comm n (1+ m)
            ^-comm   (+ m)  -[1+ n ] = ^⁺-^⁻-comm m (1+ n)
            ^-comm   (+ m)    (+ n)  = ^⁺-comm m n

          {-
          ^-* : ∀ i j → b ^(i *ℤ j) ≡ (b ^ j)^ i
          ^-* i j = {!!}
          -}

module Explicits where
  open Algebra.FunctionProperties.NP Π  {a}{a}{A} _≡_ public

  -- REPEATED from above but with explicit arguments
  module FromOp₂
           (_∙_ : Op₂ A){x x' y y'}(p : x ≡ x')(q : y ≡ y')
         where
    op= : x ∙ y ≡ x' ∙ y'
    op= = ap (_∙_ x) q ♦ ap (λ z → z ∙ y') p

  module FromComm
           (_∙_   : Op₂ A)
           (comm  : Commutative _∙_)
           (x y x' y' : A)
           (e : (y ∙ x) ≡ (y' ∙ x'))
         where
    open FromOp₂ _∙_

    comm= : x ∙ y ≡ x' ∙ y'
    comm= = comm _ _ ♦ e ♦ comm _ _

  module FromAssoc
           (_∙_   : Op₂ A)
           (assoc : Associative _∙_)

         where
    open FromOp₂ _∙_

    assocs : Associative _∙_ × Associative (flip _∙_)
    assocs = assoc , (λ _ _ _ → ! assoc _ _ _)

    module _ {c x y x' y' : A}
             (e : (x ∙ y) ≡ (x' ∙ y')) where
      assoc= : x ∙ (y ∙ c) ≡ x' ∙ (y' ∙ c)
      assoc= = ! assoc _ _ _ ♦ op= e idp ♦ assoc _ _ _

      !assoc= : (c ∙ x) ∙ y ≡ (c ∙ x') ∙ y'
      !assoc= = assoc _ _ _ ♦ op= idp e ♦ ! assoc _ _ _

    module _ {c d x y x' y' : A}
             (e : (x ∙ y) ≡ (x' ∙ y')) where
      inner= : (c ∙ x) ∙ (y ∙ d) ≡ (c ∙ x') ∙ (y' ∙ d)
      inner= = assoc= (!assoc= e)

  module FromAssocComm
           (_∙_   : Op₂ A)
           (assoc : Associative _∙_)
           (comm  : Commutative _∙_)
         where
    open FromOp₂   _∙_       renaming (op= to ∙=)
    open FromAssoc _∙_ assoc public
    open FromComm  _∙_ comm  public

    module _ x y z where
      assoc-comm : x ∙ (y ∙ z) ≡ y ∙ (x ∙ z)
      assoc-comm = assoc= (comm _ _)

      !assoc-comm : (x ∙ y) ∙ z ≡ (x ∙ z) ∙ y
      !assoc-comm = !assoc= (comm _ _)

    interchange : Interchange _∙_ _∙_
    interchange _ _ _ _ = assoc= (!assoc= (comm _ _))

    module _ {c d x y x' y' : A}
             (e : (x ∙ y) ≡ (x' ∙ y')) where
      outer= : (x ∙ c) ∙ (d ∙ y) ≡ (x' ∙ c) ∙ (d ∙ y')
      outer= = ∙= (comm _ _) (comm _ _) ♦ assoc= (!assoc= e) ♦ ∙= (comm _ _) (comm _ _)

  module _ {b}{B : Set b} where
    open Morphisms {B = B} _≡_ public

    module _ {f : A → B} where
      Injective-¬Conflict : Injective f → ¬(Conflict f)
      Injective-¬Conflict inj (x , y , x≢y , fx≡fy) = x≢y (inj _ _ fx≡fy)

      Conflict-¬Injective : Conflict f → ¬(Injective f)
      Conflict-¬Injective = flip Injective-¬Conflict
-- -}
-- -}
-- -}
-- -}
