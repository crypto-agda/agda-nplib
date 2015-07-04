{-# OPTIONS --without-K #-}
open import Function.Base using (flip; Π; Πⁱ; Op₂)
open import Data.Nat.Base
  using (_≤_; _∸_; z≤n; s≤s)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; suc to 1+_)
import Data.Nat.Properties.Simple as ℕ°
open import Data.Integer.Base
  using    (ℤ; +_; -[1+_]; _⊖_; -_)
  renaming ( _+_ to _+ℤ_; _-_ to _−ℤ_
           ; suc to sucℤ; pred to predℤ
           )
open import Data.Product
  using (_×_; _,_)
  renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality.Base
  using (_≡_; _≢_; idp; !_; ap; module ≡-Reasoning)
  renaming (_∙_ to _♦_)
open ≡-Reasoning
open import HoTT using (module Equivalences)
open Equivalences using (Is-equiv; is-equiv)

open import Algebra.Raw
import Algebra.FunctionProperties.NP

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

  module From-Magma (magma : Magma A) where

    open Magma magma

    module From-Comm
             (comm  : Commutative _∙_)
             {x y x' y' : A}
             (e : (y ∙ x) ≡ (y' ∙ x'))
           where
      comm= : x ∙ y ≡ x' ∙ y'
      comm= = comm ♦ e ♦ comm

    module From-Assoc
             (assoc : Associative _∙_)
           where

      assocs : Associative _∙_ × Associative (flip _∙_)
      assocs = assoc , ! assoc

      module _ {c x y x' y' : A}
               (e : (x ∙ y) ≡ (x' ∙ y')) where
        assoc= : x ∙ (y ∙ c) ≡ x' ∙ (y' ∙ c)
        assoc= = ! assoc ♦ ∙= e idp ♦ assoc

        !assoc= : (c ∙ x) ∙ y ≡ (c ∙ x') ∙ y'
        !assoc= = assoc ♦ ∙= idp e ♦ ! assoc

      module _ {c d x y x' y' : A}
               (e : (x ∙ y) ≡ (x' ∙ y')) where
        inner= : (c ∙ x) ∙ (y ∙ d) ≡ (c ∙ x') ∙ (y' ∙ d)
        inner= = assoc= (!assoc= e)

    module From-Assoc-Comm
             (assoc : Associative _∙_)
             (comm  : Commutative _∙_)
           where
      open From-Assoc assoc public
      open From-Comm  comm  public

      module _ {x y z} where
        assoc-comm : x ∙ (y ∙ z) ≡ y ∙ (x ∙ z)
        assoc-comm = assoc= comm

        !assoc-comm : (x ∙ y) ∙ z ≡ (x ∙ z) ∙ y
        !assoc-comm = !assoc= comm

      interchange : Interchange _∙_ _∙_
      interchange = assoc= (!assoc= comm)

      ²-∙-distr : ∀ {x y} → (x ∙ y)² ≡ x ² ∙ y ²
      ²-∙-distr = interchange

      ²-∙-distr' : ∀ {x y z} → x ² ∙ (y ∙ z) ≡ (x ∙ y) ∙ (x ∙ z)
      ²-∙-distr' = interchange

      on-sides : ∀ {x x' y y' z z' t t'}
                 → x ∙ z ≡ x' ∙ z'
                 → y ∙ t ≡ y' ∙ t'
                 → (x ∙ y) ∙ (z ∙ t) ≡ (x' ∙ y') ∙ (z' ∙ t')
      on-sides p q = interchange ♦ ∙= p q ♦ interchange

      module _ {c d x y x' y' : A}
               (e : (x ∙ y) ≡ (x' ∙ y')) where
        outer= : (x ∙ c) ∙ (d ∙ y) ≡ (x' ∙ c) ∙ (d ∙ y')
        outer= = ∙= comm comm ♦ assoc= (!assoc= e) ♦ ∙= comm comm

  module From-Op₂ (op : Op₂ A) = From-Magma ⟨ op ⟩

  module From-Monoid-Ops (mon-ops : Monoid-Ops A) where
    open Monoid-Ops mon-ops
    open From-Op₂ _∙_ public

    module From-LeftIdentity (idl : LeftIdentity ε _∙_) where
      module _ {x y} where
        is-ε-left : x ≡ ε → x ∙ y ≡ y
        is-ε-left e = ap (λ z → z ∙ _) e ♦ idl

      ε^⁺ : ∀ n → ε ^⁺ n ≡ ε
      ε^⁺ 0      = idp
      ε^⁺ (1+ n) = idl ♦ ε^⁺ n

    module From-RightIdentity (idr : RightIdentity ε _∙_) where
      module _ {x y} where
        is-ε-right : y ≡ ε → x ∙ y ≡ x
        is-ε-right e = ap (λ z → _ ∙ z) e ♦ idr

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

    module From-Identities (identities : Identity ε _∙_) where
      comm-ε : ∀ {x} → x ∙ ε ≡ ε ∙ x
      comm-ε = snd identities ♦ ! fst identities

      open From-LeftIdentity  (fst identities) public
      open From-RightIdentity (snd identities) public

    module From-Assoc-RightIdentity
             (assoc : Associative _∙_)
             (idr   : RightIdentity ε _∙_)
             where
      open From-RightIdentity idr

      module _ {c x y}(e : x ∙ y ≡ ε) where
        elim-assoc= : (c ∙ x) ∙ y ≡ c
        elim-assoc= = assoc ♦ ∙= idp e ♦ idr

      module _ {c d x y} (e : (x ∙ y) ≡ ε) where
        elim-inner= : (c ∙ x) ∙ (y ∙ d) ≡ c ∙ d
        elim-inner= = ! assoc ♦ ∙= (elim-assoc= e) idp

    module From-Assoc-LeftIdentity
             (assoc : Associative _∙_)
             (idl : LeftIdentity ε _∙_)
             where
      open From-LeftIdentity idl

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
        elim-!inner= : (c ∙ x) ∙ (y ∙ d) ≡ c ∙ d
        elim-!inner= = assoc ♦ ap (_∙_ c) (elim-!assoc= e)

  module From-Group-Ops (grp-ops : Group-Ops A) where
    open Group-Ops grp-ops
    open From-Monoid-Ops mon-ops public

    module From-Assoc-LeftIdentity-LeftInverse
             (assoc : Associative _∙_)
             (idl : LeftIdentity ε _∙_)
             (inverseˡ : LeftInverse ε _⁻¹ _∙_)
             where
      open From-Assoc assoc
      open From-LeftIdentity idl
      open From-Assoc-LeftIdentity assoc idl

      ⁻¹-inverseʳ : RightInverse ε _⁻¹ _∙_
      ⁻¹-inverseʳ {x}
         = x ∙ x ⁻¹                      ≡⟨ ! idl ⟩
           ε ∙ (x ∙ x ⁻¹)                ≡⟨ ∙= (! inverseˡ) idp ⟩
           (x ⁻¹ ⁻¹ ∙ x ⁻¹) ∙ (x ∙ x ⁻¹) ≡⟨ elim-!inner= inverseˡ ⟩
           (x ⁻¹ ⁻¹ ∙ x ⁻¹)              ≡⟨ inverseˡ ⟩
           ε                             ∎

      cancels-∙-left : LeftCancel _∙_
      cancels-∙-left {c} {x} {y} e
        = x              ≡⟨ ! idl ⟩
          ε ∙ x          ≡⟨ ∙= (! inverseˡ) idp ⟩
          c ⁻¹ ∙ c ∙ x   ≡⟨ !assoc= e ⟩
          c ⁻¹ ∙ c ∙ y   ≡⟨ ∙= inverseˡ idp ⟩
          ε ∙ y          ≡⟨ idl ⟩
          y              ∎

      module _ {x y} where
        unique-ε-right : x ∙ y ≡ x → y ≡ ε
        unique-ε-right eq
          = y               ≡⟨ ! is-ε-left inverseˡ ⟩
            x ⁻¹ ∙  x ∙ y   ≡⟨ assoc ⟩
            x ⁻¹ ∙ (x ∙ y)  ≡⟨ ∙= idp eq ⟩
            x ⁻¹ ∙ x        ≡⟨ inverseˡ ⟩
            ε               ∎

      ε^⁻ : ∀ n → ε ^⁻ n ≡ ε
      ε^⁻ n = ⁻¹= (ε^⁺ n) ♦ unique-ε-right ⁻¹-inverseʳ

      ε^ : ∀ i → ε ^ i ≡ ε
      ε^ -[1+ n ] = ε^⁻(1+ n)
      ε^ (+ n)    = ε^⁺ n

      module _ {x y} where
        -- _⁻¹ is a group homomorphism, see Algebra.Group._ᵒᵖ
        ⁻¹-hom′ : (x ∙ y)⁻¹ ≡ y ⁻¹ ∙ x ⁻¹
        ⁻¹-hom′ = cancels-∙-left {x ∙ y}
           ((x ∙ y) ∙ (x ∙ y)⁻¹     ≡⟨ ⁻¹-inverseʳ ⟩
            ε                       ≡⟨ ! ⁻¹-inverseʳ ⟩
            x ∙ x ⁻¹                ≡⟨ ap (_∙_ x) (! idl) ⟩
            x ∙ (ε ∙ x ⁻¹)          ≡⟨ ∙= idp (∙= (! ⁻¹-inverseʳ) idp) ⟩
            x ∙ ((y ∙ y ⁻¹) ∙ x ⁻¹) ≡⟨ ap (_∙_ x) assoc ⟩
            x ∙ (y ∙ (y ⁻¹ ∙ x ⁻¹)) ≡⟨ ! assoc ⟩
            (x ∙ y) ∙ (y ⁻¹ ∙ x ⁻¹) ∎)

        ⁻¹-∙-distr′ : (x ∙ y)⁻¹ ≡ y ⁻¹ / x
        ⁻¹-∙-distr′ = ⁻¹-hom′

      ⁻¹-hom′= : ∀ {x y z t} → x ∙ y ≡ z ∙ t → y ⁻¹ ∙ x ⁻¹ ≡ t ⁻¹ ∙ z ⁻¹
      ⁻¹-hom′= e = ! ⁻¹-hom′ ♦ ap _⁻¹ e ♦ ⁻¹-hom′

      elim-∙-left-⁻¹∙ : ∀ {c x y} → (c ∙ x)⁻¹ ∙ (c ∙ y) ≡ x ⁻¹ ∙ y
      elim-∙-left-⁻¹∙ {c} {x} {y}
        = (c ∙ x)⁻¹   ∙ (c ∙ y)  ≡⟨ ∙= ⁻¹-hom′ idp ⟩
          x ⁻¹ ∙ c ⁻¹ ∙ (c ∙ y)  ≡⟨ elim-!inner= inverseˡ ⟩
          x ⁻¹ ∙ y               ∎

      elim-∙-right-/ : ∀ {c x y} → (x ∙ c) / (y ∙ c) ≡ x / y
      elim-∙-right-/ {c} {x} {y}
        = x ∙ c ∙ (y ∙ c)⁻¹  ≡⟨ ap (_∙_ _) ⁻¹-hom′  ⟩
          x ∙ c ∙ (c ⁻¹ / y) ≡⟨ elim-!inner= ⁻¹-inverseʳ ⟩
          x / y              ∎

    module From-Assoc-RightIdentity-RightInverse
             (assoc : Associative _∙_)
             (idr : RightIdentity ε _∙_)
             (inverseʳ : RightInverse ε _⁻¹ _∙_)
             where
      open From-Assoc assoc
      open From-Assoc-RightIdentity assoc idr

      cancels-∙-right : RightCancel _∙_
      cancels-∙-right {c} {x} {y} e
        = x              ≡⟨ ! idr ⟩
          x ∙ ε          ≡⟨ ∙= idp (! inverseʳ) ⟩
          x ∙ (c ∙ c ⁻¹) ≡⟨ assoc= e ⟩
          y ∙ (c ∙ c ⁻¹) ≡⟨ ∙= idp inverseʳ ⟩
          y ∙ ε          ≡⟨ idr ⟩
          y              ∎

      inverseˡ : LeftInverse ε _⁻¹ _∙_
      inverseˡ {x}
        = x ⁻¹ ∙ x                      ≡⟨ ! idr ⟩
          (x ⁻¹ ∙ x) ∙ ε                ≡⟨ ∙= idp (! inverseʳ) ⟩
          (x ⁻¹ ∙ x) ∙ (x ⁻¹ ∙ x ⁻¹ ⁻¹) ≡⟨ elim-inner= inverseʳ ⟩
          (x ⁻¹ ∙ x ⁻¹ ⁻¹)              ≡⟨ inverseʳ ⟩
          ε                             ∎

      ⁻¹-involutive : Involutive _⁻¹
      ⁻¹-involutive {x}
        = cancels-∙-right
          (x ⁻¹ ⁻¹ ∙ x ⁻¹ ≡⟨ inverseˡ ⟩
           ε              ≡⟨ ! inverseʳ ⟩
           x ∙ x ⁻¹       ∎)

      module _ {x y} where
        /-∙ : (x / y) ∙ y ≡ x
        /-∙ = elim-assoc= inverseˡ

        ∙-/ : (x ∙ y) / y ≡ x
        ∙-/ = elim-assoc= inverseʳ

      module _ {x y} where
        unique-ε-left : x ∙ y ≡ y → x ≡ ε
        unique-ε-left eq
          = x            ≡⟨ ! ∙-/ ⟩
            (x ∙ y) / y  ≡⟨ /= eq idp ⟩
            y / y        ≡⟨ inverseʳ ⟩
            ε            ∎

        x/y≡ε→x≡y : x / y ≡ ε → x ≡ y
        x/y≡ε→x≡y x/y≡ε = cancels-∙-right (x/y≡ε ♦ ! inverseʳ)

        x/y≢ε : x ≢ y → x / y ≢ ε
        x/y≢ε x≢y x/y≡ε = x≢y (x/y≡ε→x≡y x/y≡ε)

      ε⁻¹≡ε : ε ⁻¹ ≡ ε
      ε⁻¹≡ε = unique-ε-left inverseˡ

    module From-Assoc-Identities-RightInverse
             (assoc : Associative _∙_)
             (identities : Identity ε _∙_)
             (inv-r : RightInverse ε _⁻¹ _∙_)
             where
      private
        idl = fst identities
        idr = snd identities

      inverseʳ : RightInverse ε _⁻¹ _∙_
      inverseʳ = inv-r

      open From-Assoc assoc
      open From-Identities identities using (comm-ε)
      open From-LeftIdentity        idl
      open From-RightIdentity       idr
      open From-Assoc-LeftIdentity  assoc idl
      open From-Assoc-RightIdentity assoc idr
      open From-Assoc-RightIdentity-RightInverse assoc idr inverseʳ public
      open From-Assoc-LeftIdentity-LeftInverse assoc idl inverseˡ public
        hiding (⁻¹-inverseʳ)

      module _ {x y} where
        ∙-/′ : y ∙ (x /′ y) ≡ x
        ∙-/′ = elim-!assoc= inverseʳ

        /′-∙ : (y ∙ x) /′ y ≡ x
        /′-∙ = elim-!assoc= inverseˡ

        /-/′ : x / (x /′ y) ≡ y
        /-/′ =
          x ∙ (y ⁻¹ ∙ x) ⁻¹    ≡⟨ ∙= idp ⁻¹-hom′ ⟩
          x ∙ (x ⁻¹ ∙ y ⁻¹ ⁻¹) ≡⟨ elim-!assoc= inverseʳ ⟩
          y ⁻¹ ⁻¹              ≡⟨ ⁻¹-involutive ⟩
          y                    ∎

        /′-/ : x /′ (x / y) ≡ y
        /′-/ =
          (x / y)⁻¹ ∙ x        ≡⟨ ∙= ⁻¹-hom′ idp ⟩
          y ⁻¹ ⁻¹ ∙ x ⁻¹ ∙ x   ≡⟨ elim-assoc= inverseˡ ⟩
          y ⁻¹ ⁻¹              ≡⟨ ⁻¹-involutive ⟩
          y                    ∎

      ∙-is-equiv : ∀ {k} → Is-equiv (_∙_ k)
      ∙-is-equiv {k} = is-equiv (_∙_ (k ⁻¹))
                                (λ _ → ! assoc ♦ ∙= inverseʳ idp ♦ idl)
                                (λ _ → ! assoc ♦ ∙= inverseˡ idp ♦ idl)

      flip-∙-is-equiv : ∀ {k} → Is-equiv (flip _∙_ k)
      flip-∙-is-equiv {k} = is-equiv (flip _∙_ (k ⁻¹))
                                     (λ _ → assoc ♦ ∙= idp inverseˡ ♦ idr)
                                     (λ _ → assoc ♦ ∙= idp inverseʳ ♦ idr)

      module _ {x y} where
        unique-⁻¹ : x ∙ y ≡ ε → x ≡ y ⁻¹
        unique-⁻¹ eq
          = x            ≡⟨ ! ∙-/ ⟩
            (x ∙ y) / y  ≡⟨ /= eq idp ⟩
            ε / y        ≡⟨ idl ⟩
            y ⁻¹         ∎

      ⁻¹-inj : ∀ {x y} → x ⁻¹ ≡ y ⁻¹ → x ≡ y
      ⁻¹-inj {x} {y} e
         = ! (y              ≡⟨ ! idr ⟩
              y ∙ ε          ≡⟨ ∙= idp (ε        ≡⟨ ! inverseˡ  ⟩
                                        x ⁻¹ ∙ x ≡⟨ ∙= e idp ⟩
                                        y ⁻¹ ∙ x ∎) ⟩
              y ∙ (y ⁻¹ ∙ x) ≡⟨ ∙-/′ ⟩
              x ∎)

      module _ {b} where
        ^⁺-1+ : ∀ n → b ^⁺(1+ n) ≡ b ^⁺ n ∙ b
        ^⁺-1+ 0 = comm-ε
        ^⁺-1+ (1+ n) = ap (_∙_ b) (^⁺-1+ n) ♦ ! assoc

        ^⁺-∸ : ∀ {m n} → n ≤ m → b ^⁺(m ∸ n) ≡ b ^⁺ m ∙ b ^⁻ n
        ^⁺-∸ z≤n = ! is-ε-right ε⁻¹≡ε
        ^⁺-∸ (s≤s {n} {m} n≤m) =
           b ^⁺(m ∸ n)                     ≡⟨ ^⁺-∸ n≤m ⟩
           (b ^⁺ m ∙ b ^⁻ n)               ≡⟨ ! elim-inner= inverseʳ ⟩
           (b ^⁺ m ∙ b) ∙ (b ⁻¹ ∙ b ^⁻ n)  ≡⟨ ∙= idp (! ⁻¹-hom′) ⟩
           (b ^⁺ m ∙ b) ∙ (b ^⁺ n ∙ b)⁻¹   ≡⟨ ∙= (! ^⁺-1+ m) (ap _⁻¹ (! ^⁺-1+ n)) ⟩
           (b ∙ b ^⁺ m) ∙ (b ∙ b ^⁺ n)⁻¹   ∎

        ^-⊖ : ∀ m n → b ^(m ⊖ n) ≡ b ^⁺ m ∙ b ^⁻ n
        ^-⊖ m      0      = ! is-ε-right ε⁻¹≡ε
        ^-⊖ 0      (1+ n) = ! idl
        ^-⊖ (1+ m) (1+ n) =
           b ^(m ⊖ n)                      ≡⟨ ^-⊖ m n ⟩
           (b ^⁺ m ∙ b ^⁻ n)               ≡⟨ ! elim-inner= inverseʳ ⟩
           (b ^⁺ m ∙ b) ∙ (b ⁻¹ ∙ b ^⁻ n)  ≡⟨ ∙= idp (! ⁻¹-hom′) ⟩
           (b ^⁺ m ∙ b) ∙ (b ^⁺ n ∙ b)⁻¹   ≡⟨ ∙= (! ^⁺-1+ m) (ap _⁻¹ (! ^⁺-1+ n)) ⟩
           (b ∙ b ^⁺ m) ∙ (b ∙ b ^⁺ n)⁻¹   ∎

        ^-⊖' : ∀ m n → b ^(m ⊖ n) ≡ b ^⁻ n ∙ b ^⁺ m
        ^-⊖' m      0      = ! is-ε-left ε⁻¹≡ε
        ^-⊖' 0      (1+ n) = ! idr
        ^-⊖' (1+ m) (1+ n) =
           b ^(m ⊖ n)                      ≡⟨ ^-⊖' m n ⟩
           (b ^⁻ n ∙ b ^⁺ m)               ≡⟨ ! elim-inner= inverseˡ ⟩
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
        ^⁻′-spec 0 = ! ε⁻¹≡ε
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
        ^-- (+ 0)    = ! ε⁻¹≡ε
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

    module From-Assoc-Identities-Inverse
             (assoc : Associative _∙_)
             (identities : Identity ε _∙_)
             (inv : Inverse ε _⁻¹ _∙_)
             where
      open From-Assoc-Identities-RightInverse assoc identities (snd inv) public

  module From-Ring-Ops (rng-ops : Ring-Ops A) where
    open Ring-Ops rng-ops

    module DistributesOverʳ
             (*-comm : Commutative _*_)
             (*-+-distrˡ : _*_ DistributesOverˡ _+_)
             where
      *-+-distrʳ : _*_ DistributesOverʳ _+_
      *-+-distrʳ = *-comm ♦ *-+-distrˡ ♦ += *-comm *-comm

    module DistributesOverˡ
             (*-comm : Commutative _*_)
             (*-+-distrʳ : _*_ DistributesOverʳ _+_)
             where
      *-+-distrˡ : _*_ DistributesOverˡ _+_
      *-+-distrˡ = *-comm ♦ *-+-distrʳ ♦ += *-comm *-comm

    module From-+Group-1*Identity-DistributesOverʳ
             (+-assoc : Associative _+_)
             (0+-identity : LeftIdentity 0# _+_)
             (+0-identity : RightIdentity 0# _+_)
             (0−-inverseʳ : RightInverse 0# 0−_ _+_)
             (1*-identity : LeftIdentity 1# _*_)
             (*-+-distrʳ : _*_ DistributesOverʳ _+_)
             where
      open From-Group-Ops.From-Assoc-Identities-RightInverse
             +-grp-ops
             +-assoc (0+-identity , +0-identity) 0−-inverseʳ
            renaming ( cancels-∙-left to cancels-+-left
                     ; cancels-∙-right to cancels-+-right
                     ; inverseˡ to 0−-inverseˡ
                     ; ε⁻¹≡ε to 0−0≡0
                     ; ⁻¹-hom′ to 0−-hom′
                     )

      -0≡0 : -0# ≡ 0#
      -0≡0 = 0−0≡0

      0*-zero : LeftZero 0# _*_
      0*-zero {x} = cancels-+-left
        (x + 0# * x      ≡⟨ += (! 1*-identity) idp ⟩
         1# * x + 0# * x ≡⟨ ! *-+-distrʳ ⟩
         (1# + 0#) * x   ≡⟨ *= +0-identity idp ⟩
         1# * x          ≡⟨ 1*-identity ⟩
         x               ≡⟨ ! +0-identity ⟩
         x + 0#          ∎)

      2*-spec : ∀ {n} → 2* n ≡ 2# * n
      2*-spec = ! += 1*-identity 1*-identity ♦ ! *-+-distrʳ

      0−-*-distr : ∀ {x y} → 0−(x * y) ≡ (0− x) * y
      0−-*-distr = cancels-+-right (0−-inverseˡ ♦ ! 0*-zero ♦ *= (! 0−-inverseˡ) idp ♦ *-+-distrʳ)

      -1*-neg : ∀ {x} → -1# * x ≡ 0− x
      -1*-neg = ! 0−-*-distr ♦ 0−= 1*-identity

      2*-*-distr : ∀ {x y} → 2*(x * y) ≡ 2* x * y
      2*-*-distr = ! *-+-distrʳ

    module From-+Group-*Identity-DistributesOver
             (+-assoc : Associative _+_)
             (0+-identity : LeftIdentity 0# _+_)
             (+0-identity : RightIdentity 0# _+_)
             (0−-inverseʳ : RightInverse 0# 0−_ _+_)
             (1*-identity : LeftIdentity 1# _*_)
             (*1-identity : RightIdentity 1# _*_)
             (*-+-distrs : _*_ DistributesOver _+_)
             where
      *-+-distrˡ : _*_ DistributesOverˡ _+_
      *-+-distrˡ = fst *-+-distrs

      *-+-distrʳ : _*_ DistributesOverʳ _+_
      *-+-distrʳ = snd *-+-distrs

      open From-Group-Ops.From-Assoc-Identities-RightInverse
             +-grp-ops
             +-assoc (0+-identity , +0-identity) 0−-inverseʳ
            renaming ( ⁻¹-involutive to 0−-involutive
                     ; cancels-∙-left to cancels-+-left
                     ; cancels-∙-right to cancels-+-right
                     ; inverseˡ to 0−-inverseˡ
                     ; ⁻¹-∙-distr′ to 0−-+-distr′
                     )

      open From-+Group-1*Identity-DistributesOverʳ
             +-assoc 0+-identity +0-identity 0−-inverseʳ
             1*-identity *-+-distrʳ
             public

      *0-zero : RightZero 0# _*_
      *0-zero {x} = cancels-+-right
        (x * 0# + x      ≡⟨ += idp (! *1-identity) ⟩
         x * 0# + x * 1# ≡⟨ ! *-+-distrˡ ⟩
         x * (0# + 1#)   ≡⟨ *= idp 0+-identity ⟩
         x * 1#          ≡⟨ *1-identity ⟩
         x               ≡⟨ ! 0+-identity ⟩
         0# + x          ∎)

      0−-*-distrʳ : ∀ {x y} → 0−(x * y) ≡ x * (0− y)
      0−-*-distrʳ = cancels-+-right (0−-inverseˡ ♦ (! *0-zero ♦ *= idp (! 0−-inverseˡ)) ♦ *-+-distrˡ)

      *-−-distr : ∀ {x y z} → x * (y − z) ≡ x * y − x * z
      *-−-distr = *-+-distrˡ ♦ += idp (! 0−-*-distrʳ)

      ²-0−-distr : ∀ {x} → (0− x)² ≡ x ²
      ²-0−-distr = ! 0−-*-distr ♦ 0−=(! 0−-*-distrʳ) ♦ 0−-involutive

      +-comm : Commutative _+_
      +-comm {a} {b} =
          cancels-+-right
            (cancels-+-left
              (a + (a + b + b)   ≡⟨ += idp +-assoc ♦ ! +-assoc ⟩
               (a + a) + (b + b) ≡⟨ += 2*-spec 2*-spec ⟩
               2# * a  + 2# * b  ≡⟨ ! *-+-distrˡ ⟩
               2# * (a + b)      ≡⟨ ! 2*-spec ⟩
               (a + b) + (a + b) ≡⟨ +-assoc ♦ += idp (! +-assoc) ⟩
               a + (b + a + b)   ∎))

      0−-+-distr : ∀ {x y} → 0−(x + y) ≡ 0− x − y
      0−-+-distr = 0−= +-comm ♦ 0−-+-distr′

  module From-Field-Ops (fld-ops : Field-Ops A) where
    open Field-Ops fld-ops

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
