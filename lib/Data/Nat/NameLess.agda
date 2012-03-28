module Data.Nat.NameLess where

open import Function
open import Data.Nat.NP
open import Relation.Binary.PropositionalEquality.NP
open import Relation.Nullary

open ≡-Reasoning

liftℕ_by_when≥_ : ℕ → ℕ → ℕ → ℕ
liftℕ_by_when≥_ x n k with suc x ≤? k
...                   | yes _ = x
...                   | no  _ = n + x

record Has# (A : Set) : Set where
  field
    # : ℕ → A

    #-injective : ∀ {x y} → # x ≡ # y → x ≡ y

record RawLiftable (A : Set) : Set where
  field
    has# : Has# A
    lift_by_when≥_ : A → ℕ → ℕ → A
  open Has# has# public

record Liftable (A : Set) : Set where
  field
    rawLiftable : RawLiftable A

    lift#≡#liftℕ :
      let open RawLiftable rawLiftable in
      ∀ {x n k} → lift # x by n when≥ k ≡ # (liftℕ x by n when≥ k)

    lift₀-vanish :
      let open RawLiftable rawLiftable in
      ∀ {e k} → lift e by 0 when≥ k ≡ e

    join-lifts :
      let open RawLiftable rawLiftable in
      ∀ {e i j m n}
      → i ≤ j → j ≤ i + m
      → lift (lift e by m when≥ i) by n when≥ j
      ≡ lift e by m + n when≥ i

    swap-lifts :
      let open RawLiftable rawLiftable in
      ∀ {e i j m n}
      → i ≤ j
      → lift (lift e by m when≥ i) by n when≥ (j + m)
      ≡ lift (lift e by n when≥ j) by m when≥ i
{-      ∀ {e i j m n}
      → i ≤ j
      → lift (lift e by 1 when≥ i) by 1 when≥ (suc j)
      ≡ lift (lift e by 1 when≥ j) by 1 when≥ i
-}
  open RawLiftable rawLiftable public

record HasRawSubst (A B C : Set) : Set where
  infix 8 _[_:=_]
  field
    _[_:=_] : A → ℕ → B → C

{-
DistrSubsts : ∀ {A B : Set}
                (hasSubstA : HasRawSubst A B A)
                (hasSubstB : HasRawSubst B B B)
              → Set
DistrSubsts hasSubstA hasSubstB =
  ∀ {e i j e₁ e₂}
  → e [ suc (j + i) := e₁ ]A [ i := e₂ [ j := e₁ ]B ]A
  ≡ e [ i := e₂ ]A [ j + i := e₁ ]A
  where
    open HasRawSubst hasSubstA public renaming (_[_:=_] to _[_:=_]A)
    open HasRawSubst hasSubstB public renaming (_[_:=_] to _[_:=_]B)
-}

DistrSubsts : ∀ {E E₁ E₂ A B C R : Set}
                (hasSubst₁ : HasRawSubst E E₁ A)
                (hasSubst₂ : HasRawSubst E₂ E₁ B)
                (hasSubst₃ : HasRawSubst A B R)
                (hasSubst₄ : HasRawSubst E E₂ C)
                (hasSubst₅ : HasRawSubst C E₁ R)
              → Set
DistrSubsts hasSubst₁ hasSubst₂ hasSubst₃ hasSubst₄ hasSubst₅ =
  ∀ {e i j e₁ e₂}
  → e [ suc (i + j) := e₁ ]₁ [ i := e₂ [ j := e₁ ]₂ ]₃
  ≡ e [ i := e₂ ]₄ [ i + j := e₁ ]₅
  where
    open HasRawSubst hasSubst₁ public renaming (_[_:=_] to _[_:=_]₁)
    open HasRawSubst hasSubst₂ public renaming (_[_:=_] to _[_:=_]₂)
    open HasRawSubst hasSubst₃ public renaming (_[_:=_] to _[_:=_]₃)
    open HasRawSubst hasSubst₄ public renaming (_[_:=_] to _[_:=_]₄)
    open HasRawSubst hasSubst₅ public renaming (_[_:=_] to _[_:=_]₅)

record HasSubst (A B : Set) : Set where
  field
    hasRawSubst    : HasRawSubst A B A
    hasRawSubstBBB : HasRawSubst B B B

    distr-substs : DistrSubsts hasRawSubst hasRawSubstBBB hasRawSubst hasRawSubst hasRawSubst

  open HasRawSubst hasRawSubst public

record HasHomSubst (A : Set) : Set where
  field
    hasHomSubst : HasSubst A A

  open HasSubst hasHomSubst public

Lift-subst≡lift :
   ∀ {A B C : Set} → (A → C) → Liftable A → HasRawSubst A B C → Set
Lift-subst≡lift A→C liftable hasRawSubst =
    ∀ e e' {n k k'} → k ≤ k' → k' ≤ k + n
    → (lift e by suc n when≥ k)[ k' := e' ]
    ≡ A→C (lift e by n when≥ k)
  where
    open Liftable liftable public
    open HasRawSubst hasRawSubst public

DistrLiftSubst₁ :
   ∀ {A B C : Set} →
     Liftable A →
     Liftable C →
     HasRawSubst A B C → Set
DistrLiftSubst₁ liftable liftableC hasSubst =
  ∀ e e' {n k k'} → k ≤ k'
  → liftC e [ k' := e' ] by n when≥ k
  ≡ (lift e by n when≥ k)[ k' + n := e' ]
  where
    open Liftable liftable public
    open Liftable liftableC public using () renaming (lift_by_when≥_ to liftC_by_when≥_)
    open HasRawSubst hasSubst public

DistrLiftSubst₂ :
   ∀ {A B C : Set}
     (liftable : Liftable A)
     (liftableB : Liftable B)
     (liftableC : Liftable C)
     (hasRawSubst : HasRawSubst A B C) → Set
DistrLiftSubst₂ liftable liftableB liftableC hasSubst =
  ∀ e e' {n k k'}
  → k' < k → liftC e [ k' := e' ] by n when≥ k
  ≡ (lift e by n when≥ suc k)[ k' := liftB e' by n when≥ (k ∸ k') ]
  where
    open Liftable liftable public
    open Liftable liftableB public using () renaming (lift_by_when≥_ to liftB_by_when≥_)
    open Liftable liftableC public using () renaming (lift_by_when≥_ to liftC_by_when≥_)
    open HasRawSubst hasSubst public

record IsNameLess (A B : Set) : Set where
  field
    hasSubst          : HasSubst A B
    liftable          : Liftable A
    liftableB         : Liftable B
    lift-subst≡lift   : Lift-subst≡lift id liftable (HasSubst.hasRawSubst hasSubst)
    distr-lift-subst₁ : DistrLiftSubst₁ liftable liftable (HasSubst.hasRawSubst hasSubst)
    distr-lift-subst₂ : DistrLiftSubst₂ liftable liftableB liftable (HasSubst.hasRawSubst hasSubst)

  open Liftable liftable public
  open HasSubst hasSubst public

  distr-lift-subst₁' : ∀ e e' {n k k'} → k ≤ k'
    → lift e [ k' := e' ] by n when≥ k
    ≡ (lift e by n when≥ k)[ n + k' := e' ]
  distr-lift-subst₁' e e' {n} {k} {k'} k≤k' =
      lift e [ k' := e' ] by n when≥ k
        ≡⟨ distr-lift-subst₁ e e' k≤k' ⟩
      (lift e by n when≥ k)[ k' + n := e' ]
        ≡⟨ cong (λ x → (lift e by n when≥ k)[ x := e' ]) (ℕ°.+-comm k' n) ⟩
      (lift e by n when≥ k)[ n + k' := e' ]
    ∎

  lift₁₀-subst₀-vanish : ∀ {e e'} → (lift e by 1 when≥ 0)[ 0 := e' ] ≡ e
  lift₁₀-subst₀-vanish {e} {e'} =
      (lift e by 1 when≥ 0)[ 0 := e' ] ≡⟨ lift-subst≡lift e e' z≤n z≤n ⟩
       lift e by 0 when≥ 0             ≡⟨ lift₀-vanish ⟩
      e
    ∎
