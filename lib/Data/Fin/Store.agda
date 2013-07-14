{-# OPTIONS --type-in-type #-}
module Data.Fin.Store where

open import Data.One
open import Data.Nat
open import Data.Product.NP hiding (Δ)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Fin as F using (Fin; zero; suc; equal)

infixr 4 _,_
record TypeStore : Set where
  constructor _,_
  field
    n : ℕ
    Δ : Fin n → Set

_◅′_ : ∀ {A n} → A → (Fin n → A) → (Fin (suc n) → A)
(x ◅′ Δ) zero    = x
(_ ◅′ Δ) (suc x) = Δ x

_◅_ : Set → TypeStore → TypeStore
A ◅ (n , Δ) = suc n , A ◅′ Δ

lift1-pf :
  ∀{A n}(Δ : Fin n → A){m}(Δ′ : Fin m → A)(v : A)(f : Fin n → Fin m)(pf : ∀ {x} → Δ x ≡ Δ′ (f x)) →
    ∀ {x} → (v ◅′ Δ) x ≡ (v ◅′ Δ′) (F.lift 1 f x)
lift1-pf Δ Δ′ v f pf {zero} = refl
lift1-pf Δ Δ′ v f pf {suc i} = pf

module Internals where

  Store : (Δ : TypeStore) → Set
  -- Store (n , Δ) = (x : Fin n) → ∀ {A} → A ≤ Δ x → A
  Store (n , Δ) = (x : Fin n) → Δ x

  record Ref (nΔ : TypeStore) (A : Set) : Set where
    constructor _,_
    open TypeStore nΔ
    field
      x     : Fin n
      Δx≡A : Δ x ≡ A

  ετ : TypeStore
  ετ = 0 , λ()

  ε : Store ετ
  ε = λ()

  new : ∀ {A Δ} → A → Store Δ → Store (A ◅ Δ) × Ref (A ◅ Δ) A
  new {A} {Δ} x Γ = Γ′ , (zero , refl) where
    Γ′ : Store (A ◅ Δ)
    Γ′ zero    = x
    Γ′ (suc y) = Γ y

  read : ∀ {A Δ} → Ref Δ A → Store Δ → A
  read (x , refl) ρ = ρ x

  write : ∀ {A Δ} → Ref Δ A → A → Store Δ → Store Δ
  write (x , refl) v ρ y with F.compare x y
  write (_ , refl) v _ ._    | equal ._ = v
  ...                        | _        = ρ y

  sucR : ∀ {A B Δ} → Ref Δ A → Ref (B ◅ Δ) A
  sucR (x , refl) = suc x , refl

record Monadic : Set where
 infixr 4 _>>_

 field
  Ref : TypeStore → Set → Set
  M : (Δ Δ′ : TypeStore) → Set → Set
  _⊆_ : TypeStore → TypeStore → Set

  new : ∀ {A Δ} → A → M Δ (A ◅ Δ) (Ref (A ◅ Δ) A)
  read : ∀ {A Δ Δ′} → Δ ⊆ Δ′ → Ref Δ A → M Δ′ Δ′ A
  write : ∀ {A Δ Δ′} → Δ ⊆ Δ′ → Ref Δ A → A → M Δ′ Δ′ 𝟙
  run : ∀ {A} → (∀ {Δ} → ∃[ Δ′ ] (M Δ Δ′ A)) → A
  return : ∀ {A Δ} → A → M Δ Δ A
  _=<<_ : ∀ {A B Δ₁ Δ₂ Δ₃} → (A → M Δ₂ Δ₃ B) → M Δ₁ Δ₂ A → M Δ₁ Δ₃ B

  ⊆-◅ : ∀ {A Δ} → Δ ⊆ (A ◅ Δ)
  ⊆-cong-◅ : ∀ {Δ Δ′ A} → Δ ⊆ Δ′ → (A ◅ Δ) ⊆ (A ◅ Δ′)
  ⊆-refl : ∀ {Δ} → Δ ⊆ Δ
  ⊆-trans : ∀ {Δ₁ Δ₂ Δ₃} → Δ₁ ⊆ Δ₂ → Δ₂ ⊆ Δ₃ → Δ₁ ⊆ Δ₃
  coe : ∀ {A Δ Δ′} → (Δ ⊆ Δ′) → Ref Δ A → Ref Δ′ A

 _>>=_ : ∀ {A B Δ₁ Δ₂ Δ₃} → M Δ₁ Δ₂ A → (A → M Δ₂ Δ₃ B) → M Δ₁ Δ₃ B
 x >>= f = f =<< x

 _>>_ : ∀ {A Δ₁ Δ₂ Δ₃} → M Δ₁ Δ₂ 𝟙 → M Δ₂ Δ₃ A → M Δ₁ Δ₃ A
 x >> y = x >>= const y

 modify : ∀ {A Δ Δ′} → Δ ⊆ Δ′ → Ref Δ A → (A → A) → M Δ′ Δ′ 𝟙
 modify w r f = (write w r ∘ f) =<< read w r

monadicImplem : Monadic
monadicImplem =
   record { Ref = Ref;
            M = M;
            _⊆_ = _⊆_;
            new = new;
            read = read;
            write = write;
            run = run;
            return = return;
            _=<<_ = _=<<_;
            ⊆-◅ = ⊆-◅;
            ⊆-cong-◅ = ⊆-cong-◅;
            ⊆-refl = ⊆-refl;
            ⊆-trans = ⊆-trans;
            coe = coe } where
  open Internals using (Store)
  open Internals public using (Ref; _,_)
  private
    record M Δ Δ′ (A : Set) : Set where
      constructor mk
      field
        f : Store Δ → Store Δ′ × A

  record _⊆_ (mΔ nΔ′ : TypeStore) : Set where
    constructor _,_
    open TypeStore mΔ renaming (n to m)
    open TypeStore nΔ′ renaming (Δ to Δ′)
    field
      coeFin : Fin m → Fin n
      comm   : ∀ {x} → Δ x ≡ Δ′ (coeFin x)

  ⊆-◅ : ∀ {A Δ} → Δ ⊆ (A ◅ Δ)
  ⊆-◅ = suc , refl
  ⊆-cong-◅ : ∀ {Δ Δ′ A} → Δ ⊆ Δ′ → (A ◅ Δ) ⊆ (A ◅ Δ′)
  ⊆-cong-◅ {n , Δ} {m , Δ′} {A} (f , pf) = F.lift 1 f , λ {x} → lift1-pf Δ Δ′ A f pf {x}
  ⊆-refl : ∀ {Δ} → Δ ⊆ Δ
  ⊆-refl = id , refl
  ⊆-trans : ∀ {Δ₁ Δ₂ Δ₃} → Δ₁ ⊆ Δ₂ → Δ₂ ⊆ Δ₃ → Δ₁ ⊆ Δ₃
  ⊆-trans (f , pf) (g , pg) = g ∘ f , trans pf pg
  coe : ∀ {A Δ Δ′} → (Δ ⊆ Δ′) → Ref Δ A → Ref Δ′ A
  coe (f , pf) (x , refl) = (f x , sym pf)

  new : ∀ {A Δ} → A → M Δ (A ◅ Δ) (Ref (A ◅ Δ) A)
  new v = mk (Internals.new v)

  read : ∀ {A Δ Δ′} → Δ ⊆ Δ′ → Ref Δ A → M Δ′ Δ′ A
  read w r = mk (λ ρ → ρ , Internals.read (coe w r) ρ)

  write : ∀ {A Δ Δ′} → Δ ⊆ Δ′ → Ref Δ A → A → M Δ′ Δ′ 𝟙
  write w r v = mk (λ ρ → Internals.write (coe w r) v ρ , _)

  run : ∀ {A} → (∀ {Δ} → ∃[ Δ′ ] (M Δ Δ′ A)) → A
  run mf = proj₂ (f Internals.ε) where open M (proj₂ mf)

  return : ∀ {A Δ} → A → M Δ Δ A
  return x = mk (λ ρ → ρ , x)

  _=<<_ : ∀ {A B Δ₁ Δ₂ Δ₃} → (A → M Δ₂ Δ₃ B) → M Δ₁ Δ₂ A → M Δ₁ Δ₃ B
  _=<<_ {A} {B} {Δ₁} {Δ₂} {Δ₃} f (mk x) = mk f′ where
    f′ : Store Δ₁ → Store Δ₃ × B
    f′ ρ₁ = let ρ₂,x = x ρ₁ in M.f (f (proj₂ ρ₂,x)) (proj₁ ρ₂,x)

open import Data.List
module Examples (monadic : Monadic) where
  open Monadic monadic

  add : ∀ {Δ} → Ref Δ ℕ → ℕ → M Δ Δ 𝟙
  add r k = modify ⊆-refl r (_+_ k)

  ex₁ : ∀ {Δ} → Ref Δ ℕ → List ℕ → M Δ Δ 𝟙
  ex₁ r []       = return _
  ex₁ r (x ∷ xs) = add r x >> ex₁ r xs

  ex₂ : List ℕ → ℕ
  ex₂ xs = run (_ , new 0 >>= λ r → ex₁ r xs >> read ⊆-refl r)

  ex₃ : ℕ
  ex₃ = run (_ , new 0 >>= λ r₁ →
                 new r₁ >>= λ r₂ →
                 read ⊆-refl r₂ >>= λ r₁′ →
                 write ⊆-◅ r₁′ 1 >> read ⊆-◅ r₁)

  record ExtRef Δ A : Set where
    constructor _,_
    field
      {Δ′} : TypeStore
      ref : Ref Δ A
      ⊆w : Δ′ ⊆ Δ
  extRef : ∀ {A Δ} → Ref Δ A → ExtRef Δ A
  extRef r = r , ⊆-refl
  -- coeExtRef : ∀ {A Δ Δ′} → (Δ ⊆ Δ′) → ExtRef Δ A → ExtRef Δ′ A
  -- coeExtRef = {!!}

{-
  ex₄ : ℕ
  ex₄ = run (_ , new 0 >>= λ r₁ →
                 new (extRef r₁) >>= λ r₂ →
                 new 1 >>= λ r₃ →
                 write ⊆-◅ r₂ (r₃ , ⊆-trans ⊆-◅ ⊆-◅) >>
                 write (⊆-trans ⊆-◅ ⊆-◅) r₁ 21 >>
                 write ⊆-refl r₃ 42 >>
                 read ⊆-◅ r₂ >>= λ r →
                 read {!ExtRef.⊆w r!} {!ExtRef.ref r!})
-}

module RunningExamples where
  open Examples monadicImplem
  test₁ : ex₂ (7 ∷ 3 ∷ 4 ∷ []) ≡ 14
  test₁ = refl

  test₂ : ex₃ ≡ 1
  test₂ = refl

{-
  MapM : (F M : Set → Set) → Set
  MapM F M = ∀ {A B} → (A → M B) → F A → M (F B)

  test₄ : ∀ {F A Δ} (mapM : MapM F (M Δ Δ)) → F A → M Δ Δ (F (Ref {!!} A))
  test₄ mapM input = mapM {!new!} input
-}
