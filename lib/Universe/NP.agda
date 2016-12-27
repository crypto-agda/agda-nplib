module Universe.NP where

open import Type
open import Type.Identities
open import Function.NP
open import Level.NP
open import Data.Product.NP
open import Data.Nat using (ℕ)
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Fin
open import Data.Sum.NP
open import Relation.Binary.PropositionalEquality.NP
open import HoTT
open Equivalences

open import Universe public

module _ {u e} {U : ★_ u} (El : U → ★_ e) where
    universe : Universe u e
    universe = record { El = El }

U★_ : (ℓ : Level) → Universe (ₛ ℓ) ℓ
U★ ℓ = universe id

U★₀ = U★_ ₀
U★₁ = U★_ ₁
U★₂ = U★_ ₂

UFin U✓ : Universe ₀ ₀

UFin = record { El = Fin }
U✓ = record { El = ✓ }

U𝟘 : ∀ {e} → Universe ₀ e
U𝟘 = record { U = 𝟘; El = λ() }

-- Or Uconst
U𝟙 : ∀ {ℓ} → ★_ ℓ → Universe ₀ ℓ
U𝟙 A = record { U = 𝟙; El = λ _ → A }

open Universe.Universe renaming (U to Code)

record Map {u u'}(U : Universe u u')
           {v v'}(V : Universe v v') : ★_ (u ⊔ v ⊔ u' ⊔ v') where
    constructor mk
    field
      map-Code : Code U → Code V
      map-El   : ∀ {u} → El U u → El V (map-Code u)

    {- This one has contravariant mapping of El's -}
record CoMap {u u'}(U : Universe u u')
             {v v'}(V : Universe v v') : ★_ (u ⊔ v ⊔ u' ⊔ v') where
    constructor mk
    field
      map-Code : Code U → Code V
      comap-El : ∀ {u} → El V (map-Code u) → El U u

module _
  {e u v}(U : Universe u e)
         (V : Universe v e)
  where
    infix 4 _⊏_
    record _⊏_ : ★_ (u ⊔ v ⊔ ₛ e) where
      constructor mk
      field
        ⊏-Code : Code U → Code V
        ⊏-El   : ∀ A → El U A ≃ El V (⊏-Code A)

module _
  {e u v}{U : Universe u e}
         {V : Universe v e}
  where
  ⊏-Map : U ⊏ V → Map U V
  ⊏-Map (mk f e) = mk f (·→ (e _))

  ⊏-CoMap : U ⊏ V → CoMap U V
  ⊏-CoMap (mk f e) = mk f (·← (e _))

✓⊏Fin : U✓ ⊏ UFin
✓⊏Fin = mk 𝟚▹ℕ [0: ≃-! Fin0≃𝟘
                 1: ≃-! Fin1≃𝟙 ]

module _ {u e}(U : Universe u e) where
    private
      U★ = U★_ e

    ⊏-refl : U ⊏ U
    ⊏-refl = mk _ λ _ → ≃-refl

    𝟘⊏_ : U𝟘 ⊏ U
    𝟘⊏_ = mk (λ()) (λ())

    _⊏★ : U ⊏ U★
    _⊏★ = mk (El U) λ _ → ≃-refl

    -- derived...

    idMap : Map U U
    idMap = ⊏-Map ⊏-refl

    idCoMap : CoMap U U
    idCoMap = ⊏-CoMap ⊏-refl

    Map𝟘 : Map U𝟘 U
    Map𝟘 = ⊏-Map 𝟘⊏_

    CoMap𝟘 : CoMap U𝟘 U
    CoMap𝟘 = ⊏-CoMap 𝟘⊏_

    Map★ : Map U U★
    Map★ = ⊏-Map _⊏★

    CoMap★ : CoMap U U★
    CoMap★ = ⊏-CoMap _⊏★

module _ {a b}{F : ★_ a → ★_ b} where
    mapF : (∀ {A} → A → F A) → Map (U★ a) (U★ b)
    mapF = mk F

    coMapF : (∀ {A} → F A → A) → CoMap (U★ a) (U★ b)
    coMapF = mk F

module _ {a}{F : ★_ a → ★_ a} where
    ⊏F : (∀ A → A ≃ F A) → U★ a ⊏ U★ a
    ⊏F = mk F

module _ {e u v w}{U : Universe u e}
                  {V : Universe v e}
                  {W : Universe w e} where
  ⊏-trans : U ⊏ V → V ⊏ W → U ⊏ W
  ⊏-trans (mk _ UV) (mk _ VW) = mk _ λ _ → ≃-trans (UV _) (VW _)

  -- could be more lax on univ levels
  Map-∘ : Map U V → Map V W → Map U W
  Map-∘ (mk _ UV) (mk _ VW) = mk _ (VW ∘ UV)

  -- could be more lax on univ levels
  CoMap-∘ : CoMap U V → CoMap V W → CoMap U W
  CoMap-∘ (mk _ UV) (mk _ VW) = mk _ (UV ∘ VW)

module _ {e u v}(U : Universe u e)(V : Universe v e) where
  _⊎ᵁ_ : Universe (u ⊔ v) e
  _⊎ᵁ_ = record { El = [inl: El U ,inr: El V ] }

  _×ᵁ_ : Universe (u ⊔ v) e
  _×ᵁ_ = record { El = λ { (A , B) → El U A × El V B } }

module _ {e u v}(U : Universe u e)(V : Universe v e) where
  inlᵁ : U ⊏ (U ⊎ᵁ V)
  inlᵁ = mk inl λ _ → ≃-refl

  inrᵁ : V ⊏ (U ⊎ᵁ V)
  inrᵁ = mk inr λ _ → ≃-refl

  fstᵁ : Map (U ×ᵁ V) U
  fstᵁ = mk fst fst

  sndᵁ : Map (U ×ᵁ V) V
  sndᵁ = mk snd snd

module _
  {u e}(U : Universe u e)
  {p}(P : Code U → ★_ p)
  where
    Σᵁ : Universe (u ⊔ p) e
    Σᵁ = record { U = Σ (Code U) P; El = El U ∘ fst }

    Σᵁ-fst : CoMap Σᵁ U
    Σᵁ-fst = mk fst id

{-
module _
  {u e}(U : Universe u e)
  {b}(B : ★_ b)
  where
    Πᵁ' : Universe u (e ⊔ b)
    Πᵁ' = record { U = Code U ; El = λ A → B → El U A }

    todo' : B → CoMap U Πᵁ'
    todo' b = mk id (λ f → f b)

module _
  {u e}(U : Universe u e)
  (F : ★_ e → ★_ e)
  where
  bla : (∀ {A} → El U A → F (El U A)) → Map U (record { El = F ∘ El U })
  bla = mk id

module _
  {u e}(U : Universe u e)
  {p}(P : ∀ {A} → El U A → ★_ p)
  where
    Πᵁ : Universe u (e ⊔ p)
    Πᵁ = record { U = Code U ; El = λ A → Π (El U A) P }

    todo : Map Πᵁ U
    todo = mk id {!!}
-}

module _
  {u e}(U : Universe u e)
  {p}(P : ∀ {A} → El U A → ★_ p)
  where
    ΣEl : Code U → ★_ _
    ΣEl A = Σ (El U A) P

    ΣElᵁ : Universe u (e ⊔ p)
    ΣElᵁ = record { El = ΣEl }

    ΣEl-fst : CoMap U ΣElᵁ
    ΣEl-fst = mk id fst

-- TODO: Move elsewhere
Finite : ★₀ → ★₁
Finite A = Σ ℕ λ n → A ≡ Fin n

UFinite : Universe _ _
UFinite = Σᵁ U★₀ Finite

finite : CoMap UFinite U★₀
finite = Σᵁ-fst U★₀ Finite
-- -}
-- -}
-- -}
-- -}
