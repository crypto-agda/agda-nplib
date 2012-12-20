open import Type            hiding (★)
open import Level           using (_⊔_; suc; Level)
open import Function.NP     using (id; const; _∘_; _∘′_; _ˢ_; _⟨_⟩°_)
open import Data.Sum        using (_⊎_; inj₁; inj₂)
open import Data.Bool       using (Bool; true; false)
open import Data.Unit       using (⊤)
open import Data.List       using (List; []; _∷_)
open import Data.Maybe      using (Maybe; nothing; just)
open import Data.Empty      using (⊥)
open import Data.Product.NP using (∃; _,_; _×_)

module Data.Indexed {i} {Ix : ★ i} where

★° : ∀ ℓ → ★ _
★° ℓ = Ix → ★ ℓ

★₀° : ★ _
★₀° = Ix → ★₀

★₁° : ★ _
★₁° = Ix → ★₂

∀° : ∀ {f} (F : ★° f) → ★ _
∀° F = ∀ {x} → F x

∃° : ∀ {f} (F : ★° f) → ★ _
∃° F = ∃[ x ] F x

pure° : ∀ {a} {A : ★ a} → A → (Ix → A)
pure° = const

-- an alias for pure°
K° : ∀ {a} (A : ★ a) → ★° _
K° = pure°

Cmp° : (F : ★° _) (i j : Ix) → ★₀
Cmp° F i j = F i → F j → Bool

Π° : ∀ {f g} (F : ★° f) (G : ∀ {i} → F i → ★° g) → ★° _
Π° F G i = (x : F i) → G x i

-- this version used to work (type-checking its uses) better than that
infixr 0 _→°_
_→°_ : ∀ {f g} (F : ★° f) (G : ★° g) → ★° (f ⊔ g)
F →° G = Π° F (const G)
-- expanded: (F →° G) i = F i → G i

infixr 0 _↦°_
_↦°_ : ∀ {f g} (F : ★° f) (G : ★° g) → ★ _
(F ↦° G) = ∀°(F →° G)

id° : ∀ {f} {F : ★° f} → F ↦° F
id° = id

_∘°_ : ∀ {f g h} {F : ★° f} {G : ★° g} {H : ★° h} → G ↦° H → F ↦° G → F ↦° H
f ∘° g = f ∘ g

infixr 0 _$°_ _$°′_

_$°_ : ∀ {f g} {F : ★° f} {G : ∀ {i} → F i → ★° g}
        → Π° F G ↦° Π° F G
_$°_ = id

_$°′_ : ∀ {f g} {F : ★° f} {G : ★° g}
        → ∀° ((F →° G) →° F →° G)
_$°′_ = id

infixl 4 _⊛°_

_⊛°_ : ∀ {a b} {A : ★ a} {B : ★ b}
         → (Ix → A → B) → ((Ix → A) → (Ix → B))
_⊛°_ = _ˢ_

liftA° : ∀ {a b} {A : ★ a} {B : ★ b}
          → (A → B) → ((Ix → A) → (Ix → B))
liftA° = _∘′_
-- liftA° f x = pure° f ⊛° x

liftA₂° : ∀ {a b c} {A : ★ a} {B : ★ b} {C : ★ c}
           → (A → B → C)
           → ((Ix → A) → (Ix → B) → (Ix → C))
liftA₂° f x y = x ⟨ f ⟩° y
-- liftA₂° f x y = pure° f ⊛° x ⊛° y

List° : ∀ {a} → ★° a → ★° a
List° = liftA° List

[]° : ∀ {f} {F : ★° f} → ∀°(List° F)
[]° = []

_∷°_ : ∀ {f} {F : ★° f} → ∀°(F →° List° F →° List° F)
_∷°_ = _∷_

Maybe° : ∀ {a} → ★° a → ★° a
Maybe° = liftA° Maybe

nothing° : ∀ {f} {F : ★° f} → ∀°(Maybe° F)
nothing° = nothing

just° : ∀ {f} {F : ★° f} → ∀°(F →° Maybe° F)
just° = just

infixr 2 _×°_
_×°_ : ∀ {f g} (F : ★° f) (G : ★° g) → ★° _
_×°_ = liftA₂° _×_

_,°_ : ∀ {f g} {F : ★° f} {G : ★° g} → ∀° (F →° G →° F ×° G)
_,°_ = _,_

pack° : ∀ {f} {F : ★° f} → (x : Ix) → F x → ∃° F
pack° = _,_

infixr 1 _⊎°_

_⊎°_ : ∀ {f g} (F : ★° f) (G : ★° g) → ★° _
_⊎°_ = liftA₂° _⊎_

inj₁° : ∀ {f g} {F : ★° f} {G : ★° g} → F ↦° F ⊎° G
inj₁° = inj₁

inj₂° : ∀ {f g} {F : ★° f} {G : ★° g} → G ↦° F ⊎° G
inj₂° = inj₂

⊤° : ★° _
⊤° = pure° ⊤

⊥° : ★° _
⊥° = pure° ⊥

¬° : ∀ {ℓ} → ★° ℓ → ★° _
¬° F = F →° ⊥°

-- This is the type of |map| functions, the fmap function on Ix-indexed
-- functors.
Map° : ∀ {a a' b b'} (F : ★° a → ★° a')
                     (G : ★° b → ★° b') → ★ _
Map° F G = ∀ {A B} → (A ↦° B) → F A ↦° G B

map°-K° : ∀ {a a' b b'}
            {F : ★ a → ★ a'}
            {G : ★ b → ★ b'}
            (fmap : ∀ {A B} → (A → B) → F A → G B)
            {A B} → (K° A ↦° K° B) → K° (F A) ↦° K° (G B)
map°-K° fmap f {i} = fmap (f {i})
