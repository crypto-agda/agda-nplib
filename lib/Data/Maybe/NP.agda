{-# OPTIONS --without-K #-}
open import Type hiding (★)
open import Function
import Level as L
open L using (_⊔_; lift; Lift)
open import Algebra
open import Algebra.Structures
open import Algebra.FunctionProperties
open import Category.Applicative
import      Category.Monad as Cat
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_;_≗_)
open import Relation.Nullary
open import Relation.Binary
open import Function using (_$_;flip;id)
open import Data.Product
open import Data.Zero using (𝟘; 𝟘-elim)
open import Data.One using (𝟙)
open import Data.Nat using (ℕ; zero; suc; _+_)
module Data.Maybe.NP where

open import Data.Maybe public

Π? : ∀ {a b} (A : ★ a) (B : A → ★ b) → ★ _
Π? A B = (x : A) → Maybe (B x)

infixr 0 _→?_
_→?_ : ∀ {a b} → ★ a → ★ b → ★ _
A →? B = A → Maybe B

module M? ℓ where
  open Cat.RawMonadPlus (monadPlus {ℓ}) public
  applicative = rawIApplicative

open M? public using (applicative)

infixl 4 _⊛?_

-- More universe-polymorphic than M?._⊛_
_⊛?_ : ∀ {a b}{A : ★ a}{B : ★ b} → Maybe (A → B) → Maybe A → Maybe B
just f  ⊛? just x = just (f x)
_       ⊛? _      = nothing

infixl 1 _>>=?_

-- More universe-polymorphic than M?._>>=_
_>>=?_ : ∀ {a b} {A : ★ a} {B : ★ b} → Maybe A → (A → Maybe B) → Maybe B
mx >>=? f = maybe f nothing mx

infixr 1 _=<<?_

-- More universe-polymorphic than M?._=<<_
_=<<?_ : ∀ {a b} {A : ★ a} {B : ★ b} → (A → Maybe B) → Maybe A → Maybe B
f =<<? mx = mx >>=? f

-- More universe-polymorphic than M?._<$>_
map? : ∀ {a b} {A : ★ a} {B : ★ b} → (A → B) → Maybe A → Maybe B
map? f mx = mx >>=? (just ∘ f)

_<$?_ : ∀ {a b} {A : ★ a} {B : ★ b} → A → Maybe B → Maybe A
_<$?_ x = map? (const x)

⟪_·_⟫? : ∀ {a b} {A : ★ a} {B : ★ b} → (A → B) → Maybe A → Maybe B
⟪ f · x ⟫? = map? f x

⟪_·_·_⟫? : ∀ {a b c}
             {A : ★ a} {B : ★ b} {C : ★ c} →
             (A → B → C) → Maybe A → Maybe B → Maybe C
⟪ f · x · y ⟫? = map? f x ⊛? y

⟪_·_·_·_⟫? : ∀ {a b c d}
               {A : ★ a} {B : ★ b} {C : ★ c} {D : ★ d}
             → (A → B → C → D)
             → Maybe A → Maybe B → Maybe C → Maybe D
⟪ f · x · y · z ⟫? = map? f x ⊛? y ⊛? z

join? : ∀ {a} {A : ★ a} → Maybe (Maybe A) → Maybe A
join? = _=<<?_ id

Maybe^ : ∀ {a} → ℕ → ★ a → ★ a
Maybe^ zero    = id
Maybe^ (suc n) = Maybe ∘ Maybe^ n

just^ : ∀ {a} {A : ★ a} n → A → Maybe^ n A
just^ zero x = x
just^ (suc n) x = just (just^ n x)

Maybe^-∘-+ : ∀ {a} m n (A : ★ a) → Maybe^ m (Maybe^ n A) ≡ Maybe^ (m + n) A
Maybe^-∘-+ zero    _ _ = ≡.refl
Maybe^-∘-+ (suc m) _ _ = ≡.cong Maybe (Maybe^-∘-+ m _ _)

just-injective : ∀ {a} {A : ★ a} {x y : A}
                 → Maybe.just x ≡ just y → x ≡ y
just-injective ≡.refl = ≡.refl

maybe-just-nothing : ∀ {a} {A : ★ a} → maybe {A = A} just nothing ≗ id
maybe-just-nothing (just _)  = ≡.refl
maybe-just-nothing nothing   = ≡.refl

_≡JAll_ : ∀ {a} {A : ★ a} (x y : Maybe A) → ★ a
x ≡JAll y = All (λ y' → All (_≡_ y') y) x

_≡JAny_ : ∀ {a} {A : ★ a} (x y : Maybe A) → ★ a
x ≡JAny y = Any (λ y' → Any (_≡_ y') y) x

≡JAll-refl : ∀ {a} {A : ★ a} {x : Maybe A} → x ≡JAll x
≡JAll-refl {x = just x}  = just (just ≡.refl)
≡JAll-refl {x = nothing} = nothing

just? : ∀ {a} {A : ★ a} → Maybe A → ★₀
just? nothing  = 𝟘
just? (just _) = 𝟙

just?→Is-just : ∀ {a} {A : ★ a} {x : Maybe A} → just? x → Is-just x
just?→Is-just {x = just _}  p = just _
just?→Is-just {x = nothing} ()

Any→just? : ∀ {a p} {A : ★ a} {P : A → ★ p} {x} → Any P x → just? x
Any→just? (just _) = _

Any-join? : ∀ {a p} {A : ★ a} {P : A → ★ p} {x} → Any (Any P) x → Any P (join? x)
Any-join? (just p) = p

All-join? : ∀ {a p} {A : ★ a} {P : A → ★ p} {x} → All (All P) x → All P (join? x)
All-join? (just p) = p
All-join? nothing  = nothing

Any-join?′ : ∀ {a p} {A : ★ a} {P : A → ★ p} {x} → Any P (join? x) → Any (Any P) x
Any-join?′ {x = just x}  p = just p
Any-join?′ {x = nothing} ()

All-join?′ : ∀ {a p} {A : ★ a} {P : A → ★ p} {x} → All P (join? x) → All (All P) x
All-join?′ {x = just x}  p       = just p
All-join?′ {x = nothing} nothing = nothing

Any→Is-just : ∀ {a p} {A : ★ a} {P : A → ★ p} {x} → Any P x → Is-just x
Any→Is-just (just _) = just _

just≡→just? : ∀ {a} {A : ★ a} {x} {y : A} → x ≡ just y → just? x
just≡→just? ≡.refl = _

just?-join? : ∀ {a} {A : ★ a} {x : Maybe (Maybe A)} → just? (join? x) → just? x
just?-join? = Any→just? ∘ Any-join?′ ∘ just?→Is-just

Any-just?-join? : ∀ {A : ★₀} (x : Maybe (Maybe A)) → just? (join? x) → Any just? x
Any-just?-join? (just (just _)) _ = just _
Any-just?-join? (just nothing)  ()
Any-just?-join? nothing         ()

just?-map? : ∀ {a b} {A : ★ a} {B : ★ b} (f : A → B)
               (x : Maybe A) → just? (map? f x) → just? x
just?-map? f (just x) pf = _
just?-map? f nothing  ()

infix 4 _≗?_

_≗?_ : ∀ {a b} {A : ★ a} {B : ★ b} →
         (f g : A →? B) → ★ _
(f ≗? g) = ∀ x → f x ≡JAll g x

_∘?_ : ∀ {a b c} {A : ★ a} {B : ★ b} {C : ★ c}
       → B →? C → A →? B → A →? C
(f ∘? g) x = g x >>=? f

∘?-just : ∀ {a b} {A : ★ a} {B : ★ b} →
            (f : A →? B) → f ∘? just ≗? f
∘?-just f x = ≡JAll-refl

just-∘? : ∀ {a b} {A : ★ a} {B : ★ b} →
            (f : A →? B) → just ∘? f ≗? f
just-∘? f x with f x
just-∘? f x | just _  = just (just ≡.refl)
just-∘? f x | nothing = nothing

∘?-assoc : ∀ {a b c d} {A : ★ a} {B : ★ b} {C : ★ c} {D : ★ d}
             (f : C →? D) (g : B →? C) (h : A →? B)
             → (f ∘? g) ∘? h ≗ f ∘? (g ∘? h)
∘?-assoc f g h x with h x
∘?-assoc f g h x | just _  = ≡.refl
∘?-assoc f g h x | nothing = ≡.refl

T[_] : ∀ {a b} {A : ★ a} {B : ★ b} (f? : A →? B) → ★ (a L.⊔ b)
T[_] {A = A} {B} f? = (x : A) → .{pf : just? (f? x)} → B

F[_] : ∀ {a b} {A : ★ a} {B : ★ b} (f? : A →? B) → T[ f? ]
F[ f? ] x {pf} with f? x
F[ f? ] x      | just r  = r
F[ f? ] x {()} | nothing

T'[_] : ∀ {a b} {A : ★ a} {B : ★ b} (f? : A →? B) → ★ (a L.⊔ b)
T'[_] {A = A} {B} f? = (x : A) → Is-just (f? x) → B

F'[_] : ∀ {a b} {A : ★ a} {B : ★ b} (f? : A →? B) → T'[ f? ]
F'[ f? ] x pf with f? x
F'[ f? ] x (just {y} _) | .(just y) = y

-- F[ f? ] ⟶ F'[ f? ]

module F[] where
    _[≗]_ : ∀ {a b} {A : ★ a} {B : ★ b}
              {f? g? : A →? B}
              (f : T[ f? ]) (g : T[ g? ]) → ★ _
    f [≗] g = ∀ x {pf1} {pf2} → f x {pf1} ≡ g x {pf2}

    [id] : ∀ {a} {A : ★ a} → T[ just {A = A} ]
    [id] = F[ just ]

    {- might actually be wrong
    []-just-≡ : ∀ {a b} {A : ★ a} {B : ★ b} {f? : A →? B} (f : T[ f? ]) {x} (pf : just? (f? x)) → just (f x {pf}) ≡ f? x
    []-just-≡ {f? = f?} f {x} pf = {!!}
    -}

    _[∘]_ : ∀ {a b c} {A : ★ a} {B : ★ b} {C : ★ c}
              {f? : B →? C} {g? : A →? B}
            → T[ f? ] → T[ g? ] → T[ f? ∘? g? ]
    _[∘]_ {f? = f?} {g?} f g x {pf} with g? x
    _[∘]_ f g x {pf} | just y  = f y {pf}
    _[∘]_ f g x {()} | nothing

    {-
    [id]-[∘] : ∀ {a b} {A : ★ a} {B : ★ b}
                 {f? : A →? B} (f : T[ f? ]) → (F[ just ] [∘] f) [≗] f
    [id]-[∘] {f? = f?} f x {pf1} {pf2} = just-injective {!(≡.sym (≡.trans ([]-just-≡ f pf2) ?))!}
    -}

    [∘]-[id] : ∀ {a b} {A : ★ a} {B : ★ b}
                 {f? : A →? B} (f : T[ f? ]) → (f [∘] [id]) [≗] f
    [∘]-[id] {f? = f?} f x {pf1} {pf2} = ≡.refl

Is-nothing-≡nothing : ∀ {a} {A : ★ a} {x : Maybe A} → Is-nothing x → x ≡ nothing
Is-nothing-≡nothing nothing = ≡.refl
Is-nothing-≡nothing (just ())

≡nothing-Is-nothing : ∀ {a} {A : ★ a} {x : Maybe A} → x ≡ nothing → Is-nothing x
≡nothing-Is-nothing ≡.refl = nothing

module FunctorLemmas {a} where
  open M? a

  <$>-injective₁ : ∀ {A B}
                     {f : A → B} {x y : Maybe A}
                     (f-inj : ∀ {x y} → f x ≡ f y → x ≡ y)
                   → f <$> x ≡ f <$> y → x ≡ y
  <$>-injective₁ {x = just _}  {just _}  f-inj eq = ≡.cong just (f-inj (just-injective eq))
  <$>-injective₁ {x = nothing} {nothing} _     _  = ≡.refl
  <$>-injective₁ {x = just _}  {nothing} _     ()
  <$>-injective₁ {x = nothing} {just _}  _     ()

  <$>-assoc : ∀ {A B C} {f : A → B} {g : C → A} (x : Maybe C) → f ∘ g <$> x ≡ f <$> (g <$> x)
  <$>-assoc (just _) = ≡.refl
  <$>-assoc nothing  = ≡.refl

module MonadLemmas {a} where

  open M? a public
 --  open RawApplicative applicative public

  cong-Maybe : ∀ {A B}
                 (f : A → B) {x y} → x ≡ pure y → f <$> x ≡ pure (f y)
  cong-Maybe f ≡.refl = ≡.refl

  cong₂-Maybe : ∀ {A B C}
                  (f : A → B → C) {x y u v} → x ≡ pure y → u ≡ pure v → pure f ⊛ x ⊛ u ≡ pure (f y v)
  cong₂-Maybe f ≡.refl ≡.refl = ≡.refl

  Maybe-comm-monad :
    ∀ {A B C} {x y} {f : A → B → Maybe C} →
      (x >>= λ x' → y >>= λ y' → f x' y')
    ≡ (y >>= λ y' → x >>= λ x' → f x' y')
  Maybe-comm-monad {x = nothing} {nothing}  = ≡.refl
  Maybe-comm-monad {x = nothing} {just _}   = ≡.refl
  Maybe-comm-monad {x = just _}  {nothing}  = ≡.refl
  Maybe-comm-monad {x = just _}  {just _}   = ≡.refl

  Maybe-comm-appl : ∀ {A B} {f : Maybe (A → B)} {x} → f ⊛ x ≡ (flip _$_) <$> x ⊛ f
  Maybe-comm-appl {f = nothing} {nothing}  = ≡.refl
  Maybe-comm-appl {f = nothing} {just _}   = ≡.refl
  Maybe-comm-appl {f = just _}  {nothing}  = ≡.refl
  Maybe-comm-appl {f = just _}  {just _}   = ≡.refl

  Maybe-comm-appl₂ : ∀ {A B C} {f : A → B → C} {x y} → f <$> x ⊛ y ≡ flip f <$> y ⊛ x
  Maybe-comm-appl₂ {x = nothing} {nothing}  = ≡.refl
  Maybe-comm-appl₂ {x = nothing} {just _}   = ≡.refl
  Maybe-comm-appl₂ {x = just _}  {nothing}  = ≡.refl
  Maybe-comm-appl₂ {x = just _}  {just _}   = ≡.refl

module MonoidFromSemigroup {c ℓ} (sg   : Semigroup c ℓ)
                                 {_≈?_ : let open Semigroup sg
                                         in Maybe Carrier → Maybe Carrier → ★ ℓ}
                                 (isEquivalence : IsEquivalence _≈?_)
                                 (just-cong : let open Semigroup sg in
                                              just Preserves _≈_ ⟶ _≈?_)
                                 (just-inj  : let open Semigroup sg in
                                              (_≈?_ on just) ⇒ _≈_)
                                 (just≉nothing : ∀ {x} → ¬(just x ≈? nothing)) where
  private
    module SG = Semigroup sg
    open SG using (_≈_) renaming (Carrier to A; _∙_ to op)
    module ≈  = IsEquivalence SG.isEquivalence
    module ≈? = IsEquivalence isEquivalence
    _∙_ : Op₂ (Maybe A)
    just x  ∙ just y  = just (op x y)
    just x  ∙ nothing = just x
    nothing ∙ y?      = y?

    ε : Maybe A
    ε = nothing

    assoc : Associative _≈?_ _∙_
    assoc (just x) (just y) (just z) = just-cong (SG.assoc x y z)
    assoc (just _) (just _) nothing  = ≈?.refl
    assoc (just _) nothing  _        = ≈?.refl
    assoc nothing  _        _        = ≈?.refl

    right-identity : RightIdentity _≈?_ ε _∙_
    right-identity (just _) = ≈?.refl
    right-identity nothing  = ≈?.refl

    ∙-cong : _∙_ Preserves₂ _≈?_ ⟶ _≈?_ ⟶ _≈?_
    ∙-cong {just _}{just _}{just _}{just _}   p q
      = just-cong (SG.∙-cong (just-inj p) (just-inj q))
    ∙-cong {just _}{just _}{just _}{nothing}  p q = 𝟘-elim (just≉nothing q)
    ∙-cong {just _}{just _}{nothing}{just _}  p q = 𝟘-elim (just≉nothing (≈?.sym q))
    ∙-cong {just _}{just _}{nothing}{nothing} p q = p
    ∙-cong {nothing} {nothing} p q = q
    ∙-cong {just _}  {nothing} p q = 𝟘-elim (just≉nothing p)
    ∙-cong {nothing} {just _}  p q = 𝟘-elim (just≉nothing (≈?.sym p))

  monoid : Monoid c ℓ
  monoid = record { Carrier = Maybe A
                  ; _≈_ = _≈?_
                  ; _∙_ = _∙_
                  ; ε = ε
                  ; isMonoid
                    = record { isSemigroup
                               = record { isEquivalence = isEquivalence
                                        ; assoc = assoc; ∙-cong = ∙-cong }
                             ; identity = (λ _ → ≈?.refl) , right-identity } }

  open Monoid monoid public

module Monoid-≡ {a} {A : ★ a} {op : Op₂ A} (isSg : IsSemigroup _≡_ op)
  = MonoidFromSemigroup (record { isSemigroup = isSg })
                        ≡.isEquivalence (≡.cong just) just-injective

module First-≈ {a ℓ} {A : ★ a} {_≈_ : Maybe A → Maybe A → ★ ℓ}
               (isEquivalence : IsEquivalence _≈_)
               (just≉nothing : ∀ {x} → ¬(just x ≈ nothing)) where
  private
    module ≈ = IsEquivalence isEquivalence
    _∙_ : Op₂ (Maybe A)
    x ∙ y = maybe just y x

    ε : Maybe A
    ε = nothing

    assoc : Associative _≈_ _∙_
    assoc (just _) _ _ = ≈.refl
    assoc nothing  _ _ = ≈.refl

    right-identity : RightIdentity _≈_ ε _∙_
    right-identity (just _) = ≈.refl
    right-identity nothing  = ≈.refl

    ∙-cong : _∙_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
    ∙-cong {just _} {just _}   p q = p
    ∙-cong {nothing} {nothing} p q = q
    ∙-cong {just _} {nothing}  p q = 𝟘-elim (just≉nothing p)
    ∙-cong {nothing} {just _}  p q = 𝟘-elim (just≉nothing (≈.sym p))

  monoid : Monoid a ℓ
  monoid = record { Carrier = Maybe A
                  ; _≈_ = _≈_
                  ; _∙_ = _∙_
                  ; ε = ε
                  ; isMonoid
                    = record { isSemigroup
                               = record { isEquivalence = isEquivalence
                                        ; assoc = assoc; ∙-cong = ∙-cong }
                             ; identity = (λ _ → ≈.refl) , right-identity } }

  open Monoid monoid public

module First {a} (A : ★ a) = First-≈ {A = A} ≡.isEquivalence (λ())
-- -}
