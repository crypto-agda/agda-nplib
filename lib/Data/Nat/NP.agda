{-# OPTIONS --without-K #-}
module Data.Nat.NP where

open import Type hiding (★)
import Algebra
open import Algebra.FunctionProperties.NP
open import Data.Two.Base hiding (_==_; _²)
open import Data.Product using (∃; _,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (map to ⊎-map)
open import Data.Zero using (𝟘-elim; 𝟘)
open import Data.One using (𝟙)
open import Function.NP
open import Function.Extensionality
open import Relation.Nullary
open import Relation.Binary.NP
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≢_; _≗_; module ≡-Reasoning; !_; _∙_; ap; ap₂; coe)
       renaming (refl to idp)
open import HoTT
open Equivalences

open import Data.Nat public hiding (module GeneralisedArithmetic; module ≤-Reasoning; fold)
open import Data.Nat.Properties

pattern 1+_ x = suc x
pattern 2+_ x = 1+ suc x
pattern 3+_ x = 2+ suc x
pattern 4+_ x = 3+ suc x

⟨0↔1⟩ : ℕ → ℕ
⟨0↔1⟩ 0 = 1
⟨0↔1⟩ 1 = 0
⟨0↔1⟩ n = n

private
  _² : ∀ {A : ★₀} → Endo (Endo A)
  f ² = f ∘ f

⟨0↔1⟩-involutive : ⟨0↔1⟩ ∘ ⟨0↔1⟩ ≗ id
⟨0↔1⟩-involutive 0             = idp
⟨0↔1⟩-involutive 1             = idp
⟨0↔1⟩-involutive (suc (suc _)) = idp

⇑⟨_⟩ : (ℕ → ℕ) → (ℕ → ℕ)
⇑⟨ f ⟩ zero    = zero
⇑⟨ f ⟩ (suc n) = suc (f n)

⟨0↔1+_⟩ : ℕ → ℕ → ℕ
⟨0↔1+ 0     ⟩ = ⟨0↔1⟩
⟨0↔1+ suc n ⟩ = ⟨0↔1⟩ ∘ ⇑⟨ ⟨0↔1+ n ⟩ ⟩ ∘ ⟨0↔1⟩

⟨_↔+1⟩ : ℕ → ℕ → ℕ
⟨ 0     ↔+1⟩ = ⟨0↔1⟩
⟨ suc n ↔+1⟩ 0       = 0
⟨ suc n ↔+1⟩ (suc m) = suc (⟨ n ↔+1⟩ m)

⟨_↔+1⟩-involutive : ∀ n → ⟨ n ↔+1⟩ ∘ ⟨ n ↔+1⟩ ≗ id
⟨_↔+1⟩-involutive 0 = ⟨0↔1⟩-involutive
⟨_↔+1⟩-involutive (suc _) 0       = idp
⟨_↔+1⟩-involutive (suc n) (suc m) = ap suc (⟨ n ↔+1⟩-involutive m)

⟨_↔+1⟩-equiv : ℕ → ℕ ≃ ℕ
⟨ n ↔+1⟩-equiv = self-inv-equiv ⟨ n ↔+1⟩ ⟨ n ↔+1⟩-involutive

⇑⟨_⟩-involutive : ∀ {f} → f ² ≗ id → ⇑⟨ f ⟩ ² ≗ id
⇑⟨ f²id ⟩-involutive zero    = idp
⇑⟨ f²id ⟩-involutive (suc x) = ap suc (f²id x)

⟨0↔1+_⟩-involutive : ∀ n → ⟨0↔1+ n ⟩ ² ≗ id
⟨0↔1+_⟩-involutive zero = ⟨0↔1⟩-involutive
⟨0↔1+_⟩-involutive (suc n) x = ap (⟨0↔1⟩ ∘ ⇑⟨ ⟨0↔1+ n ⟩ ⟩) (⟨0↔1⟩-involutive (⇑⟨ ⟨0↔1+ n ⟩ ⟩ (⟨0↔1⟩ x)))
  ∙ ap ⟨0↔1⟩ (⇑⟨ ⟨0↔1+ n ⟩-involutive ⟩-involutive (⟨0↔1⟩ x)) ∙ ⟨0↔1⟩-involutive x

module _ {{_ : UA}} where
    ⟨_↔+1⟩-eq : ℕ → ℕ ≡ ℕ
    ⟨_↔+1⟩-eq = ua ∘ ⟨_↔+1⟩-equiv

    ⟨_↔+1⟩-eq-β : ∀ n m → coe ⟨ n ↔+1⟩-eq m ≡ ⟨ n ↔+1⟩ m
    ⟨_↔+1⟩-eq-β = coe-β ∘ ⟨_↔+1⟩-equiv

ℕˢ = ≡.setoid ℕ

module ℕcmp = StrictTotalOrder strictTotalOrder
module ℕ≤   = DecTotalOrder decTotalOrder
module ℕ°   = Algebra.CommutativeSemiring commutativeSemiring
module ℕ+   = Algebra.CommutativeMonoid ℕ°.+-commutativeMonoid
module ℕ+′  = Algebra.Monoid ℕ°.+-monoid
module ⊔°   = Algebra.CommutativeSemiringWithoutOne ⊔-⊓-0-commutativeSemiringWithoutOne
module ℕˢ   = Setoid ℕˢ

infixr 8 _∙≤_
_∙≤_ = ℕ≤.trans
_∙cmp_ = ℕcmp.trans
_∙<_ = <-trans

[P:_zero:_suc:_] : ∀ {p} (P : ℕ → ★ p) → P zero → (∀ {n} → P n → P (suc n)) → ∀ n → P n
[P: _ zero: z suc: _ ] zero    = z
[P: P zero: z suc: s ] (suc n) = s ([P: P zero: z suc: s ] n)

[zero:_suc:_] : ∀ {a} {A : ★ a} → A → (ℕ → A → A) → ℕ → A
[zero: z suc: s ] = [P: _ zero: z suc: (λ {n} → s n) ]

module ≤-Reasoning where
  open Preorder-Reasoning ℕ≤.preorder public renaming (_∼⟨_⟩_ to _≤⟨_⟩_)
  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ x {y z : ℕ} → x ≡ y → y ≤ z → x ≤ z
  _ ≡⟨ idp ⟩ p = p
  infixr 2 _<⟨_⟩_
  _<⟨_⟩_ : ∀ x {y z : ℕ} → x < y → y ≤ z → x < z
  x <⟨ p ⟩ q = suc x ≤⟨ p ⟩ q

suc-injective : ∀ {n m : ℕ} → ℕ.suc n ≡ suc m → n ≡ m
suc-injective = ap pred

+-≤-inj : ∀ x {y z} → x + y ≤ x + z → y ≤ z
+-≤-inj zero    = id
+-≤-inj (suc x) = +-≤-inj x ∘ ≤-pred

infixl 6 _+°_
infixl 7 _*°_ _⊓°_
infixl 6 _∸°_ _⊔°_

_+°_ : ∀ {a} {A : ★ a} (f g : A → ℕ) → A → ℕ
(f +° g) x = f x + g x

_∸°_ : ∀ {a} {A : ★ a} (f g : A → ℕ) → A → ℕ
(f ∸° g) x = f x ∸ g x

_*°_ : ∀ {a} {A : ★ a} (f g : A → ℕ) → A → ℕ
(f *° g) x = f x * g x

_⊔°_ : ∀ {a} {A : ★ a} (f g : A → ℕ) → A → ℕ
(f ⊔° g) x = f x ⊔ g x

_⊓°_ : ∀ {a} {A : ★ a} (f g : A → ℕ) → A → ℕ
(f ⊓° g) x = f x ⊓ g x

-- this one is not completly in line with the
-- others
_≤°_ : ∀ {a} {A : ★ a} (f g : A → ℕ) → ★ a
f ≤° g = ∀ x → f x ≤ g x

sucx≰x : ∀ x → suc x ≰ x
sucx≰x zero    = λ()
sucx≰x (suc x) = sucx≰x x ∘ ≤-pred

total-≤ : ∀ a b → a ≤ b ⊎ b ≤ a
total-≤ zero b = inj₁ z≤n
total-≤ (suc a) zero = inj₂ z≤n
total-≤ (suc a) (suc b) with total-≤ a b
... | inj₁ p = inj₁ (s≤s p)
... | inj₂ p = inj₂ (s≤s p)

a≡a⊓b+a∸b : ∀ a b → a ≡ a ⊓ b + (a ∸ b)
a≡a⊓b+a∸b zero zero = idp
a≡a⊓b+a∸b zero (suc b) = idp
a≡a⊓b+a∸b (suc a) zero = idp
a≡a⊓b+a∸b (suc a) (suc b) rewrite ! a≡a⊓b+a∸b a b = idp

¬n≤x<n : ∀ n {x} → n ≤ x → x < n → 𝟘
¬n≤x<n n p q = sucx≰x _ (q ∙≤ p)

¬n+≤y<n : ∀ n {x y} → n + x ≤ y → y < n → 𝟘
¬n+≤y<n n p q = sucx≰x _ (q ∙≤ ℕ≤.reflexive (ℕ°.+-comm 0 n) ∙≤ ℕ≤.refl {n} +-mono z≤n ∙≤ p)

fold : ∀ {a} {A : ★ a} → A → Endo A → ℕ → A
fold x f n = nest n f x

module nest-Properties {a} {A : ★ a} (f : Endo A) where
  nest₀ : nest 0 f ≡ id
  nest₀ = idp
  nest₁ : nest 1 f ≡ f
  nest₁ = idp
  nest₂ : nest 2 f ≡ f ∘ f
  nest₂ = idp
  nest₃ : nest 3 f ≡ f ∘ f ∘ f
  nest₃ = idp

  nest-+ : ∀ m n → nest (m + n) f ≡ nest m f ∘ nest n f
  nest-+ zero    n = idp
  nest-+ (suc m) n = ap (_∘_ f) (nest-+ m n)

  nest-+' : ∀ m n → nest (m + n) f ≗ nest m f ∘ nest n f
  nest-+' m n x = ap (flip _$_ x) (nest-+ m n)

  nest-* : ∀ m n → nest (m * n) f ≗ nest m (nest n f)
  nest-* zero n x = idp
  nest-* (suc m) n x =
    nest (suc m * n) f x             ≡⟨ idp ⟩
    nest (n + m * n) f x             ≡⟨ nest-+' n (m * n) x ⟩
    (nest n f ∘ nest (m * n) f) x    ≡⟨ ap (nest n f) (nest-* m n x) ⟩
    (nest n f ∘ nest m (nest n f)) x ≡⟨ idp ⟩
    nest n f (nest m (nest n f) x)   ≡⟨ idp ⟩
    nest (suc m) (nest n f) x ∎
   where open ≡-Reasoning

{- WRONG
module more-nest-Properties {a} {A : ★ a} where
  nest-+'' : ∀ (f : Endo (Endo A)) g m n → nest m f g ∘ nest n f g ≗ nest (m + n) f g
  nest-+'' f g zero n = {!!}
  nest-+'' f g (suc m) n = {!!}
-}

+-inj-over-∸ : ∀ x y z → (x + y) ∸ (x + z) ≡ y ∸ z
+-inj-over-∸ = [i+j]∸[i+k]≡j∸k 

2*_ : ℕ → ℕ
2* x = x + x

2*-spec : ∀ n → 2* n ≡ 2 * n
2*-spec n rewrite ℕ°.+-comm n 0 = idp

_==_ : (x y : ℕ) → 𝟚
zero   == zero   = 1₂
zero   == suc _  = 0₂
suc _  == zero   = 0₂
suc m  == suc n  = m == n

+-assoc-comm : ∀ x y z → x + (y + z) ≡ y + (x + z)
+-assoc-comm x y z = ! ℕ°.+-assoc x y z ∙ ap (flip _+_ z) (ℕ°.+-comm x y) ∙ ℕ°.+-assoc y x z

+-interchange : Interchange _≡_ _+_ _+_
+-interchange = InterchangeFromAssocCommCong.∙-interchange _≡_ ≡.isEquivalence
                                                           _+_ ℕ°.+-assoc ℕ°.+-comm (λ z → ap (flip _+_ z))

*-assoc-comm : ∀ x y z → x * (y * z) ≡ y * (x * z)
*-assoc-comm x y z = ! ℕ°.*-assoc x y z ∙ ap (flip _*_ z) (ℕ°.*-comm x y) ∙ ℕ°.*-assoc y x z

*-interchange : Interchange _≡_ _*_ _*_
*-interchange = InterchangeFromAssocCommCong.∙-interchange _≡_ ≡.isEquivalence
                                                           _*_ ℕ°.*-assoc ℕ°.*-comm (λ z → ap (flip _*_ z))

a+b≡a⊔b+a⊓b : ∀ a b → a + b ≡ a ⊔ b + a ⊓ b
a+b≡a⊔b+a⊓b zero    b       rewrite ℕ°.+-comm b 0 = idp
a+b≡a⊔b+a⊓b (suc a) zero    = idp
a+b≡a⊔b+a⊓b (suc a) (suc b) rewrite +-assoc-comm a 1 b
                                  | +-assoc-comm (a ⊔ b) 1 (a ⊓ b)
                                  | a+b≡a⊔b+a⊓b a b
                                  = idp

a⊓b≡a : ∀ {a b} → a ≤ b → a ⊓ b ≡ a
a⊓b≡a z≤n = idp
a⊓b≡a (s≤s a≤b) rewrite a⊓b≡a a≤b = idp

⊔≤+ : ∀ a b → a ⊔ b ≤ a + b
⊔≤+ zero b          = ℕ≤.refl
⊔≤+ (suc a) zero    = s≤s (ℕ≤.reflexive (ℕ°.+-comm 0 a))
⊔≤+ (suc a) (suc b) = s≤s (⊔≤+ a b ∙≤ ≤-step ℕ≤.refl ∙≤ ℕ≤.reflexive (+-assoc-comm 1 a b))

2*′_ : ℕ → ℕ
2*′_ = fold 0 (suc ∘′ suc)

2*′-spec : ∀ n → 2*′ n ≡ 2* n
2*′-spec zero = idp
2*′-spec (suc n) rewrite 2*′-spec n | +-assoc-comm 1 n n = idp

2^⟨_⟩* : ℕ → ℕ → ℕ
2^⟨ n ⟩* x = fold x 2*_ n

⟨2^_*_⟩ : ℕ → ℕ → ℕ
⟨2^ n * x ⟩ = 2^⟨ n ⟩* x

2*′-inj : ∀ {m n} → 2*′ m ≡ 2*′ n → m ≡ n
2*′-inj {zero}  {zero}  _ = idp
2*′-inj {zero}  {suc _} ()
2*′-inj {suc _} {zero}  ()
2*′-inj {suc m} {suc n} p = ap suc (2*′-inj (suc-injective (suc-injective p)))

2*-inj : ∀ {m n} → 2* m ≡ 2* n → m ≡ n
2*-inj {m} {n} p rewrite ! 2*′-spec m
                       | ! 2*′-spec n
                       = 2*′-inj p

2^-inj : ∀ k {m n} → ⟨2^ k * m ⟩ ≡ ⟨2^ k * n ⟩ → m ≡ n
2^-inj zero    = id
2^-inj (suc k) = 2^-inj k ∘ 2*-inj

2*-distrib : ∀ x y → 2* x + 2* y ≡ 2* (x + y) 
2*-distrib x y = +-interchange x x y y

2^*-distrib : ∀ k x y → ⟨2^ k * (x + y)⟩ ≡ ⟨2^ k * x ⟩ + ⟨2^ k * y ⟩
2^*-distrib zero x y = idp
2^*-distrib (suc k) x y rewrite 2^*-distrib k x y = ! 2*-distrib ⟨2^ k * x ⟩ ⟨2^ k * y ⟩

2^*-2*-comm : ∀ k x → ⟨2^ k * 2* x ⟩ ≡ 2* ⟨2^ k * x ⟩
2^*-2*-comm k x = 2^*-distrib k x x

2*-mono : ∀ {a b} → a ≤ b → 2* a ≤ 2* b
2*-mono pf = pf +-mono pf

2^*-mono : ∀ k {a b} → a ≤ b → ⟨2^ k * a ⟩ ≤ ⟨2^ k * b ⟩
2^*-mono zero    pf = pf
2^*-mono (suc k) pf = 2*-mono (2^*-mono k pf)

2*-mono′ : ∀ {a b} → 2* a ≤ 2* b → a ≤ b
2*-mono′ {zero} pf = z≤n
2*-mono′ {suc a} {zero} ()
2*-mono′ {suc a} {suc b} pf rewrite +-assoc-comm a 1 a
                                  | +-assoc-comm b 1 b = s≤s (2*-mono′ (≤-pred (≤-pred pf)))

2^*-mono′ : ∀ k {a b} → ⟨2^ k * a ⟩ ≤ ⟨2^ k * b ⟩ → a ≤ b
2^*-mono′ zero    = id
2^*-mono′ (suc k) = 2^*-mono′ k ∘ 2*-mono′

2^-comm : ∀ x y z → ⟨2^ x * ⟨2^ y * z ⟩ ⟩ ≡ ⟨2^ y * ⟨2^ x * z ⟩ ⟩
2^-comm zero y z = idp
2^-comm (suc x) y z rewrite 2^-comm x y z = ! 2^*-2*-comm y ⟨2^ x * z ⟩

2^-+ : ∀ x y z → ⟨2^ x * ⟨2^ y * z ⟩ ⟩ ≡ ⟨2^ (x + y) * z ⟩
2^-+ zero    y z = idp
2^-+ (suc x) y z = ap 2*_ (2^-+ x y z)

cancel-*-left : ∀ i j {k} → suc k * i ≡ suc k * j → i ≡ j
cancel-*-left i j {k}
  rewrite ℕ°.*-comm (suc k) i
        | ℕ°.*-comm (suc k) j = cancel-*-right i j {k}

2ⁿ*0≡0 : ∀ n → ⟨2^ n * 0 ⟩ ≡ 0
2ⁿ*0≡0 zero    = idp
2ⁿ*0≡0 (suc n) = ap₂ _+_ (2ⁿ*0≡0 n) (2ⁿ*0≡0 n)

0∸_≡0 : ∀ x → 0 ∸ x ≡ 0
0∸ zero  ≡0 = idp
0∸ suc x ≡0 = idp

2*-∸ : ∀ x y → 2* x ∸ 2* y ≡ 2* (x ∸ y)
2*-∸ _       zero    = idp
2*-∸ zero    (suc _) = idp
2*-∸ (suc x) (suc y) rewrite ! 2*-∸ x y | ℕ°.+-comm x (1 + x) | ℕ°.+-comm y (1 + y) = idp

n+k∸m : ∀ {m n} k → m ≤ n → n + k ∸ m ≡ (n ∸ m) + k
n+k∸m k z≤n = idp
n+k∸m k (s≤s m≤n) = n+k∸m k m≤n

factor-+-∸ : ∀ {b x y} → x ≤ b → y ≤ b → (b ∸ x) + (b ∸ y) ≡ 2* b ∸ (x + y)
factor-+-∸ {b} {zero} {y} z≤n y≤b rewrite ℕ°.+-comm b (b ∸ y) = ! n+k∸m b y≤b
factor-+-∸ (s≤s {x} {b} x≤b) z≤n             rewrite ℕ°.+-comm x 0 = ! n+k∸m (suc b) x≤b
factor-+-∸ (s≤s {x} {b} x≤b) (s≤s {y} y≤b)   rewrite factor-+-∸ x≤b y≤b
                                              | ℕ°.+-comm b (suc b)
                                              | ℕ°.+-comm x (suc y)
                                              | n+k∸m (suc y) x≤b
                                              | ℕ°.+-comm x y = idp

_*′_ : ℕ → ℕ → ℕ
0 *′ n = 0
1 *′ n = n
m *′ 0 = 0
m *′ 1 = m
m *′ n = m * n

*′-spec : ∀ m n → m *′ n ≡ m * n
*′-spec 0             n = idp
*′-spec 1             n = ℕ°.+-comm 0 n
*′-spec (suc (suc m)) 0 = ℕ°.*-comm 0 m
*′-spec (suc (suc m)) 1 = ap (suc ∘′ suc) (! snd ℕ°.*-identity m)
*′-spec (suc (suc m)) (suc (suc n)) = idp

≤→≢1+ : ∀ {x y} → x ≤ y → x ≢ suc y
≤→≢1+ z≤n     ()
≤→≢1+ (s≤s p) q = ≤→≢1+ p (suc-injective q)

<→≢ : ∀ {x y} → x < y → x ≢ y
<→≢ (s≤s p) = ≤→≢1+ p

∸-assoc-+ : ∀ x y z → x ∸ y ∸ z ≡ x ∸ (y + z)
∸-assoc-+ x       zero    z       = idp
∸-assoc-+ zero    (suc y) zero    = idp
∸-assoc-+ zero    (suc y) (suc z) = idp
∸-assoc-+ (suc x) (suc y) z       = ∸-assoc-+ x y z

_∸-tone_ : ∀ {x y t u} → x ≤ y → t ≤ u → t ∸ y ≤ u ∸ x
_∸-tone_ {y = y} z≤n t≤u = n∸m≤n y _ ∙≤ t≤u
s≤s x≤y ∸-tone z≤n = z≤n
s≤s x≤y ∸-tone s≤s t≤u = x≤y ∸-tone t≤u

∸-mono' : ∀ k {x y} → x ≤ y → x ∸ k ≤ y ∸ k
∸-mono' k = _∸-tone_ (ℕ≤.refl {k})

∸-anti : ∀ k {x y} → x ≤ y → k ∸ y ≤ k ∸ x
∸-anti k x≤y = _∸-tone_ x≤y (ℕ≤.refl {k})

infix 8 _^_
_^_ : ℕ → ℕ → ℕ
b ^ zero  = 1
b ^ suc n = b * b ^ n

_^2 : ℕ → ℕ
n ^2 = n * n

^2-spec : ∀ n → n ^2 ≡ n ^ 2
^2-spec n rewrite snd ℕ°.*-identity n = idp

2^_ : ℕ → ℕ
2^ n = ⟨2^ n * 1 ⟩

2^-spec : ∀ n → 2^ n ≡ 2 ^ n
2^-spec zero = idp
2^-spec (suc n) rewrite 2^-spec n | 2*-spec (2 ^ n) = idp

2^*-spec : ∀ m n → 2^⟨ m ⟩* n ≡ 2 ^ m * n
2^*-spec zero    n rewrite ℕ°.+-comm n 0 = idp
2^*-spec (suc m) n rewrite 2^*-spec m n
                         | ℕ°.*-assoc 2 (2 ^ m) n
                         | ℕ°.+-comm (2 ^ m * n) 0 = idp

1≤2^ : ∀ n → 2^ n ≥ 1
1+≤2^ : ∀ n → 2^ n ≥ 1 + n
1+≤2^ zero    = s≤s z≤n
1+≤2^ (suc n) = (1≤2^ n) +-mono (1+≤2^ n)

1≤2^ n  = s≤s z≤n ∙≤ 1+≤2^ n

≤-steps′ : ∀ {x} y → x ≤ x + y
≤-steps′ {x} y rewrite ℕ°.+-comm x y = ≤-steps y ℕ≤.refl

≤⇒∃ : ∀ {m n} → m ≤ n → ∃ λ k → m + k ≡ n
≤⇒∃ z≤n      = _ , idp
≤⇒∃ (s≤s pf) = _ , ap suc (snd (≤⇒∃ pf))

is0? : ℕ → 𝟚
is0? zero    = 1₂
is0? (suc n) = 0₂

module _ {{_ : UA}} where
    open Equivalences
    ∃-is0?-uniq : ∃ (✓ ∘ is0?) ≡ 𝟙
    ∃-is0?-uniq = ua (equiv _ (const (0 , _)) (const idp)
                            λ { (0 , _) → idp ; (suc _ , ()) })


{-
module GeneralisedArithmetic {a} {A : ★ a} (0# : A) (1+ : A → A) where

  1# : A
  1# = 1+ 0#

  open Data.Nat.GeneralisedArithmetic 0# 1+ public

  exp : (* : A → A → A) → (ℕ → A → A)
  exp _*_ n b = fold 1# (λ s → b * s) n
-}
  -- hyperop a n b = fold exp

module == where
  _≈_ : (m n : ℕ) → ★₀
  m ≈ n = ✓ (m == n)

  subst : ∀ {ℓ} → Substitutive _≈_ ℓ
  subst _ {zero}  {zero}  _  = id
  subst P {suc _} {suc _} p  = subst (P ∘ suc) p
  subst _ {zero}  {suc _} ()
  subst _ {suc _} {zero}  ()

  sound : ∀ m n → ✓ (m == n) → m ≡ n
  sound m n p = subst (_≡_ m) p idp

  refl : Reflexive _≈_
  refl {zero}  = _
  refl {suc n} = refl {n}

  sym : Symmetric _≈_
  sym {m} {n} eq rewrite sound m n eq = refl {n}

  trans : Transitive _≈_
  trans {m} {n} {o} m≈n n≈o rewrite sound m n m≈n | sound n o n≈o = refl {o}

  setoid : Setoid _ _
  setoid = record { Carrier = ℕ; _≈_ = _≈_
                  ; isEquivalence =
                      record { refl = λ {x} → refl {x}
                             ; sym = λ {x} {y} → sym {x} {y}
                             ; trans = λ {x} {y} {z} → trans {x} {y} {z} } }

  open Setoid setoid public hiding (refl; sym; trans; _≈_)

{-
data _`≤?`_↝_ : (m n : ℕ) → Dec (m ≤ n) → ★₀ where
  z≤?n     : ∀ {n} → zero `≤?` n ↝ yes z≤n
  s≤?z     : ∀ {m} → suc m `≤?` zero ↝ no λ()
  s≤?s-yes : ∀ {m n m≤n} → m `≤?` n ↝ yes m≤n → suc m `≤?` suc n ↝ yes (s≤s m≤n)
  s≤?s-no  : ∀ {m n m≰n} → m `≤?` n ↝ no m≰n → suc m `≤?` suc n ↝ no (m≰n ∘ ≤-pred)

`≤?`-complete : ∀ m n → m `≤?` n ↝ (m ≤? n)
`≤?`-complete zero n = z≤?n
`≤?`-complete (suc n) zero = {!s≤?z!}
`≤?`-complete (suc m) (suc n) with m ≤? n | `≤?`-complete m n
... | yes q | r = s≤?s-yes r
... | no q  | r = s≤?s-no {!!}
-}

_<=_ : (x y : ℕ) → 𝟚
zero   <= _      = 1₂
suc _  <= zero   = 0₂
suc m  <= suc n  = m <= n

module <= where
  ℛ : ℕ → ℕ → ★₀
  ℛ x y = ✓ (x <= y)

  sound : ∀ m n → ℛ m n → m ≤ n
  sound zero    _       _  = z≤n
  sound (suc m) (suc n) p  = s≤s (sound m n p)
  sound (suc m) zero    ()

  complete : ∀ {m n} → m ≤ n → ℛ m n
  complete z≤n       = _
  complete (s≤s m≤n) = complete m≤n

  isTotalOrder : IsTotalOrder _≡_ ℛ
  isTotalOrder = record { isPartialOrder = isPartialOrder; total = λ x y → ⊎-map complete complete (ℕ≤.total x y) }
   where
    reflexive : ∀ {i j} → i ≡ j → ℛ i j
    reflexive {i} idp = complete (ℕ≤.refl {i})
    trans : Transitive ℛ
    trans {x} {y} {z} p q = complete (ℕ≤.trans (sound x y p) (sound y z q))
    isPreorder : IsPreorder _≡_ ℛ
    isPreorder = record { isEquivalence = ≡.isEquivalence
                        ; reflexive = reflexive
                        ; trans = λ {x} {y} {z} → trans {x} {y} {z} }
    antisym : Antisymmetric _≡_ ℛ
    antisym {x} {y} p q = ℕ≤.antisym (sound x y p) (sound y x q)
    isPartialOrder : IsPartialOrder _≡_ ℛ
    isPartialOrder = record { isPreorder = isPreorder; antisym = antisym }

  open IsTotalOrder isTotalOrder public

<=-steps′ : ∀ {x} y → ✓ (x <= (x + y))
<=-steps′ {x} y = <=.complete (≤-steps′ {x} y)

sucx∸y≤suc⟨x∸y⟩ : ∀ x y → suc x ∸ y ≤ suc (x ∸ y)
sucx∸y≤suc⟨x∸y⟩ x zero = ℕ≤.refl
sucx∸y≤suc⟨x∸y⟩ zero (suc y) rewrite 0∸n≡0 y = z≤n
sucx∸y≤suc⟨x∸y⟩ (suc x) (suc y) = sucx∸y≤suc⟨x∸y⟩ x y

x≤2y′→x∸y≤y : ∀ x y → x ≤ 2*′ y → x ∸ y ≤ y
x≤2y′→x∸y≤y x zero p = p
x≤2y′→x∸y≤y zero (suc y) p = z≤n
x≤2y′→x∸y≤y (suc zero) (suc y) (s≤s p) rewrite 0∸n≡0 y = z≤n
x≤2y′→x∸y≤y (suc (suc x)) (suc y) (s≤s (s≤s p))
  = sucx∸y≤suc⟨x∸y⟩ x y ∙≤ s≤s (x≤2y′→x∸y≤y x y p)

x<2y′→x∸y<y : ∀ x y → x < 2*′ y → x ∸ y < y
x<2y′→x∸y<y x zero p = p
x<2y′→x∸y<y zero (suc y) p = s≤s z≤n
x<2y′→x∸y<y (suc zero) (suc y) (s≤s (s≤s p)) rewrite 0∸n≡0 y = s≤s z≤n
x<2y′→x∸y<y (suc (suc x)) (suc y) (s≤s (s≤s p))
  = s≤s (sucx∸y≤suc⟨x∸y⟩ x y) ∙≤ s≤s (x<2y′→x∸y<y x y p)

x<2y→x∸y<y : ∀ x y → x < 2* y → x ∸ y < y
x<2y→x∸y<y x y p rewrite ! 2*′-spec y = x<2y′→x∸y<y x y p

≰→< : ∀ x y → x ≰ y → y < x
≰→< x y p with ℕcmp.compare (suc y) x
≰→< x y p | tri< a ¬b ¬c = s≤s (≤-step ℕ≤.refl) ∙≤ a
≰→< x y p | tri≈ ¬a b ¬c = ℕ≤.reflexive b
≰→< x y p | tri> ¬a ¬b c = 𝟘-elim (p (≤-pred c))

¬≤ : ∀ {m n} → ¬(m < n) → n ≤ m
¬≤ {m} {n} p with ℕcmp.compare m n
... | tri< m<n _ _   = 𝟘-elim (p m<n)
... | tri≈ _ eq _    = ℕ≤.reflexive (! eq)
... | tri> _ _ 1+n≤m = ≤-pred (≤-steps 1 1+n≤m)

not<=→< : ∀ x y → ✓ (not (x <= y)) → ✓ (suc y <= x)
not<=→< x y p = <=.complete (≰→< x y (✓-not-¬ p ∘ <=.complete))

even? odd? : ℕ → 𝟚
even? zero    = 1₂
even? (suc n) = odd? n 
odd? n = not (even? n)
-- -}
-- -}
-- -}
-- -}
