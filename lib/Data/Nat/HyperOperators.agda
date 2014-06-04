open import Type
open import Function.NP
open import Data.Product
open import Data.Nat.NP hiding (⇑⟨_⟩)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality.NP

module Data.Nat.HyperOperators where

-- https://en.wikipedia.org/wiki/Hyper_operator
_↑⟨_⟩_ : ℕ → ℕ → ℕ → ℕ
a ↑⟨ suc n             ⟩ (suc b) = a ↑⟨ n ⟩ (a ↑⟨ suc n ⟩ b)
a ↑⟨ 0                 ⟩ b       = suc b
a ↑⟨ 1                 ⟩ 0       = a
a ↑⟨ 2                 ⟩ 0       = 0
a ↑⟨ suc (suc (suc n)) ⟩ 0       = 1

module ↑-Props where
  ↑-fold : ∀ a n b → a ↑⟨ suc n ⟩ b ≡ fold (a ↑⟨ suc n ⟩ 0) (_↑⟨_⟩_ a n) b
  ↑-fold a n zero = idp
  ↑-fold a n (suc b) = ap (_↑⟨_⟩_ a n) (↑-fold a n b)

  ↑₀-+ : ∀ a b → a ↑⟨ 0 ⟩ b ≡ 1 + b
  ↑₀-+ a b = idp

  ↑₁-+ : ∀ a b → a ↑⟨ 1 ⟩ b ≡ b + a
  ↑₁-+ a zero    = idp
  ↑₁-+ a (suc b) = ap suc (↑₁-+ a b)

  ↑₂-* : ∀ a b → a ↑⟨ 2 ⟩ b ≡ b * a
  ↑₂-* a zero    = idp
  ↑₂-* a (suc b) rewrite ↑₂-* a b
                       | ↑₁-+ a (b * a)
                       | ℕ°.+-comm (b * a) a
                       = idp

  -- fold 1 (_*_ a) b ≡ a ^ b
  ↑₃-^ : ∀ a b → a ↑⟨ 3 ⟩ b ≡ a ^ b
  ↑₃-^ a zero = idp
  ↑₃-^ a (suc b) rewrite ↑₃-^ a b
                       | ↑₂-* a (a ^ b)
                       | ℕ°.*-comm (a ^ b) a
                       = idp

  _↑⟨_⟩0 : ℕ → ℕ → ℕ
  a ↑⟨ 0                 ⟩0 = 1
  a ↑⟨ 1                 ⟩0 = a
  a ↑⟨ 2                 ⟩0 = 0
  a ↑⟨ suc (suc (suc n)) ⟩0 = 1

  _`↑⟨_⟩_ : ℕ → ℕ → ℕ → ℕ
  _`↑⟨_⟩_ a 0       = suc
  _`↑⟨_⟩_ a (suc n) = fold (a ↑⟨ suc n ⟩0) (_`↑⟨_⟩_ a n)

  ↑-ind-rule : ∀ a n b → a ↑⟨ suc n ⟩ (suc b) ≡ a ↑⟨ n ⟩ (a ↑⟨ suc n ⟩ b)
  ↑-ind-rule a n b = idp

  _↑′⟨_⟩_ : ℕ → ℕ → ℕ → ℕ
  a ↑′⟨ 0 ⟩ b = suc b
  a ↑′⟨ 1 ⟩ b = a + b
  a ↑′⟨ 2 ⟩ b = a * b
  a ↑′⟨ 3 ⟩ b = a ^ b
  a ↑′⟨ suc (suc (suc (suc n))) ⟩ b = a ↑⟨ 4 + n ⟩ b

  ↑-↑′ : ∀ a n b → a ↑⟨ n ⟩ b ≡ a ↑′⟨ n ⟩ b
  ↑-↑′ a 0 b = idp
  ↑-↑′ a 1 b = ↑₁-+ a b ∙ ℕ°.+-comm b a
  ↑-↑′ a 2 b = ↑₂-* a b ∙ ℕ°.*-comm b a
  ↑-↑′ a 3 b = ↑₃-^ a b
  ↑-↑′ a (suc (suc (suc (suc _)))) b = idp

  _↑2+⟨_⟩_ : ℕ → ℕ → ℕ → ℕ
  _↑2+⟨_⟩_ a = fold (_*_ a) (fold 1)

module InflModule where
  -- Inflationary functions
  Infl< : (f : ℕ → ℕ) → ★₀
  Infl< f = ∀ {x} → x < f x

  Infl : (f : ℕ → ℕ) → ★₀
  Infl f = Infl< (suc ∘ f)

  InflT< : (f : Endo (Endo ℕ)) → ★₀
  InflT< f = ∀ {g} → Infl< g → Infl< (f g)

{-
∀ {x} → x ≤ f x


  1 + x ≤ 1 + f x
  x < 1 + f x
  x < (suc ∘ f) x
  Infl< (suc ∘ f)

  Infl< f = ∀ {x} → 1 + x ≤ f x
  Infl< f = ∀ {x} → 1 + x ≤ f x

Infl< f → Infl f
Infl< f → Infl< (suc ∘ f)
-}

  id-infl : Infl id
  id-infl = ℕ≤.refl

  ∘-infl< : ∀ {f g} → Infl< f → Infl< g → Infl< (f ∘ g)
  ∘-infl< inflf< inflg< = inflg< ∙< inflf<

  suc-infl< : Infl< suc
  suc-infl< = ℕ≤.refl

  suc-infl : Infl suc
  suc-infl = s≤s (≤-step ℕ≤.refl)

  nest-infl : ∀ f (finfl : Infl f) n → Infl (nest n f)
  nest-infl f _ zero = ℕ≤.refl
  nest-infl f finfl (suc n) = nest-infl f finfl n ∙≤ finfl

  nest-infl< : ∀ f (finfl< : Infl< f) n → Infl< (nest (suc n) f)
  nest-infl< f finfl< zero    = finfl<
  nest-infl< f finfl< (suc n) = nest-infl< f finfl< n ∙< finfl< 

-- See Function.NP.nest-Properties for more properties
module fold-Props where

  fold-suc : ∀ m n → fold m suc n ≡ n + m
  fold-suc m zero = idp
  fold-suc m (suc n) rewrite fold-suc m n = idp

  fold-+ : ∀ m n → fold 0 (_+_ m) n ≡ n * m
  fold-+ m zero = idp
  fold-+ m (suc n) rewrite fold-+ m n = idp

  fold-* : ∀ m n → fold 1 (_*_ m) n ≡ m ^ n
  fold-* m zero = idp
  fold-* m (suc n) rewrite fold-* m n = idp

{- TODO
  fold-^ : ∀ m n → fold 1 (flip _^_ m) n ≡ m ↑⟨ 4 ⟩ n
  fold-^ m zero = idp
  fold-^ m (suc n) rewrite fold-^ m n = ?
-}

  cong-fold : ∀ {A : ★₀} {f g : Endo A} (f≗g : f ≗ g) {z} → fold z f ≗ fold z g
  cong-fold eq zero = idp
  cong-fold eq {z} (suc x) rewrite cong-fold eq {z} x = eq _

  private
   open ↑-Props
   module Alt↑2 where
    alt : ℕ → ℕ → ℕ → ℕ
    alt a 0       = λ b → a ↑⟨ 2 ⟩ b
    alt a (suc n) = fold 1 (alt a n)

    alt-ok : ∀ a n → _↑2+⟨_⟩_ a n ≗ alt a n
    alt-ok a zero = !_ ∘ ↑-↑′ a 2
    alt-ok a (suc n) = cong-fold (alt-ok a n)

{- TODO
    alt' : ∀ a n → _↑2+⟨_⟩_ a n ≗ _↑⟨_⟩_ a (2 + n)
    alt' a zero  b = !_ (↑-↑′ a 2 _)
    alt' a (suc n) zero = idp
    alt' a (suc n) (suc x) rewrite alt' a n (_↑2+⟨_⟩_ a (suc n) x)
       = ap (_↑⟨_⟩_ a (2 + n)) { fold 1 (fold (_*_ a) (fold 1) n) x} {a ↑⟨ suc (suc (suc n)) ⟩ x} (alt' a (suc n) x)
-}

  open InflModule
{-
  fold1-infl : ∀ f → Infl f → Infl (fold 1 f)
  fold1-infl f finfl {zero} = {!z≤n!}
  fold1-infl f finfl {suc x} =
     x          <⟨ {!s≤s (fold1-infl f finfl {x})!} ⟩
     fold 1 f x <⟨ {!!} ⟩
     {- f (fold 1 f x) ≤⟨ finfl ⟩
     f (fold 1 f x) ≡⟨ idp ⟩ -}
     fold 1 f (1 + x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}

{-
  fold1+1-infl< : ∀ (f : ℕ → ℕ) → Infl< (f ∘ suc) → Infl< (fold 1 f ∘ suc)
  fold1+1-infl< f finfl< {zero} = finfl<
  fold1+1-infl< f finfl< {suc x} =
     2 + x ≤⟨ s≤s (fold1+1-infl< f finfl< {x}) ⟩
     1 + f (fold 1 f x) ≤⟨ finfl< {f (fold 1 f x)} ⟩
     f (suc (f (fold 1 f x))) ≤⟨ {!!} ⟩
     fold 1 f (2 + x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
{-
  fold1+1-infl< : ∀ (f : ℕ → ℕ) → Infl< (f ∘ suc) → Infl< (fold 1 (f ∘ suc))
  fold1+1-infl< f finfl< {zero} = s≤s z≤n
  fold1+1-infl< f finfl< {suc x} =
     2 + x ≤⟨ s≤s (fold1+1-infl< f finfl< {x}) ⟩
     1 + fold 1 (f ∘ suc) x ≤⟨ finfl< ⟩
     fold 1 (f ∘ suc) (suc x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
{-
  fold1+-infl< : ∀ k f → Infl< (f ∘′ _+_ k) → Infl< (fold 1 (f ∘′ _+_ k))
  fold1+-infl< k f finfl< {zero} = s≤s z≤n
  fold1+-infl< k f finfl< {suc x} =
     2 + x ≤⟨ s≤s (fold1+-infl< k f finfl< {x}) ⟩
     1 + fold 1 (f ∘ _+_ k) x ≤⟨ finfl< ⟩
     fold 1 (f ∘ _+_ k) (suc x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
  
{-
  fold1+-infl< : ∀ f → Infl+2< f → Infl+2< (fold 1 f)
  fold1+-infl< f finfl< {zero} _ = ℕ≤.refl
  fold1+-infl< f finfl< {suc zero} _ = {!!}
  fold1+-infl< f finfl< {suc (suc zero)} _ = {!!}
  fold1+-infl< f finfl< {suc (suc (suc x))} x>1 =
     4 + x ≤⟨ s≤s (fold1+-infl< f finfl< {suc (suc x)} (m≤m+n 2 x)) ⟩
     1 + fold 1 f (2 + x) ≤⟨ finfl< {!!} ⟩
     fold 1 f (3 + x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
{-
  fold1-infl< f finfl< {zero} = s≤s z≤n
  fold1-infl< f finfl< {suc x} =
     2 + x ≤⟨ s≤s (fold1-infl< f finfl< {x}) ⟩
     1 + fold 1 f x ≤⟨ finfl< ⟩
     fold 1 f (suc x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
module ^-Props where
  open ≡-Reasoning

  ^1 : ∀ n → n ^ 1 ≡ n
  ^1 zero = idp
  ^1 (suc n) = ap suc (proj₂ ℕ°.*-identity n)

  ^-+ : ∀ b m n → b ^ (m + n) ≡ b ^ m * b ^ n
  ^-+ b zero n = ! proj₂ ℕ°.+-identity (b ^ n)
  ^-+ b (suc m) n rewrite ^-+ b m n = ! ℕ°.*-assoc b (b ^ m) (b ^ n)

  ^-* : ∀ b m n → b ^ (m * n) ≡ (b ^ n) ^ m
  ^-* b zero    n = idp
  ^-* b (suc m) n = b ^ (n + m * n)
                  ≡⟨ ^-+ b n (m * n) ⟩
                    b ^ n * b ^ (m * n)
                  ≡⟨ ap (_*_ (b ^ n)) (^-* b m n) ⟩
                    b ^ n * (b ^ n) ^ m ∎


ack : ℕ → ℕ → ℕ
ack zero n          = suc n
ack (suc m) zero    = ack m (suc zero)
ack (suc m) (suc n) = ack m (ack (suc m) n)

module ack-Props where
  lem∸ : ∀ {m n} → m ≤ n → m + (n ∸ m) ≡ n
  lem∸ z≤n = idp
  lem∸ (s≤s {m} {n} m≤n) = ap suc (lem∸ m≤n)

  -- n >= m → m + (n ∸ m) ≡ n
  -- n >= m → ∃ k → n ≡ m + k
  -- ∃ k → n ≡ m + k → m + (n ∸ m) ≡ n
  -- ∀ k → n ≡ m + k → m + (n ∸ m) ≡ n
  -- ∀ k → m + ((m + k) ∸ m) ≡ m + k
  -- ∀ k → m + k ≡ m + k

  -- 3 ≤ x → P x → ∃ λ k → P (3 + k)

  open InflModule

  fold1+-inflT< : ∀ {z} → InflT< (fold (suc z))
  fold1+-inflT<     _      {zero} = s≤s z≤n
  fold1+-inflT< {z} {f} finfl< {suc x} =
     2 + x                ≤⟨ s≤s (fold1+-inflT< {z} {f} finfl< {x}) ⟩
     1 + fold (suc z) f x ≤⟨ finfl< ⟩
     f (fold (suc z) f x) ≡⟨ idp ⟩
     fold (suc z) f (1 + x)
   ∎
     where open ≤-Reasoning

  Mon : (f : ℕ → ℕ) → ★₀
  Mon f = ∀ {x y} → x ≤ y → f x ≤ f y
  open InflModule


  ℕ-ind : ∀ (P : ℕ → ★₀) → P zero → (∀ {n} → P n → P (suc n)) → ∀ {n} → P n
  ℕ-ind P P0 PS {zero} = P0
  ℕ-ind P P0 PS {suc n} = PS (ℕ-ind P P0 PS)

  open fold-Props
  fold-infl< : ∀ {f g} → Infl< f → InflT< g → ∀ {n} → Infl< (fold f g n)
  fold-infl< {f} {g} inflf< inflTg< {n} = ℕ-ind (Infl< ∘ fold f g) inflf< inflTg< {n}

  fold-mon : ∀ {f} (fmon : Mon f) (finfl< : Infl< f) {z} → Mon (fold z f)
  fold-mon fmon finfl< {_} {y = 0} z≤n = ℕ≤.refl
  fold-mon {f} fmon finfl< {z} {y = suc n} z≤n = z ≤⟨ ≤-step ℕ≤.refl ⟩
                                              suc z ≤⟨ nest-infl< f finfl< n {z} ⟩
                                              fold z f (suc n) ≡⟨ idp ⟩
                                              fold z f (suc n) ∎
    where open ≤-Reasoning
  fold-mon fmon finfl< (s≤s m≤n) = fmon (fold-mon fmon finfl< m≤n)

  MonT : Endo (Endo ℕ) → ★₀
  MonT g = ∀ {f} → Mon f → Infl< f → Mon (g f)

  fold-mon' : ∀ {f g} → Mon f → Infl< f → MonT g → InflT< g → ∀ {n} → Mon (fold f g n)
  fold-mon' {f} {g} mon-f infl-f mont-g inflTg< {n} = go n where
    go : ∀ n → Mon (fold f g n)
    go zero    = mon-f
    go (suc n) = mont-g (go n) (fold-infl< infl-f inflTg< {n})


  --  +-fold : ∀ a b → a + b ≡ fold a suc b
  --  *-fold : ∀ a b → a * b ≡ fold 0 (_+_ a) b

  1≤1+a^b : ∀ a b → 1 ≤ (1 + a) ^ b
  1≤1+a^b a zero = s≤s z≤n
  1≤1+a^b a (suc b) = 1≤1+a^b a b +-mono z≤n

  1+a^-mon : ∀ {a} → Mon (_^_ (1 + a))
  1+a^-mon {a} (z≤n {b}) = 1≤1+a^b a b
  1+a^-mon {a} (s≤s {m} {n} m≤n)
     = (1 + a) ^ (1 + m)             ≡⟨ idp ⟩
       (1 + a) ^ m + a * (1 + a) ^ m ≤⟨ (1+a^-mon m≤n) +-mono ((a ∎) *-mono (1+a^-mon m≤n)) ⟩
       (1 + a) ^ n + a * (1 + a) ^ n ≡⟨ idp ⟩
       (1 + a) ^ (1 + n) ∎
    where open ≤-Reasoning

  lem2^3 : ∀ n → 2 ^ 3 ≤ 2 ^ (3 + n)
  lem2^3 n = 1+a^-mon {1} {3} {3 + n} (s≤s (s≤s (s≤s z≤n)))

  lem2221 : ∀ m → 2 ≡ 2 ↑⟨ 2 + m ⟩ 1
  lem2221 zero = idp
  lem2221 (suc m) = lem2221 m

  lem4212 : ∀ m → 4 ≡ 2 ↑⟨ 1 + m ⟩ 2
  lem4212 zero = idp
  lem4212 (suc m) = 4                            ≡⟨ lem4212 m ⟩
                    2 ↑⟨ 1 + m ⟩ 2               ≡⟨ ap (_↑⟨_⟩_ 2 (1 + m)) (lem2221 m) ⟩
                    2 ↑⟨ 1 + m ⟩ (2 ↑⟨ 2 + m ⟩ 1) ≡⟨ idp ⟩
                    2 ↑⟨ 2 + m ⟩ 2 ∎
    where open ≡-Reasoning

  2*′′ = _*_ 2

  -- fold 2*′′ n 1 ≡ 2 ^ n

  -- nest-* : ∀ m n → nest (m * n) f ≗ nest m (nest n f)

  nest-2*′′ : ∀ m n → nest (m * n) (fold 1) 2*′′ ≡ nest m (nest n (fold 1)) 2*′′
  nest-2*′′ m n = nest-Properties.nest-* (fold 1) m n 2*′′

{-
  lem3≤ : ∀ n → 3 ≤ fold 2*′′ (fold 1) n 2
  lem3≤ 0 = s≤s (s≤s (s≤s z≤n))
    where open ≤-Reasoning
  lem3≤ (suc n) = 
    3 ≤⟨ {!!} ⟩
    fold 2*′′ f1 (1 + n) 2 ∎
    where open ≤-Reasoning
          f1 = fold 1

  lem3≤' : ∀ n → 3 ≤ fold 2*′′ (fold 1) n 3
  lem3≤' 0 = s≤s (s≤s (s≤s z≤n))
    where open ≤-Reasoning
  lem3≤' (suc n) = 
    3 ≤⟨ lem3≤ n ⟩
    fold 2*′′ (fold 1) n 2 ≡⟨ idp ⟩
    fold 2*′′ (fold 1) n (fold 2*′′ (fold 1) 3 1) ≡⟨ {!!} ⟩
{- ≡⟨ nest-Properties.nest-* {!2*′′!} {!!} {!!} {!!} ⟩
    fold 2*′′ (fold 1) (3 * n) 1 ≡⟨ {!!} ⟩
-}
    fold 1 (fold 2*′′ (fold 1) n) 3 ≡⟨ idp ⟩
    fold 2*′′ (fold 1) (1 + n) 3 ∎
    where open ≤-Reasoning
-}
---

{-
fold 2*′′ (fold 1) (3 * n) 1 ≤

fold 2*′′ (fold 1) n (fold 2*′′ (fold 1) n (fold 2*′′ (fold 1) n 1)) ≤

fold 1 (fold 2*′′ (fold 1) n) 3 ≤
fold 2*′′ (fold 1) (1 + n) 3
-}

{-
  open ↑-Props

  -*⟨1+n⟩-infl : ∀ n → Infl (_*_ (1 + n))
  -*⟨1+n⟩-infl n = {!!}

  lem121 : ∀ a b → b < (1 + a) ↑⟨ 2 ⟩ (1 + b)
  lem121 a b rewrite ↑₂-* (1 + a) (1 + b)
     = 1 + b
              ≤⟨ m≤m+n _ _ ⟩
       (1 + a) * (1 + b)
              ≡⟨ ℕ°.*-comm (1 + a) (1 + b) ⟩
       (1 + b) * (1 + a)
     ∎
     where open ≤-Reasoning

  -- ∀ a b → b < (2 + a) * b
  lem222 : ∀ a b → b < (2 + a) ↑⟨ 2 ⟩ (2 + b)
  lem222 a b rewrite ↑₂-* (2 + a) (2 + b)
     = 1 + b
              ≤⟨ suc-infl ⟩
       2 + b
              ≤⟨ m≤m+n _ _ ⟩
       (2 + a) * (2 + b)
              ≡⟨ ℕ°.*-comm (2 + a) (2 + b) ⟩
       (2 + b) * (2 + a)
     ∎
     where open ≤-Reasoning
-}
{-
  open fold-Props

  module Foo a where
    f = λ n b → (2 + a) ↑2+⟨ n ⟩ b
    f-lem : ∀ n → f (suc n) ≗ fold 1 (f n)
    f-lem n x = idp

    f2 = λ n b → (2 + a) ↑2+⟨ n ⟩ (2 + b)
    f2-lem : ∀ n → f2 (suc n) ≗ fold 1 (f2 n)
    f2-lem n x = {!!}

  -- b < (1 + a) * (1 + b)

 -- nest-infl< : ∀ f (finfl< : Infl< f) n → Infl< (nest (suc n) f)
  infl3< : ∀ a n → Infl< (λ b → (1 + a) ↑2+⟨ n ⟩ (1 + b))
  infl3< a zero {b} = lem121 a b
  infl3< a (suc n) {b}
    = 1 + b
 --  fold1-infl< : ∀ f → Infl< f → ∀ x → x < fold 1 f x
            ≤⟨ {!fold1f2-infl< {_}!} ⟩
      fold 1 f1 b
            ≤⟨ {!!} ⟩
{-
            ≤⟨ fold1-infl< (f 0) (λ {x} → {!infl3< a n {x}!}) {{!!}} ⟩
      {!!}
            ≤⟨ {!!} ⟩
-}
{-
      1 + b
      (2 + a) ↑2+⟨ n ⟩ (2 + b)
            ≤⟨ {!nest-infl< (λ b → (2 + a) ↑2+⟨ n ⟩ b) ? b {(2 + a) ↑2+⟨ n ⟩ (2 + b)}!} ⟩
      fold (f 0 1) (f 0) (1 + b)
            ≤⟨ {!ℕ≤.reflexive (ap (λ g → g 1) (nest-Properties.nest-+ (f 0) 1 (1 + b)))!} ⟩
-}
      fold 1 (f 0) (1 + b)
            ≡⟨ idp ⟩
      f 1 (1 + b)
            ≡⟨ idp ⟩
      (1 + a) ↑2+⟨ suc n ⟩ (1 + b)
    ∎

     where
       f = λ k b → (1 + a) ↑2+⟨ k + n ⟩ b
       f1 = f 0 ∘ suc

       -- fold1f2-infl< : Infl< (fold 1 f2)
       -- fold1f2-infl< = fold1-infl< f2 {!(λ b → infl3< a n b ?)!}

       fold1f1-infl<' : Infl< (fold 1 f1)
       fold1f1-infl<' = {!fold1+1-infl< (f 0) {!infl3< a n!}!}
       lem : ∀ x → f 0 (1 + x) < f 0 (f 0 x)
       lem x = {!!}
       postulate
         finfl : Infl< (f 0)
       open ≤-Reasoning
-}

_⇑⟨_,_⟩_ : (a n k b : ℕ) → ℕ
a ⇑⟨ n , k ⟩ b = fold k f n
  module M⇑ where 
    f : ℕ → ℕ
    f x = a ↑⟨ 2 + x ⟩ b

module ⇑-Props where
  _⇑′⟨_,_⟩_ : (a n k b : ℕ) → ℕ
  a ⇑′⟨ n₀ , k ⟩ b = g n₀
    module M⇑′ where
      h : ℕ → ℕ
      h x = a ↑⟨ 2 + x ⟩ b

      g : ℕ → ℕ
      g 0       = k
      g (suc n) = h (g n)

      g-nest : ∀ n → g n ≡ h $⟨ n ⟩ k
      g-nest zero = idp
      g-nest (suc n) rewrite g-nest n = idp

  ⇑₀ : ∀ a k b → a ⇑⟨ 0 , k ⟩ b ≡ k
  ⇑₀ _ _ _ = idp

  ⇑₁ : ∀ a k b → a ⇑⟨ 1 , k ⟩ b ≡ a ↑⟨ 2 + k ⟩ b
  ⇑₁ _ _ _ = idp

  ⇑-⇑′ : ∀ a n k b → a ⇑⟨ n , k ⟩ b ≡ a ⇑′⟨ n , k ⟩ b
  ⇑-⇑′ a n k b rewrite M⇑′.g-nest a n k b n = idp

-- https://en.wikipedia.org/wiki/Graham%27s_number
Graham's-number : ℕ
Graham's-number = 3 ⇑⟨ 64 , 4 ⟩ 3
  -- = (f∘⁶⁴…∘f)4
  -- where f x = 3 ↑⟨ 2 + x ⟩ 3
