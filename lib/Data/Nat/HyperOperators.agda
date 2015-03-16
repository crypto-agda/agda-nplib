open import Type
open import Function.NP
open import Data.Product.NP
open import Data.Nat.NP hiding (⇑⟨_⟩)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality.NP

module Data.Nat.HyperOperators where

-- https://en.wikipedia.org/wiki/Hyper_operator
_↑⟨_⟩_ : ℕ → ℕ → ℕ → ℕ
a ↑⟨ 1+ n ⟩ (1+ b) = a ↑⟨ n ⟩ (a ↑⟨ 1+ n ⟩ b)
a ↑⟨ 0    ⟩ b      = 1+ b
a ↑⟨ 1    ⟩ 0      = a
a ↑⟨ 2    ⟩ 0      = 0
a ↑⟨ 3+ n ⟩ 0      = 1

module ↑-Props where
  ↑-fold : ∀ a n b → a ↑⟨ 1+ n ⟩ b ≡ fold (a ↑⟨ 1+ n ⟩ 0) (_↑⟨_⟩_ a n) b
  ↑-fold a n 0      = idp
  ↑-fold a n (1+ b) = ap (_↑⟨_⟩_ a n) (↑-fold a n b)

  ↑₀-+ : ∀ a b → a ↑⟨ 0 ⟩ b ≡ 1 + b
  ↑₀-+ a b = idp

  ↑₁-+ : ∀ a b → a ↑⟨ 1 ⟩ b ≡ b + a
  ↑₁-+ a 0      = idp
  ↑₁-+ a (1+ b) = ap suc (↑₁-+ a b)

  ↑₂-* : ∀ a b → a ↑⟨ 2 ⟩ b ≡ b * a
  ↑₂-* a 0 = idp
  ↑₂-* a (1+ b) rewrite ↑₂-* a b
                      | ↑₁-+ a (b * a)
                      | ℕ°.+-comm (b * a) a
                      = idp

  -- fold 1 (_*_ a) b ≡ a ^ b
  ↑₃-^ : ∀ a b → a ↑⟨ 3 ⟩ b ≡ a ^ b
  ↑₃-^ a 0 = idp
  ↑₃-^ a (1+ b) rewrite ↑₃-^ a b
                      | ↑₂-* a (a ^ b)
                      | ℕ°.*-comm (a ^ b) a
                      = idp

  _↑⟨_⟩0 : ℕ → ℕ → ℕ
  a ↑⟨ 0    ⟩0 = 1
  a ↑⟨ 1    ⟩0 = a
  a ↑⟨ 2    ⟩0 = 0
  a ↑⟨ 3+ n ⟩0 = 1

  _`↑⟨_⟩_ : ℕ → ℕ → ℕ → ℕ
  _`↑⟨_⟩_ a 0      = suc
  _`↑⟨_⟩_ a (1+ n) = fold (a ↑⟨ 1+ n ⟩0) (_`↑⟨_⟩_ a n)

  ↑-ind-rule : ∀ a n b → a ↑⟨ 1+ n ⟩ (1+ b) ≡ a ↑⟨ n ⟩ (a ↑⟨ 1+ n ⟩ b)
  ↑-ind-rule a n b = idp

  _↑′⟨_⟩_ : ℕ → ℕ → ℕ → ℕ
  a ↑′⟨ 0    ⟩ b = 1+  b
  a ↑′⟨ 1    ⟩ b = a + b
  a ↑′⟨ 2    ⟩ b = a * b
  a ↑′⟨ 3    ⟩ b = a ^ b
  a ↑′⟨ 4+ n ⟩ b = a ↑⟨ 4 + n ⟩ b

  ↑-↑′ : ∀ a n b → a ↑⟨ n ⟩ b ≡ a ↑′⟨ n ⟩ b
  ↑-↑′ a 0      b = idp
  ↑-↑′ a 1      b = ↑₁-+ a b ∙ ℕ°.+-comm b a
  ↑-↑′ a 2      b = ↑₂-* a b ∙ ℕ°.*-comm b a
  ↑-↑′ a 3      b = ↑₃-^ a b
  ↑-↑′ a (4+ _) b = idp

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
  nest-infl f _     0 = ℕ≤.refl
  nest-infl f finfl (1+ n) = nest-infl f finfl n ∙≤ finfl

  module _ f (finfl< : Infl< f) where
    nest-infl< : ∀  n → Infl< (nest (1+ n) f)
    nest-infl< 0      = finfl<
    nest-infl< (1+ n) = nest-infl< n ∙< finfl<

-- See Function.NP.nest-Properties for more properties
module fold-Props where

  module _ m where
    fold-suc : ∀ n → fold m suc n ≡ n + m
    fold-suc 0 = idp
    fold-suc (1+ n) rewrite fold-suc n = idp

    fold-+ : ∀ n → fold 0 (_+_ m) n ≡ n * m
    fold-+ 0 = idp
    fold-+ (1+ n) rewrite fold-+ n = idp

    fold-* : ∀ n → fold 1 (_*_ m) n ≡ m ^ n
    fold-* 0 = idp
    fold-* (1+ n) rewrite fold-* n = idp

    {- TODO
    fold-^ : ∀ n → fold 1 (flip _^_ m) n ≡ m ↑⟨ 4 ⟩ n
    fold-^ 0 = idp
    fold-^ (1+ n) rewrite fold-^ n = ?
    -}

  module _ {A : ★₀} {f g : Endo A} (f≗g : f ≗ g) {z} where
    cong-fold : fold z f ≗ fold z g
    cong-fold 0 = idp
    cong-fold (1+ x) rewrite cong-fold x = f≗g _

  private
   open ↑-Props
   module Alt↑2 a where
    alt : ℕ → ℕ → ℕ
    alt 0       = λ b → a ↑⟨ 2 ⟩ b
    alt (1+ n) = fold 1 (alt n)

    alt-ok : ∀ n → _↑2+⟨_⟩_ a n ≗ alt n
    alt-ok 0 = !_ ∘ ↑-↑′ a 2
    alt-ok (1+ n) = cong-fold (alt-ok n)

{- TODO
    alt' : ∀ n → _↑2+⟨_⟩_ a n ≗ _↑⟨_⟩_ a (2 + n)
    alt' 0  b = !_ (↑-↑′ a 2 _)
    alt' (1+ n) 0 = idp
    alt' (1+ n) (1+ x) rewrite alt' n (_↑2+⟨_⟩_ a (1+ n) x)
       = ap (_↑⟨_⟩_ a (2 + n)) { fold 1 (fold (_*_ a) (fold 1) n) x} {a ↑⟨ 3+ n ⟩ x} (alt' (1+ n) x)
-}

  open InflModule
{-
  fold1-infl : ∀ f → Infl f → Infl (fold 1 f)
  fold1-infl f finfl {0} = {!z≤n!}
  fold1-infl f finfl {1+ x} =
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
  fold1+1-infl< f finfl< {0} = finfl<
  fold1+1-infl< f finfl< {1+ x} =
     2 + x ≤⟨ s≤s (fold1+1-infl< f finfl< {x}) ⟩
     1 + f (fold 1 f x) ≤⟨ finfl< {f (fold 1 f x)} ⟩
     f (1+ f (fold 1 f x)) ≤⟨ {!!} ⟩
     fold 1 f (2 + x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
{-
  fold1+1-infl< : ∀ (f : ℕ → ℕ) → Infl< (f ∘ suc) → Infl< (fold 1 (f ∘ suc))
  fold1+1-infl< f finfl< {0} = s≤s z≤n
  fold1+1-infl< f finfl< {1+ x} =
     2 + x ≤⟨ s≤s (fold1+1-infl< f finfl< {x}) ⟩
     1 + fold 1 (f ∘ suc) x ≤⟨ finfl< ⟩
     fold 1 (f ∘ suc) (1+ x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
{-
  fold1+-infl< : ∀ k f → Infl< (f ∘′ _+_ k) → Infl< (fold 1 (f ∘′ _+_ k))
  fold1+-infl< k f finfl< {0} = s≤s z≤n
  fold1+-infl< k f finfl< {1+ x} =
     2 + x ≤⟨ s≤s (fold1+-infl< k f finfl< {x}) ⟩
     1 + fold 1 (f ∘ _+_ k) x ≤⟨ finfl< ⟩
     fold 1 (f ∘ _+_ k) (1+ x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
  
{-
  fold1+-infl< : ∀ f → Infl+2< f → Infl+2< (fold 1 f)
  fold1+-infl< f finfl< {0} _ = ℕ≤.refl
  fold1+-infl< f finfl< {1} _ = {!!}
  fold1+-infl< f finfl< {2} _ = {!!}
  fold1+-infl< f finfl< {3+ x} x>1 =
     4 + x ≤⟨ s≤s (fold1+-infl< f finfl< {2 + x} (m≤m+n 2 x)) ⟩
     1 + fold 1 f (2 + x) ≤⟨ finfl< {!!} ⟩
     fold 1 f (3 + x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
{-
  fold1-infl< f finfl< {0} = s≤s z≤n
  fold1-infl< f finfl< {1+ x} =
     2 + x ≤⟨ s≤s (fold1-infl< f finfl< {x}) ⟩
     1 + fold 1 f x ≤⟨ finfl< ⟩
     fold 1 f (1+ x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}

ack : ℕ → ℕ → ℕ
ack 0      n      = 1+ n
ack (1+ m) 0      = ack m 1
ack (1+ m) (1+ n) = ack m (ack (1+ m) n)

module ack-Props where
  lem∸ : ∀ {m n} → m ≤ n → m + (n ∸ m) ≡ n
  lem∸ z≤n = idp
  lem∸ (s≤s m≤n) = ap suc (lem∸ m≤n)

  -- n >= m → m + (n ∸ m) ≡ n
  -- n >= m → ∃ k → n ≡ m + k
  -- ∃ k → n ≡ m + k → m + (n ∸ m) ≡ n
  -- ∀ k → n ≡ m + k → m + (n ∸ m) ≡ n
  -- ∀ k → m + ((m + k) ∸ m) ≡ m + k
  -- ∀ k → m + k ≡ m + k

  -- 3 ≤ x → P x → ∃ λ k → P (3 + k)

  open InflModule

  module _ {z} where
    fold1+-inflT< : InflT< (fold (1+ z))
    fold1+-inflT<     _      {0} = s≤s z≤n
    fold1+-inflT< {f} finfl< {1+ x} =
      2 + x                ≤⟨ s≤s (fold1+-inflT< finfl<) ⟩
      1 + fold (1+ z) f x  ≤⟨ finfl< ⟩
      f  (fold (1+ z) f x) ∎
     where open ≤-Reasoning

  Mon : (f : ℕ → ℕ) → ★₀
  Mon f = ∀ {x y} → x ≤ y → f x ≤ f y

  module _ (P : ℕ → ★₀)
           (P0 : P 0)
           (PS : ∀ {n} → P n → P (1+ n)) where
    ℕ-ind : ∀ {n} → P n
    ℕ-ind {0} = P0
    ℕ-ind {1+ n} = PS ℕ-ind

  open fold-Props
  module _ {f g}(inflf< : Infl< f)(inflTg< : InflT< g) n where
    fold-infl< : Infl< (fold f g n)
    fold-infl< = ℕ-ind (Infl< ∘ fold f g) inflf< inflTg< {n}

  module _ {f} (fmon : Mon f) (finfl< : Infl< f) {z} where
    fold-mon : Mon (fold z f)
    fold-mon {y = 0}    z≤n = ℕ≤.refl
    fold-mon {y = 1+ n} z≤n
      = z               ≤⟨ ≤-step ℕ≤.refl ⟩
        1+ z            ≤⟨ nest-infl< f finfl< n {z} ⟩
        fold z f (1+ n) ∎
      where open ≤-Reasoning
    fold-mon (s≤s m≤n) = fmon (fold-mon m≤n)

  MonT : Endo (Endo ℕ) → ★₀
  MonT g = ∀ {f} → Mon f → Infl< f → Mon (g f)

  module _ {f g}(mon-f : Mon f)(infl-f : Infl< f)
                (mont-g : MonT g)(inflTg< : InflT< g) where
    fold-mon' : ∀ n → Mon (fold f g n)
    fold-mon' 0 = mon-f
    fold-mon' (1+ n) = mont-g (fold-mon' n)
                              (fold-infl< infl-f inflTg< n)

  --  +-fold : ∀ a b → a + b ≡ fold a suc b
  --  *-fold : ∀ a b → a * b ≡ fold 0 (_+_ a) b

  1≤1+a^b : ∀ a b → 1 ≤ (1 + a) ^ b
  1≤1+a^b a 0 = s≤s z≤n
  1≤1+a^b a (1+ b) = 1≤1+a^b a b +-mono z≤n

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
  lem2221 0 = idp
  lem2221 (1+ m) = lem2221 m

  lem4212 : ∀ m → 4 ≡ 2 ↑⟨ 1 + m ⟩ 2
  lem4212 0 = idp
  lem4212 (1+ m)
    = 4                             ≡⟨ lem4212 m ⟩
      2 ↑⟨ 1 + m ⟩ 2                ≡⟨ ap (_↑⟨_⟩_ 2 (1 + m)) (lem2221 m) ⟩
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
  lem3≤ (1+ n) =
    3 ≤⟨ {!!} ⟩
    fold 2*′′ f1 (1 + n) 2 ∎
    where open ≤-Reasoning
          f1 = fold 1

  lem3≤' : ∀ n → 3 ≤ fold 2*′′ (fold 1) n 3
  lem3≤' 0 = s≤s (s≤s (s≤s z≤n))
    where open ≤-Reasoning
  lem3≤' (1+ n) =
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
    f-lem : ∀ n → f (1+ n) ≗ fold 1 (f n)
    f-lem n x = idp

    f2 = λ n b → (2 + a) ↑2+⟨ n ⟩ (2 + b)
    f2-lem : ∀ n → f2 (1+ n) ≗ fold 1 (f2 n)
    f2-lem n x = {!!}

  -- b < (1 + a) * (1 + b)

 -- nest-infl< : ∀ f (finfl< : Infl< f) n → Infl< (nest (1+ n) f)
  infl3< : ∀ a n → Infl< (λ b → (1 + a) ↑2+⟨ n ⟩ (1 + b))
  infl3< a 0 {b} = lem121 a b
  infl3< a (1+ n) {b}
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
      (1 + a) ↑2+⟨ 1+ n ⟩ (1 + b)
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
  a ⇑′⟨ n , k ⟩ b = g n
     module M⇑′ where
      h : ℕ → ℕ
      h x = a ↑⟨ 2 + x ⟩ b

      g : ℕ → ℕ
      g 0      = k
      g (1+ m) = h (g m)

      g-nest : ∀ n → g n ≡ h $⟨ n ⟩ k
      g-nest 0 = idp
      g-nest (1+ n) rewrite g-nest n = idp

  module _ {a n k b} where
    ⇑-⇑′ : a ⇑⟨ n , k ⟩ b ≡ a ⇑′⟨ n , k ⟩ b
    ⇑-⇑′ rewrite M⇑′.g-nest a n k b n = idp

  ⇑₀ : ∀ {a k b} → a ⇑⟨ 0 , k ⟩ b ≡ k
  ⇑₀ = idp

  ⇑₁ : ∀ {a k b} → a ⇑⟨ 1 , k ⟩ b ≡ a ↑⟨ 2 + k ⟩ b
  ⇑₁ = idp

-- https://en.wikipedia.org/wiki/Graham%27s_number
Graham's-number : ℕ
Graham's-number = 3 ⇑⟨ 64 , 4 ⟩ 3
  -- = (f∘⁶⁴…∘f)4
  -- where f x = 3 ↑⟨ 2 + x ⟩ 3
