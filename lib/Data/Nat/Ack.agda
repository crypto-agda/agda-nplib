-- NOTE with-K
module Data.Nat.Ack where

open import Data.Nat.NP
open import Data.Nat.HyperOperators
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡

open ack-Props
open InflModule

postulate
  ↑3+ : ∀ a n b → a ↑⟨ 3 + n ⟩ b ≡ fold (_^_ a) (fold 1) n b
  -- mon↑3+'' : ∀ a b → Mon (λ n → fold (_^_ a) (fold 1) n b)

  mon↑3+' : ∀ b → Mon (λ n → fold (_^_ 2) (fold 1) n (3 + b))
-- mon↑3+' b = {!!}

mon↑3+ : ∀ b → Mon (λ n → 2 ↑⟨ 3 + n ⟩ (3 + b))
mon↑3+ b {m} {n} rewrite ↑3+ 2 m (3 + b) | ↑3+ 2 n (3 + b) = mon↑3+' b

open ↑-Props
lem>=3 : ∀ m n → 3 ≤ 2 ↑⟨ 3 + m ⟩ (3 + n)
lem>=3 m n = 3 ≤⟨ s≤s (s≤s (s≤s z≤n)) ⟩
             2 ↑⟨ 3 ⟩ 3 ≡⟨ ↑₃-^ 2 3 ⟩
             2 ^ 3 ≤⟨ lem2^3 n ⟩
             2 ^ (3 + n) ≡⟨ ≡.sym (↑₃-^ 2 (3 + n)) ⟩
             2 ↑⟨ 3 ⟩ (3 + n) ≤⟨ mon↑3+ n z≤n ⟩
             2 ↑⟨ 3 + m ⟩ (3 + n) ∎
  where open ≤-Reasoning

lem>=3'' : ∀ m n → 3 ≤ 2 ↑⟨ suc m ⟩ (3 + n)
lem>=3'' zero n = s≤s (s≤s (s≤s z≤n))
lem>=3'' (suc zero) n rewrite ↑₂-* 2 (3 + n) = s≤s (s≤s (s≤s z≤n))
lem>=3'' (suc (suc m)) n = lem>=3 m n

ack-↑ : ∀ m n → 3 + ack m n ≡ 2 ↑⟨ m ⟩ (3 + n)
ack-↑ zero n = ≡.refl
ack-↑ (suc m) zero = 3 + ack (suc m) 0   ≡⟨ ack-↑ m 1 ⟩
                     2 ↑⟨ m ⟩ 4          ≡⟨ ≡.cong (_↑⟨_⟩_ 2 m) (lem4212 m) ⟩
                     2 ↑⟨ suc m ⟩ 3 ∎
  where open ≡-Reasoning
ack-↑ (suc m) (suc n) = 3 + ack (suc m) (suc n)
                      ≡⟨ ≡.refl ⟩
                        3 + ack m (ack (suc m) n)
                      ≡⟨ ≡.refl ⟩
                        3 + ack m ((3 + ack (suc m) n) ∸ 3)
                      ≡⟨ ≡.cong (λ x → 3 + ack m (x ∸ 3)) (ack-↑ (suc m) n) ⟩
                         3 + ack m (2 ↑⟨ suc m ⟩ (3 + n) ∸ 3)
                      ≡⟨ ack-↑ m (2 ↑⟨ suc m ⟩ (3 + n) ∸ 3) ⟩
                         2 ↑⟨ m ⟩ (3 + (2 ↑⟨ suc m ⟩ (3 + n) ∸ 3))
                      ≡⟨ ≡.cong (λ x → 2 ↑⟨ m ⟩ x) (lem∸ (lem>=3'' m n)) ⟩
                         2 ↑⟨ m ⟩ (2 ↑⟨ suc m ⟩ (3 + n))
                      ≡⟨ ≡.refl ⟩
                        2 ↑⟨ suc m ⟩ (4 + n) ∎ 
  where open ≡-Reasoning
{-
postulate
  1+a^-infl< : ∀ {a}  → Infl< (_^_ (1 + a))

--  2+a*1+b-infl< : ∀ a → Infl< (λ x → (2 + a) * (1 + x))
-- ∀ a b → b < (2 + a) * b
-- fold-a*-fold1 : ∀ {n a} → Infl< (_↑2+⟨_⟩_ (2 + a) n)
fold-a^-fold1 : ∀ {n a} → Infl< (fold (_^_ (1 + a)) (fold 1) n)
fold-a^-fold1 {n} = fold-infl< 1+a^-infl< fold1+-inflT< {n}

↑3+-mon : ∀ a n → Mon (fold (_^_ (1 + a)) (fold 1) n)
↑3+-mon a n = fold-mon' 1+a^-mon 1+a^-infl< (λ η₁ η₂ → fold-mon η₁ η₂) fold1+-inflT< {n}
-- -}
-- -}
-- -}
-- -}
