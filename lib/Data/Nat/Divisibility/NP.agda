{-# OPTIONS --without-K #-}
module Data.Nat.Divisibility.NP where

open import Function
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP
open import Relation.Binary.PropositionalEquality.TrustMe.NP as TrustMe

open import Data.Fin.NP using (Fin▹ℕ; Fin; zero; suc; fromℕ≤)
open import Data.Fin.Properties as FinP
open import Data.Nat.NP
open import Data.Nat.DivMod.NP
open import Data.Nat.Divisibility public
  hiding (_∣?_) -- was slow

nonZeroDivisor-lemmaℕ
  : ∀ n m {r} → n modℕ m ≡ suc r → ¬ m ∣ n
nonZeroDivisor-lemmaℕ .(suc r) zero {r} refl p with 0∣⇒≡0 {suc r} p
... | ()
nonZeroDivisor-lemmaℕ n (suc m) H p = nonZeroDivisor-lemma m (n div (suc m)) (n mod suc m) helper ((_∣_ (suc m) ▸ divModProp n (suc m)) p)
  where helper : Fin▹ℕ (n mod suc m) ≢ 0
        helper e rewrite FinP.toℕ-fromℕ≤ (modℕ<divisor n (suc m)) with ! H ∙ e
        ... | ()

_∣?_ : Decidable _∣_
m ∣? n  with n modℕ m | inspect (_modℕ_ n) m
... | zero  | [ e ] = yes (divides (n div m) (TrustMe.erase (divModPropℕ n m ∙ += e idp)))
... | suc r | [ e ] = no  (nonZeroDivisor-lemmaℕ n m e)

-- -}
-- -}
-- -}
-- -}
