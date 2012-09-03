
module Data.Bits.Count where

open import Data.Bits
open import Data.Bits.OperationSyntax
import Data.Bits.Search as Search
open Search.SimpleSearch
open import Data.Bits.Sum


import Data.Bool.NP as Bool
open Bool hiding (_==_; toℕ)
open import Data.Bool.Properties using (not-involutive)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open Fin using (Fin; zero; suc; #_; inject₁; inject+; raise) renaming (_+_ to _+ᶠ_)

open import Data.Maybe.NP

open import Data.Nat.NP hiding (_==_) 
open import Data.Nat.Properties
import Data.Vec.NP as V
open V hiding (rewire; rewireTbl; sum) renaming (map to vmap; swap to vswap)

open import Data.Product using (_×_; _,_; uncurry; proj₁; proj₂)

open import Function.NP

import Relation.Binary.PropositionalEquality.NP as ≡
open ≡

#⟨_⟩ : ∀ {n} → (Bits n → Bool) → ℕ
#⟨ pred ⟩ = sum (Bool.toℕ ∘ pred)

-- #-ext
#-≗ : ∀ {n} (f g : Bits n → Bool) → f ≗ g → #⟨ f ⟩ ≡ #⟨ g ⟩
#-≗ f g f≗g = sum-≗ (Bool.toℕ ∘ f) (Bool.toℕ ∘ g) (λ x → ≡.cong Bool.toℕ (f≗g x))

#-comm : ∀ {n} (pad : Bits n) (f : Bits n → Bool) → #⟨ f ⟩ ≡ #⟨ f ∘ _⊕_ pad ⟩
#-comm pad f = sum-comm pad (Bool.toℕ ∘ f)

#-bij : ∀ {n} f (g : Bits n → Bit) → #⟨ g ∘ eval f ⟩ ≡ #⟨ g ⟩
#-bij f g = sum-bij f (Bool.toℕ ∘ g)

#-⊕ : ∀ {c} (bs : Bits c) (f : Bits c → Bit) → #⟨ f ⟩ ≡ #⟨ f ∘ _⊕_ bs ⟩
#-⊕ = #-comm

#-const : ∀ n b → #⟨ (λ (_ : Bits n) → b) ⟩ ≡ ⟨2^ n * Bool.toℕ b ⟩
#-const n b = sum-const n (Bool.toℕ b)

#never≡0 : ∀ n → #⟨ never n ⟩ ≡ 0
#never≡0 = sum-const0≡0

#always≡2^_ : ∀ n → #⟨ always n ⟩ ≡ 2^ n
#always≡2^ n = sum-const n 1

#-dist : ∀ {n} (f₀ f₁ : Bits n → Bit) → sum (λ x → Bool.toℕ (f₀ x) + Bool.toℕ (f₁ x)) ≡ #⟨ f₀ ⟩ + #⟨ f₁ ⟩
#-dist f₀ f₁ = sum-dist (Bool.toℕ ∘ f₀) (Bool.toℕ ∘ f₁)

#-+ : ∀ {m n} (f : Bits (m + n) → Bit) →
                 #⟨ f ⟩ ≡ sum {m} (λ xs → #⟨ (λ ys → f (xs ++ ys)) ⟩ )
#-+ {m} {n} f = sum-+ {m} {n} (Bool.toℕ ∘ f)

#-# : ∀ {m n} (f : Bits (m + n) → Bit) →
                          sum {m} (λ xs → #⟨ (λ ys → f (xs ++ ys)) ⟩)
                        ≡ sum {n} (λ ys → #⟨ (λ (xs : Bits m) → f (xs ++ ys)) ⟩)
#-# {m} {n} f = sum-sum {m} {n} (Bool.toℕ ∘ f)

#-swap : ∀ {m n} (f : Bits (m + n) → Bit) → #⟨ f ∘ vswap n {m} ⟩ ≡ #⟨ f ⟩
#-swap {m} {n} f = sum-swap {m} {n} (Bool.toℕ ∘ f)

#⟨==_⟩ : ∀ {n} (xs : Bits n) → #⟨ _==_ xs ⟩ ≡ 1
#⟨== [] ⟩ = refl
#⟨==_⟩ {suc n} (true ∷ xs)  rewrite #never≡0 n | #⟨== xs ⟩ = refl
#⟨==_⟩ {suc n} (false ∷ xs) rewrite #never≡0 n | #⟨== xs ⟩ = refl

≗-cong-# : ∀ {n} (f g : Bits n → Bit) → f ≗ g → #⟨ f ⟩ ≡ #⟨ g ⟩
≗-cong-# f g f≗g = sum-≗ _ _ (cong Bool.toℕ ∘ f≗g)

-- #-+ : ∀ {n a b} (f : Bits (suc n) → Bit) → #⟨ f ∘ 0∷_ ⟩ ≡ a → #⟨ f ∘ 1∷_ ⟩ ≡ b → #⟨ f ⟩ ≡ a + b
-- #-+ f f0 f1 rewrite f0 | f1 = refl

#-take-drop : ∀ m n (f : Bits m → Bit) (g : Bits n → Bit)
                → #⟨ (f ∘ take m) |∧| (g ∘ drop m) ⟩ ≡ #⟨ f ⟩ * #⟨ g ⟩
#-take-drop zero n f g with f []
... | true rewrite ℕ°.+-comm #⟨ g ⟩ 0 = refl
... | false = #never≡0 n
#-take-drop (suc m) n f g
  rewrite ≗-cong-# ((f ∘ take (suc m)) |∧| (g ∘ drop (suc m)) ∘ 0∷_)
                   ((f ∘ 0∷_ ∘ take m) |∧| (g ∘ drop m))
                     (λ x → cong₂ (λ x y → f x ∧ g y) (take-∷ m 0b x) (drop-∷ m 0b x))
        | #-take-drop m n (f ∘ 0∷_) g
        | ≗-cong-# ((f ∘ take (suc m)) |∧| (g ∘ drop (suc m)) ∘ 1∷_)
                   ((f ∘ 1∷_ ∘ take m) |∧| (g ∘ drop m))
                     (λ x → cong₂ (λ x y → f x ∧ g y) (take-∷ m 1b x) (drop-∷ m 1b x))
        | #-take-drop m n (f ∘ 1∷_) g
          = sym (proj₂ ℕ°.distrib #⟨ g ⟩ #⟨ f ∘ 0∷_ ⟩ #⟨ f ∘ 1∷_ ⟩)

#-drop-take : ∀ m n (f : Bits n → Bit) (g : Bits m → Bit)
                  → #⟨ (f ∘ drop m) |∧| (g ∘ take m) ⟩ ≡ #⟨ f ⟩ * #⟨ g ⟩
#-drop-take m n f g =
              #⟨ (f ∘ drop m) |∧| (g ∘ take m) ⟩
            ≡⟨ ≗-cong-# ((f ∘ drop m) |∧| (g ∘ take m)) ((g ∘ take m) |∧| (f ∘ drop m)) (λ x → Bool°.+-comm (f (drop m x)) _) ⟩
              #⟨ (g ∘ take m) |∧| (f ∘ drop m) ⟩
            ≡⟨ #-take-drop m n g f ⟩
              #⟨ g ⟩ * #⟨ f ⟩
            ≡⟨ ℕ°.*-comm #⟨ g ⟩ _ ⟩
              #⟨ f ⟩ * #⟨ g ⟩
            ∎
      where open ≡-Reasoning

#-take : ∀ m n (f : Bits m → Bit) → #⟨ f ∘ take m {n} ⟩ ≡ 2^ n * #⟨ f ⟩
#-take m n f = #⟨ f ∘ take m {n} ⟩
             ≡⟨ #-drop-take m n (always n) f ⟩
               #⟨ always n ⟩ * #⟨ f ⟩
             ≡⟨ cong (flip _*_ #⟨ f ⟩) (#always≡2^ n) ⟩
               2^ n * #⟨ f ⟩
             ∎
      where open ≡-Reasoning

#-drop : ∀ m n (f : Bits m → Bit) → #⟨ f ∘ drop n ⟩ ≡ 2^ n * #⟨ f ⟩
#-drop m n f = #⟨ f ∘ drop n ⟩
             ≡⟨ #-take-drop n m (always n) f ⟩
               #⟨ always n ⟩ * #⟨ f ⟩
             ≡⟨ cong (flip _*_ #⟨ f ⟩) (#always≡2^ n) ⟩
               2^ n * #⟨ f ⟩
             ∎
      where open ≡-Reasoning

#⟨_==⟩ : ∀ {n} (xs : Bits n) → #⟨ flip _==_ xs ⟩ ≡ 1
#⟨ xs ==⟩ = trans (≗-cong-# (flip _==_ xs) (_==_ xs) (flip ==-comm xs)) #⟨== xs ⟩

#⇒ : ∀ {n} (f g : Bits n → Bit) → (∀ x → T (f x) → T (g x)) → #⟨ f ⟩ ≤ #⟨ g ⟩
#⇒ {zero} f g f⇒g with f [] | g [] | f⇒g []
... | true  | true  | _ = s≤s z≤n
... | true  | false | p = ⊥-elim (p _)
... | false | _     | _ = z≤n
#⇒ {suc n} f g f⇒g = #⇒ (f ∘ 0∷_) (g ∘ 0∷_) (f⇒g ∘ 0∷_)
               +-mono #⇒ (f ∘ 1∷_) (g ∘ 1∷_) (f⇒g ∘ 1∷_)

#-∧-∨ᵇ : ∀ x y → Bool.toℕ (x ∧ y) + Bool.toℕ (x ∨ y) ≡ Bool.toℕ x + Bool.toℕ y
#-∧-∨ᵇ true y rewrite ℕ°.+-comm (Bool.toℕ y) 1 = refl
#-∧-∨ᵇ false y = refl

#-LEM : ∀ {n} → (f g : Bits n → Bit) → #⟨ f ⟩ ≡ #⟨ g |∧| f ⟩ + #⟨ |not| g |∧| f ⟩
#-LEM {zero} f g with g []
... | false = refl
... | true  = ℕ°.+-comm 0 #⟨ f ⟩
#-LEM {suc n} f g 
  rewrite #-LEM (f ∘ 0∷_) (g ∘ 0∷_)
        | #-LEM (f ∘ 1∷_) (g ∘ 1∷_)
          = +-interchange #⟨ (g ∘ 0∷_) |∧| (f ∘ 0∷_) ⟩
                #⟨ |not| (g ∘ 0∷_) |∧| (f ∘ 0∷_) ⟩ 
                #⟨ (g ∘ 1∷_) |∧| (f ∘ 1∷_) ⟩
                #⟨ |not| (g ∘ 1∷_) |∧| (f ∘ 1∷_) ⟩


#-∧-snd : ∀ {n} (f g : Bits n → Bit) → #⟨ f |∧| g ⟩ ≤ #⟨ g ⟩
#-∧-snd {zero} f g with f [] | g []
... | false | false = z≤n
... | false | true  = z≤n
... | true  | _     = ℕ≤.reflexive refl
#-∧-snd {suc n} f g = #-∧-snd (f ∘ 0∷_) (g ∘ 0∷_) 
               +-mono #-∧-snd (f ∘ 1∷_) (g ∘ 1∷_)

#-∧-fst : ∀ {n} (f g : Bits n → Bit) → #⟨ f |∧| g ⟩ ≤ #⟨ f ⟩
#-∧-fst f g = 
          #⟨ f |∧| g ⟩ 
            ≡⟨ #-≗ (f |∧| g) (g |∧| f) (|∧|-comm f g) ⟩ 
          #⟨ g |∧| f ⟩ 
            ≤⟨ #-∧-snd g f ⟩ 
          #⟨ f ⟩ ∎
      where open ≤-Reasoning

#-∧-∨ : ∀ {n} (f g : Bits n → Bit) → #⟨ f |∧| g ⟩ + #⟨ f |∨| g ⟩ ≡ #⟨ f ⟩ + #⟨ g ⟩
#-∧-∨ {zero} f g = #-∧-∨ᵇ (f []) (g [])
#-∧-∨ {suc n} f g =
  trans
    (trans
      (helper #⟨ (f ∘ 0∷_) |∧| (g ∘ 0∷_) ⟩
              #⟨ (f ∘ 1∷_) |∧| (g ∘ 1∷_) ⟩
              #⟨ (f ∘ 0∷_) |∨| (g ∘ 0∷_) ⟩
                #⟨ (f ∘ 1∷_) |∨| (g ∘ 1∷_) ⟩)
      (cong₂ _+_ (#-∧-∨ (f ∘ 0∷_) (g ∘ 0∷_))
                 (#-∧-∨ (f ∘ 1∷_) (g ∘ 1∷_))))
      (helper #⟨ f ∘ 0∷_ ⟩ #⟨ g ∘ 0∷_ ⟩ #⟨ f ∘ 1∷_ ⟩ #⟨ g ∘ 1∷_ ⟩)
        where open SemiringSolver
              helper : ∀ x y z t → x + y + (z + t) ≡ x + z + (y + t)
              helper = solve 4 (λ x y z t → x :+ y :+ (z :+ t) := x :+ z :+ (y :+ t)) refl

#∨' : ∀ {n} (f g : Bits n → Bit) → #⟨ f |∨| g ⟩ ≤ #⟨ f ⟩ + #⟨ g ⟩
#∨' {zero} f g with f []
... | true  = s≤s z≤n
... | false = ℕ≤.refl
#∨' {suc _} f g = ℕ≤.trans (#∨' (f ∘ 0∷_) (g ∘ 0∷_) +-mono
                            #∨' (f ∘ 1∷_) (g ∘ 1∷_))
                        (ℕ≤.reflexive
                          (helper #⟨ f ∘ 0∷_ ⟩ #⟨ g ∘ 0∷_ ⟩ #⟨ f ∘ 1∷_ ⟩ #⟨ g ∘ 1∷_ ⟩))
    where open SemiringSolver
          helper : ∀ x y z t → x + y + (z + t) ≡ x + z + (y + t)
          helper = solve 4 (λ x y z t → x :+ y :+ (z :+ t) := x :+ z :+ (y :+ t)) refl

#∨ : ∀ {m n o} {f g : Bits o → Bit} → #⟨ f ⟩ ≤ m → #⟨ g ⟩ ≤ n → #⟨ f |∨| g ⟩ ≤ (m + n)
#∨ {m} {n} {o} {f} {g} pf pg = ℕ≤.trans (#∨' f g) (pf +-mono pg)

#∧ : ∀ {m n o} {f g : Bits o → Bit} → #⟨ f ⟩ ≤ m → #⟨ g ⟩ ≤ n → #⟨ f |∧| g ⟩ ≤ (m + n)
#∧ {f = f} {g} pf pg = ℕ≤.trans (#⇒ (f |∧| g) (f |∨| g) (λ x → ∧⇒∨ (f x) (g x))) (#∨ {f = f} pf pg)

#-bound : ∀ c (f : Bits c → Bit) → #⟨ f ⟩ ≤ 2^ c
#-bound zero    f = Bool.toℕ≤1 (f [])
#-bound (suc c) f = #-bound c (f ∘ 0∷_) +-mono #-bound c (f ∘ 1∷_)

#-∘vnot : ∀ c (f : Bits c → Bit) → #⟨ f ⟩ ≡ #⟨ f ∘ vnot ⟩
#-∘vnot _ f = #-⊕ 1ⁿ f

#-∘xorᵢ : ∀ {c} (i : Fin c) (f : Bits c → Bit) b → #⟨ f ⟩ ≡ #⟨ f ∘ onᵢ (_xor_ b) i ⟩
#-∘xorᵢ i f b = pf
  where pad = onᵢ (_xor_ b) i 0ⁿ
        pf : #⟨ f ⟩ ≡ #⟨ f ∘ onᵢ (_xor_ b) i ⟩
        pf rewrite #-⊕ pad f = ≗-cong-# (f ∘ _⊕_ pad) (f ∘ onᵢ (_xor_ b) i) (cong (_$_ f) ∘ sym ∘ onᵢ-xor-⊕ b i)

#-∘notᵢ : ∀ {c} (i : Fin c) (f : Bits c → Bit) → #⟨ f ⟩ ≡ #⟨ f ∘ notᵢ i ⟩
#-∘notᵢ i f = #-∘xorᵢ i f true

#-not∘ : ∀ c (f : Bits c → Bit) → #⟨ f ⟩ ≡ 2^ c ∸ #⟨ not ∘ f ⟩
#-not∘ zero f with f []
... | true  = ≡.refl
... | false = ≡.refl
#-not∘ (suc c) f
  rewrite #-not∘ c (f ∘ 0∷_)
        | #-not∘ c (f ∘ 1∷_) = factor-+-∸ (#-bound c (not ∘ f ∘ 0∷_)) (#-bound c (not ∘ f ∘ 1∷_))

#-not∘′ : ∀ c (f : Bits c → Bit) → #⟨ not ∘ f ⟩ ≡ 2^ c ∸ #⟨ f ⟩
#-not∘′ c f = #⟨ not ∘ f ⟩
            ≡⟨ #-not∘ c (not ∘ f) ⟩
              2^ c ∸ #⟨ not ∘ not ∘ f ⟩
            ≡⟨ ≡.cong (λ g → 2^ c ∸ g) (≗-cong-# (not ∘ not ∘ f) f (not-involutive ∘ f)) ⟩
              2^ c ∸ #⟨ f ⟩
            ∎
      where open ≡-Reasoning


difference-lemma : ∀ {n}(A B F : Bits n → Bit) 
      → #⟨ |not| F |∧| A ⟩ ≡ #⟨ |not| F |∧| B ⟩
      → dist #⟨ A ⟩ #⟨ B ⟩ ≤ #⟨ F ⟩
difference-lemma A B F A∧¬F≡B∧¬F = 
  dist #⟨ A ⟩ #⟨ B ⟩ 
    ≡⟨ cong₂ dist (#-LEM A F) (#-LEM B F) ⟩
  dist (#⟨ F |∧| A ⟩ + #⟨ |not| F |∧| A ⟩)
       (#⟨ F |∧| B ⟩ + #⟨ |not| F |∧| B ⟩)
    ≡⟨ cong₂ dist (ℕ°.+-comm #⟨ F |∧| A ⟩ #⟨ |not| F |∧| A ⟩) 
                  (ℕ°.+-comm #⟨ F |∧| B ⟩ #⟨ |not| F |∧| B ⟩) ⟩
  dist (#⟨ |not| F |∧| A ⟩ + #⟨ F |∧| A ⟩)
       (#⟨ |not| F |∧| B ⟩ + #⟨ F |∧| B ⟩)
    ≡⟨ cong₂ dist (refl {x = #⟨ |not| F |∧| A ⟩ + #⟨ F |∧| A ⟩})
                  (cong₂ _+_ (sym A∧¬F≡B∧¬F) (refl {x = #⟨ F |∧| B ⟩})) ⟩
  dist (#⟨ |not| F |∧| A ⟩ + #⟨ F |∧| A ⟩)
       (#⟨ |not| F |∧| A ⟩ + #⟨ F |∧| B ⟩)
    ≡⟨ dist-x+ #⟨ |not| F |∧| A ⟩ #⟨ F |∧| A ⟩ #⟨ F |∧| B ⟩ ⟩
  dist #⟨ F |∧| A ⟩ #⟨ F |∧| B ⟩
    ≤⟨ dist-bounded {#⟨ F |∧| A ⟩} {#⟨ F |∧| B ⟩} {#⟨ F ⟩} (#-∧-fst F A) (#-∧-fst F B) ⟩ 
  #⟨ F ⟩ ∎
     where open ≤-Reasoning

#⟨_⟩ᶠ : ∀ {n} → (Bits n → Bool) → Fin (suc (2^ n))
#⟨ pred ⟩ᶠ = countᶠ pred (allBits _)

#⟨⟩-spec : ∀ {n} (pred : Bits n → Bool) → #⟨ pred ⟩ ≡ Fin.toℕ #⟨ pred ⟩ᶠ
#⟨⟩-spec {zero}  pred with pred []
... | true = refl
... | false = refl
#⟨⟩-spec {suc n} pred rewrite count-++ pred (vmap 0∷_ (allBits n)) (vmap 1∷_ (allBits n))
                            | #⟨⟩-spec {n} (pred ∘ 0∷_)
                            | #⟨⟩-spec {n} (pred ∘ 1∷_)
                            | count-∘ 0∷_ pred (allBits n)
                            | count-∘ 1∷_ pred (allBits n) = refl

ext-# : ∀ {c} {f g : Bits c → Bit} → f ≗ g → #⟨ f ⟩ᶠ ≡ #⟨ g ⟩ᶠ
ext-# f≗g = ext-countᶠ f≗g (allBits _)

find? : ∀ {n a} {A : Set a} → (Bits n →? A) →? A
find? = search (M?._∣_ _)

findB : ∀ {n} → (Bits n → Bool) →? Bits n
findB pred = find? (λ x → if pred x then just x else nothing)
