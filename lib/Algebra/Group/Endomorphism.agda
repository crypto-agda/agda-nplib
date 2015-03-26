{-# OPTIONS --without-K --copatterns #-}
open import Function.NP hiding (_∘_) renaming (_∘′_ to _∘_)
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Function.Extensionality
open import Data.Product.NP
open import Algebra.Monoid
open import Algebra.Monoid.Homomorphism
open import Algebra.Group
open import Algebra.Group.Abelian
open import Algebra.Group.Homomorphism
open import Relation.Binary.PropositionalEquality.NP renaming (_∙_ to _♦_)

import Algebra as A
import Algebra.Structures as AS

{- without commutativity
module Algebra.Group.Endomorphism {{_ : FunExt}}{ℓ}{G : Set ℓ}(𝔾 : Group G)
  where

open Group 𝔾 public

GroupEndomorphism : ∀ {ℓ}{G : Set ℓ} → Group G → Endo G → Set ℓ
GroupEndomorphism 𝔾 = GroupHomomorphism 𝔾 𝔾

EndoG = Σ (Endo G) (GroupEndomorphism 𝔾)

_⊙_ : Endo G → Endo G → Endo G
(f ⊙ g) x = f x ∙ g x

_⁽⁻¹⁾ : Endo G → Endo G
(f ⁽⁻¹⁾) x = (f x)⁻¹

⟨ε⟩ : Endo G
⟨ε⟩ = λ _ → ε

⊙-mon-ops : Monoid-Ops (Endo G)
⊙-mon-ops = _⊙_ , ⟨ε⟩

⊙-mon-struct : Monoid-Struct ⊙-mon-ops
⊙-mon-struct = (λ=ⁱ assoc , λ=ⁱ !assoc) , λ=ⁱ ε∙-identity , λ=ⁱ ∙ε-identity

⊙-grp-ops : Group-Ops (Endo G)
⊙-grp-ops = ⊙-mon-ops , _⁽⁻¹⁾

⊙-grp-struct : Group-Struct ⊙-grp-ops
⊙-grp-struct = ⊙-mon-struct , λ=ⁱ (fst inverse) , λ=ⁱ (snd inverse)

distr : _∘_ DistributesOverˡ _⊙_
distr {f} {g} {h} = λ= λ x → {!!}

ring : A.Ring _ _
ring = record
         { Carrier = Endo G
         ; _≈_ = _≡_
         ; _+_ = _⊙_
         ; _*_ = _∘_
         ; -_ = _⁽⁻¹⁾
         ; 0# = ⟨ε⟩
         ; 1# = id
         ; isRing =
           record
           { +-isAbelianGroup =
             record
             { isGroup =
               record
               { isMonoid =
                 record
                 { isSemigroup =
                   record { isEquivalence = isEquivalence
                          ; assoc = λ _ _ _ → λ=ⁱ assoc
                          ; ∙-cong = ap₂ _⊙_ }
                 ; identity = (λ _ → λ=ⁱ ε∙-identity)
                            , (λ _ → λ=ⁱ ∙ε-identity) }
               ; inverse = (λ _ → λ=ⁱ (fst inverse))
                         , (λ _ → λ=ⁱ (snd inverse))
               ; ⁻¹-cong = ap _⁽⁻¹⁾ }
             ; comm = {!!} }
           ; *-isMonoid =
             record
             { isSemigroup =
               record { isEquivalence = isEquivalence
                      ; assoc = λ _ _ _ → idp
                      ; ∙-cong = ap₂ _∘_ }
             ; identity = (λ _ → idp) , (λ _ → idp) }
           ; distrib = {!!} }
         }
-}

module Algebra.Group.Endomorphism {{_ : FunExt}}{ℓ}{G : Set ℓ} -- (𝔾 : Group G)
  where

postulate
  𝔾 : Abelian-Group G

module 𝔾 = Abelian-Group 𝔾

open 𝔾

𝔾' : Group G
𝔾' = grp

open GroupHomomorphism

GroupEndomorphism : ∀ {ℓ}{G : Set ℓ} → Group G → Endo G → Set ℓ
GroupEndomorphism 𝔾 = GroupHomomorphism 𝔾 𝔾

EndoG = Σ (Endo G) (GroupEndomorphism grp)

endoG= : {f g : EndoG} → (∀ {x} → fst f x ≡ fst g x) → f ≡ g
endoG= {f} {g} fg = ?

_⊙_ : Endo G → Endo G → Endo G
(f ⊙ g) x = f x ∙ g x

_⊙'_ : EndoG → EndoG → EndoG
fst (f ⊙' g) = fst f ⊙ fst g
hom (snd (f ⊙' g)) = ∙= (hom (snd f)) (hom (snd g)) ♦ interchange

_⁽⁻¹⁾ : Endo G → Endo G
(f ⁽⁻¹⁾) x = (f x)⁻¹

_⁽⁻¹⁾' : EndoG → EndoG
fst (f ⁽⁻¹⁾') x = (fst f x)⁻¹
hom (snd (f ⁽⁻¹⁾')) = ap _⁻¹ (hom (snd f)) ♦ ⁻¹-hom

⟨ε⟩ : Endo G
⟨ε⟩ = λ _ → ε

⟨ε⟩' : EndoG
fst ⟨ε⟩'       = ⟨ε⟩
hom (snd ⟨ε⟩') = ! ε∙-identity

⊙-mon-ops : Monoid-Ops (Endo G)
⊙-mon-ops = _⊙_ , ⟨ε⟩

⊙-mon-ops' : Monoid-Ops EndoG
⊙-mon-ops' = _⊙'_ , ⟨ε⟩'

⊙-mon-struct : Monoid-Struct ⊙-mon-ops
⊙-mon-struct = (λ=ⁱ assoc , λ=ⁱ !assoc) , λ=ⁱ ε∙-identity , λ=ⁱ ∙ε-identity

⊙-mon-struct' : Monoid-Struct ⊙-mon-ops'
⊙-mon-struct' = (endoG= assoc , endoG= !assoc) , endoG= ε∙-identity , endoG= ∙ε-identity

⊙-grp-ops : Group-Ops (Endo G)
⊙-grp-ops = ⊙-mon-ops , _⁽⁻¹⁾

⊙-grp-ops' : Group-Ops EndoG
⊙-grp-ops' = ⊙-mon-ops' , _⁽⁻¹⁾'

⊙-grp-struct : Group-Struct ⊙-grp-ops
⊙-grp-struct = ⊙-mon-struct , λ=ⁱ (fst inverse) , λ=ⁱ (snd inverse)

⊙-grp-struct' : Group-Struct ⊙-grp-ops'
⊙-grp-struct' = ⊙-mon-struct' , endoG= (fst inverse) , endoG= (snd inverse)

id' : EndoG
fst id' = id
hom (snd id') = idp

_∘'_ : EndoG → EndoG → EndoG
fst (f ∘' g) = fst f ∘ fst g
hom (snd (f ∘' g)) = ap (fst f) (hom (snd g)) ♦ hom (snd f)

-- NOTE: only the the first function needs to be an homomorphism
distr : _∘'_ DistributesOverˡ _⊙'_
distr {_ , mk f-hom} = endoG= f-hom

{-
ring : A.Ring _ _
ring = record
         { Carrier = EndoG
         ; _≈_ = _≡_
         ; _+_ = _⊙'_
         ; _*_ = _∘'_
         ; -_ = _⁽⁻¹⁾'
         ; 0# = ⟨ε⟩'
         ; 1# = {!id!}
         ; isRing =
           record
           { +-isAbelianGroup =
             record
             { isGroup =
               record
               { isMonoid =
                 record
                 { isSemigroup =
                   record { isEquivalence = isEquivalence
                          ; assoc = {!λ _ _ _ → λ=ⁱ assoc!}
                          ; ∙-cong = ap₂ _⊙'_ }
                 ; identity = (λ _ → λ=ⁱ ε∙-identity)
                            , (λ _ → λ=ⁱ ∙ε-identity) }
               ; inverse = (λ _ → λ=ⁱ (fst inverse))
                         , (λ _ → λ=ⁱ (snd inverse))
               ; ⁻¹-cong = ap _⁽⁻¹⁾ }
             ; comm = λ _ _ → λ=ⁱ comm }
           ; *-isMonoid =
             record
             { isSemigroup =
               record { isEquivalence = isEquivalence
                      ; assoc = λ _ _ _ → idp
                      ; ∙-cong = ap₂ _∘_ }
             ; identity = (λ _ → idp) , (λ _ → idp) }
           ; distrib = (λ _ _ _ → λ=ⁱ {!!}) , {!λ _ _ _ → λ=ⁱ distr!} }
         }
{-
ring : A.Ring _ _
ring = record
         { Carrier = Endo G
         ; _≈_ = _≡_
         ; _+_ = _⊙_
         ; _*_ = _∘_
         ; -_ = _⁽⁻¹⁾
         ; 0# = ⟨ε⟩
         ; 1# = id
         ; isRing =
           record
           { +-isAbelianGroup =
             record
             { isGroup =
               record
               { isMonoid =
                 record
                 { isSemigroup =
                   record { isEquivalence = isEquivalence
                          ; assoc = λ _ _ _ → λ=ⁱ assoc
                          ; ∙-cong = ap₂ _⊙_ }
                 ; identity = (λ _ → λ=ⁱ ε∙-identity)
                            , (λ _ → λ=ⁱ ∙ε-identity) }
               ; inverse = (λ _ → λ=ⁱ (fst inverse))
                         , (λ _ → λ=ⁱ (snd inverse))
               ; ⁻¹-cong = ap _⁽⁻¹⁾ }
             ; comm = λ _ _ → λ=ⁱ comm }
           ; *-isMonoid =
             record
             { isSemigroup =
               record { isEquivalence = isEquivalence
                      ; assoc = λ _ _ _ → idp
                      ; ∙-cong = ap₂ _∘_ }
             ; identity = (λ _ → idp) , (λ _ → idp) }
           ; distrib = (λ _ _ _ → λ=ⁱ {!!}) , {!λ _ _ _ → λ=ⁱ distr!} }
         }
-- -}
-- -}
-- -}
-- -}
