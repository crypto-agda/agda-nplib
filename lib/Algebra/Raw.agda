open import Type using (Type_)
open import Function.NP
open import Data.Nat using (ℕ) renaming (suc to 1+_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Relation.Binary.PropositionalEquality.NP renaming (_∙_ to _♦_)

module Algebra.Raw where

record Magma {ℓ}(A : Type ℓ) : Type ℓ where
  constructor ⟨_⟩
  infixl 7 _∙_

  field
    _∙_ : A → A → A

  infix 8 _² _³ _⁴

  _² : A → A
  x ² = x ∙ x

  _³ : A → A
  x ³ = x ² ∙ x

  _⁴ : A → A
  x ⁴ = x ³ ∙ x

  infix 8 _^¹⁺_
  _^¹⁺_ : A → ℕ → A
  x ^¹⁺ n = nest n (_∙_ x) x

  module _ {x x' y y'}(p : x ≡ x')(q : y ≡ y') where
    ∙= : x ∙ y ≡ x' ∙ y'
    ∙= = ap (_∙_ x) q ♦ ap (λ z → z ∙ y') p

record Monoid-Ops {ℓ} (A : Type ℓ) : Type ℓ where
  constructor _,_
  infixl 7 _∙_

  field
    _∙_ : A → A → A
    ε   : A

  ∙-magma : Magma A
  ∙-magma = ⟨ _∙_ ⟩

  open Magma ∙-magma public hiding (_∙_)

  infix 8 _^⁺_
  _^⁺_ : A → ℕ → A
  x ^⁺ n = nest n (_∙_ x) ε

-- A renaming of Monoid-Ops with additive notation
module Additive-Monoid-Ops {ℓ}{M : Set ℓ} (mon : Monoid-Ops M) where
  private
   module M = Monoid-Ops mon
    using    ()
    renaming ( _∙_ to _+_
             ; ε to 0#
             ; _² to 2⊗_
             ; _³ to 3⊗_
             ; _⁴ to 4⊗_
             ; _^¹⁺_ to _⊗¹⁺_
             ; _^⁺_ to _⊗⁺_
             ; ∙= to +=
             )
  open M public using (0#; +=)
  infixl 6 _+_
  infixl 7 _⊗¹⁺_ _⊗⁺_ 2⊗_ 3⊗_ 4⊗_
  _+_   = M._+_
  _⊗¹⁺_ = M._⊗¹⁺_
  _⊗⁺_  = M._⊗⁺_
  2⊗_   = M.2⊗_
  3⊗_   = M.3⊗_
  4⊗_   = M.4⊗_

-- A renaming of Monoid-Ops with multiplicative notation
module Multiplicative-Monoid-Ops {ℓ}{M : Type ℓ} (mon-ops : Monoid-Ops M)
  = Monoid-Ops mon-ops
    renaming ( _∙_ to _*_
             ; ε to 1#
             ; ∙= to *=
             )

record Group-Ops {ℓ} (A : Type ℓ) : Type ℓ where
  constructor _,_

  field
    mon-ops : Monoid-Ops A
    _⁻¹     : A → A

  open Monoid-Ops mon-ops public

  ⁻¹= : ∀ {x y} → x ≡ y → x ⁻¹ ≡ y ⁻¹
  ⁻¹= = ap _⁻¹

  infixl 7 _/_

  _/_ : A → A → A
  x / y = x ∙ y ⁻¹

  /-magma : Magma A
  /-magma = ⟨ _/_ ⟩

  open Magma /-magma public using () renaming (∙= to /=)

  _^⁻_ _^⁻′_ : A → ℕ → A
  x ^⁻ n = (x ^⁺ n)⁻¹
  x ^⁻′ n = (x ⁻¹)^⁺ n

  _^_ : A → ℤ → A
  x ^ -[1+ n ] = x ^⁻(1+ n)
  x ^ (+ n)    = x ^⁺ n

-- A renaming of Group-Ops with additive notation
module Additive-Group-Ops {ℓ}{G : Type ℓ} (grp : Group-Ops G) where
  private
   module M = Group-Ops grp
    using    ()
    renaming ( _⁻¹ to 0−_
             ; ⁻¹= to 0−=
             ; _/_ to _−_
             ; _^⁻_ to _⊗⁻_
             ; _^_ to _⊗_
             ; mon-ops to +-mon-ops
             ; /= to −=)
  open M public using (0−_; +-mon-ops; −=; 0−=)
  open Additive-Monoid-Ops +-mon-ops public
  infixl 6 _−_
  infixl 7 _⊗⁻_ _⊗_
  _−_   = M._−_
  _⊗⁻_  = M._⊗⁻_
  _⊗_   = M._⊗_

-- A renaming of Group-Ops with multiplicative notation
module Multiplicative-Group-Ops {ℓ}{G : Type ℓ} (grp : Group-Ops G) = Group-Ops grp
    using    ( _^⁺_; _²; _³; _⁴; _⁻¹; _/_; /=; _^⁻_; _^_; /-magma; ⁻¹= )
    renaming ( _∙_ to _*_; ε to 1#; mon-ops to *-mon-ops; ∙= to *= )

record Ring-Ops {ℓ} (A : Type ℓ) : Type ℓ where
  constructor _,_
  infixl 6 2+_

  field
    +-grp-ops  : Group-Ops A
    *-mon-ops : Monoid-Ops A

  open Additive-Group-Ops        +-grp-ops public
    renaming (2⊗_ to 2*_)
  open Multiplicative-Monoid-Ops *-mon-ops public

  suc : A → A
  suc = _+_ 1#

  pred : A → A
  pred x = x − 1#

  2# 3# -0# -1# : A
  2#  = suc 1#
  3#  = suc 2#
  -0# = 0− 0#
  -1# = 0− 1#

  ℕ[_] : ℕ → A
  ℕ[ 0    ] = 0#
  ℕ[ 1+ n ] = nest n suc 1#

  ℤ[_] : ℤ → A
  ℤ[ + x      ] = ℕ[ x ]
  ℤ[ -[1+ x ] ] = 0− ℕ[ 1+ x ]

  -- TODO use _^⁺_ and _^_ from group/monoid
  _^ℕ_ : A → ℕ → A
  b ^ℕ 0      = 1#
  b ^ℕ (1+ n) = nest n (_*_ b) b

  2+_ : A → A
  2+ x = 2# + x

record Field-Ops {ℓ} (A : Set ℓ) : Set ℓ where

  field
    +-grp-ops : Group-Ops A
    *-grp-ops : Group-Ops A

  open Multiplicative-Group-Ops *-grp-ops public
    using ( _⁻¹; ⁻¹=; _/_; /-magma; /=; _^⁻_; _^_; *-mon-ops )

  rng-ops : Ring-Ops A
  rng-ops = +-grp-ops , *-mon-ops

  open Ring-Ops rng-ops public
    hiding (+-grp-ops; *-mon-ops)

  _^ℤ_ : A → ℤ → A
  b ^ℤ (+ n)    = b ^ℕ n
  b ^ℤ -[1+ n ] = (b ^ℕ (1+ n))⁻¹
-- -}
-- -}
-- -}
-- -}
