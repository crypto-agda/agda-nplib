open import Algebra.Raw
import Algebra.Field as Field

open import Relation.Binary.PropositionalEquality.NP as ≡

open import Level
open import Data.Nat as Nat using (ℕ) renaming (suc to 1+_)
open import Data.One
open import Data.Product

open import Function

module Algebra.Field.Solver where

data R-Op : Set where
  [+] [*] [-] : R-Op

data F-Op : Set where
  [+] [*] [-] [/] : F-Op

data Tm (F Op Var : Set) : Set where
  op  : (o : Op) (t₁ t₂ : Tm F Op Var) → Tm F Op Var
  con : F → Tm F Op Var
  var : Var → Tm F Op Var

infixl 6 _:+_ _:-_
infixl 7 _:*_ _:/_
pattern _:+_ x y = op [+] x y
pattern _:*_ x y = op [*] x y
pattern _:-_ x y = op [-] x y
pattern _:/_ x y = op [/] x y

R-include : R-Op → F-Op
R-include [+] = [+]
R-include [*] = [*]
R-include [-] = [-]

module _ {F Op Var : Set}(evalOp : Op → F → F → F)(ρ : Var → F) where
  eval : Tm F Op Var → F
  eval (op o t u) = evalOp o (eval t) (eval u)
  eval (con x) = x
  eval (var x) = ρ x

module _ {F Var : Set}(evF : Tm F F-Op Var → Set) where
  Assumptions : Tm F F-Op Var → Set
  Assumptions (op [+] t u) = Assumptions t × Assumptions u
  Assumptions (op [*] t u) = Assumptions t × Assumptions u
  Assumptions (op [-] t u) = Assumptions t × Assumptions u
  Assumptions (op [/] t u) = Assumptions t × Assumptions u × evF u
  Assumptions (con x) = Lift 𝟙
  Assumptions (var x) = Lift 𝟙

module _
  {Var : Set}
  {F : Set}
  (𝔽 : Field-Ops F)
  where

  open Field-Ops 𝔽

  F-Op-eval : F-Op → F → F → F
  F-Op-eval [+] x y = x + y
  F-Op-eval [*] x y = x * y
  F-Op-eval [-] x y = x − y
  F-Op-eval [/] x y = x / y

  R-Op-eval : R-Op → F → F → F
  R-Op-eval o = F-Op-eval (R-include o)

  evalF : (ρ : Var → F) → Tm F F-Op Var → F
  evalR : (ρ : Var → F) → Tm F R-Op Var → F
  evalF = eval F-Op-eval
  evalR = eval R-Op-eval

  private
      TmF = Tm F F-Op Var
      TmR = Tm F R-Op Var

  infix 2 _/_:[_,_]
  record Div (evF : TmF → F)(evR : TmR → F)(t : TmF) : Set where
    constructor _/_:[_,_]
    field
      N : TmR
      D : TmR
      .non-zero-D : evR D ≢ 0#
      .is-correct : evF t ≡ evR N / evR D

  module _ (FS : Field.Field-Struct 𝔽)(ρ : Var → F) where
    open Field.Field-Struct FS

    private
      Div' = Div (evalF ρ) (evalR ρ)
      evF = evalF ρ

    NonZeroF : TmF → Set
    NonZeroF x = evF x ≢ 0#

    _+Div_ : ∀ {t u} → Div' t → Div' u → Div' (t :+ u)
    (N / D :[ nD , ok ]) +Div (N₁ / D₁ :[ nD₁ , ok₁ ])
       = N :* D₁ :+ N₁ :* D / D :* D₁
       :[ no-zero-divisor nD nD₁ , += ok ok₁ ∙ +-quotient nD nD₁ ]

    _*Div_ : ∀ {t u} → Div' t → Div' u → Div' (t :* u)
    (N / D :[ nD , ok ]) *Div (N₁ / D₁ :[ nD₁ , ok₁ ])
       = N :* N₁ / D :* D₁
       :[ no-zero-divisor nD nD₁ , *= ok ok₁ ∙ *-quotient nD nD₁ ]

    _−Div_ : ∀ {t u} → Div' t → Div' u → Div' (t :- u)
    (N / D :[ nD , ok ]) −Div (N₁ / D₁ :[ nD₁ , ok₁ ])
       = N :* D₁ :- N₁ :* D / D :* D₁
       :[ no-zero-divisor nD nD₁ , −= ok ok₁ ∙ −-quotient nD nD₁ ]

    _/Div_:[_] : ∀ {t u} → Div' t → Div' u → evF u ≢ 0# → Div' (t :/ u)
    (N / D :[ nD , ok ]) /Div (N₁ / D₁ :[ nD₁ , ok₁ ]) :[ u≢0 ]
      = (N :* D₁) / (D :* N₁)
      :[ no-zero-divisor nD nN₁ , /= ok ok₁ ∙ /-quotient nN₁ nD nD₁ ]
      where .nN₁ : evalR ρ N₁ ≢ 0#
            nN₁ p = u≢0 (ok₁ ∙ *= p idp ∙ 0*-zero)

    -- con-Div and var-Div are basically the same but not so convenient to unify
    con-Div : ∀ x → Div' (con x)
    var-Div : ∀ x → Div' (var x)

    con-Div x = con x / con 1# :[ 1≢0 , ! /1-id ]
    var-Div x = var x / con 1# :[ 1≢0 , ! /1-id ]

    to-ring : ∀ (t : TmF) → Assumptions NonZeroF t → Div' t
    to-ring (op [+] t u) (at , au)       = to-ring t at +Div to-ring u au
    to-ring (op [*] t u) (at , au)       = to-ring t at *Div to-ring u au
    to-ring (op [-] t u) (at , au)       = to-ring t at −Div to-ring u au
    to-ring (op [/] t u) (at , au , u≢0) = to-ring t at /Div to-ring u au :[ u≢0 ]
    to-ring (con x) _                    = con-Div x
    to-ring (var x) _                    = var-Div x

{-
    Eqn : Set _
    Eqn = TmF × TmF

    divR : ∀ {t} → Div' t → TmR
    divR (N / D :[ nD , ok ]) = {!!}

    to-ring' : ∀ (t : TmF) → Assumptions t → TmR
    to-ring' t a = {!!}
    -}

open import Relation.Binary
module _
  {F : Set}
  (𝔽 : Field.Field F)
  (_≟R_ : Decidable {A = F} _≡_)

  where
  open import Algebra using (RawRing)
  open import Algebra.RingSolver.AlmostCommutativeRing

  private
    module 𝔽 = Field.Field 𝔽

  open 𝔽
  R : AlmostCommutativeRing _ _
  R = record
        { Carrier = F
        ; _≈_ = _≡_
        ; _+_ = _+_
        ; _*_ = _*_
        ; -_ = 0−_
        ; 0# = 0#
        ; 1# = 1#
        ; isAlmostCommutativeRing =
          record
            { isCommutativeSemiring =
              record
              { +-isCommutativeMonoid =
                record
                { isSemigroup =
                  record
                  { isEquivalence = ≡.isEquivalence
                  ; assoc = λ _ _ _ → +-assoc
                  ; ∙-cong = += }
                ; identityˡ = λ _ → 0+-identity
                ; comm = λ _ _ → +-comm }
              ; *-isCommutativeMonoid =
                record
                { isSemigroup =
                  record
                  { isEquivalence = ≡.isEquivalence
                  ; assoc = λ _ _ _ → *-assoc
                  ; ∙-cong = *= }
                ; identityˡ = λ _ → 1*-identity
                ; comm = λ _ _ → *-comm }
              ; distribʳ = λ _ _ _ → *-+-distrʳ
              ; zeroˡ = λ _ → 0*-zero
              }
            ; -‿cong = 0−=
            ; -‿*-distribˡ = λ _ _ → ! 0−-*-distr
            ; -‿+-comm = λ _ _ → ! 0−-+-distr
            }
        }
  import Algebra.RingSolver
  import Algebra.RingSolver.Simple

{- I try first with the RingSolver.Simple, otherwise here is what we need

  Coeff : RawRing _
  Coeff = {!!}

  morphism : Coeff -Raw-AlmostCommutative⟶ R
  morphism = {!!}

  _coeff≟_ : Decidable (Induced-equivalence morphism)
  x coeff≟ y = {!!}

  module RS = Algebra.RingSolver Coeff R morphism _coeff≟_
-}

  module RS = Algebra.RingSolver.Simple R _≟R_

  import Relation.Binary.Reflection as Reflection
  open Reflection (≡.setoid F) RS.var RS.⟦_⟧ RS.⟦_⟧↓ RS.correct public
      using (prove; solve; solve₁) renaming (_⊜_ to _:=_)

  test-+-comm : ∀ m n → m + n ≡ n + m
  test-+-comm m n = solve₁ 2 (λ x y → x RS.:+ y := y RS.:+ x) m n refl

  ℕ▹P : ℕ → ∀ {n} → RS.Polynomial n
  ℕ▹P 0 = RS.con 0#
  ℕ▹P 1 = RS.con 1#
  ℕ▹P (1+ x) = RS.con 1# RS.:+ ℕ▹P x

  {-
  test-0−-inverse : ∀ m → m + 0− m ≡ 0#
  test-0−-inverse m = solve₁ 1 (λ x → x RS.:+ (RS.:- x) := RS.con 0#) m refl

  test-0−-involutive : ∀ m → 0− (0− m) ≡ m
  test-0−-involutive m = solve₁ 1 (λ x → RS.:- (RS.:- x) := x) m refl

  test-2* : ∀ n → 2# * n ≡ n + n
  test-2* n = solve₁ 1 (λ x → (ℕ▹P 2 RS.:* x) := (x RS.:+ x)) n refl
  -}

  open import Data.Vec
  open import Data.Fin using (Fin)

  poly : ∀ {n} → Tm F R-Op (Fin n) → RS.Polynomial n
  poly (op [+] t u) = poly t RS.:+ poly u
  poly (op [*] t u) = poly t RS.:* poly u
  poly (op [-] t u) = poly t RS.:- poly u
  poly (con x) = RS.con x
  poly (var x) = RS.var x

  {-
  FO = 𝔽.field-ops
  FS = 𝔽.field-struct

  Expr : ℕ → Set
  Expr n = Σ (Tm F F-Op (Fin n))
    -- this is probably wrong...
    (λ t → (ρ : Fin n → F) → Assumptions (NonZeroF FO FS ρ) t)

  Sem : Set
  Sem = F

  -- this takes only the numerator in account
  ⟦_⟧ : ∀ {n} → Expr n → Vec F n → Sem
  ⟦ t , a ⟧ ρ = RS.⟦ poly (Div.N (to-ring FO FS (flip lookup ρ) t (a (flip lookup ρ)))) ⟧ ρ

  -- this takes only the numerator in account
  ⟦_⟧↓ : ∀ {n} → Expr n → Vec F n → Sem
  ⟦ t , a ⟧↓ ρ = RS.⟦ poly (Div.N (to-ring FO FS (flip lookup ρ) t (a (flip lookup ρ)))) ⟧↓ ρ

  correct : ∀ {n} (e : Expr n) ρ → ⟦ e ⟧↓ ρ ≡ ⟦ e ⟧ ρ
  correct (op o t t₁ , a) ρ = {!!}
  correct (con x , a) ρ = {!idp!}
  correct (var x , a) ρ = {!!}

  open Reflection ≡.setoid var ⟦_⟧ ⟦_⟧↓ correct public
    using (prove; solve) renaming (_⊜_ to _:=_)

-- -}
-- -}
-- -}
-- -}
