open import Function
open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Fin using (Fin)
open import Data.Vec
open import Data.Vec.N-ary.NP
open import Relation.Binary.PropositionalEquality

module liftVec where
module single (A : Set)(_+_ : A → A → A)where

  data Tm : Set where
    var : Tm
    cst : A → Tm
    fun : Tm → Tm → Tm

  eval : Tm → A → A
  eval var x = x
  eval (cst c) x = c
  eval (fun tm tm') x = eval tm x + eval tm' x

  veval : {m : ℕ} → Tm → Vec A m → Vec A m
  veval var xs = xs
  veval (cst x) xs = replicate x
  veval (fun tm tm') xs = zipWith _+_ (veval tm xs) (veval tm' xs)

  record Fm : Set where
    constructor _=='_
    field
      lhs : Tm
      rhs : Tm

  s[_] : Fm → Set
  s[ lhs ==' rhs ] = (x : A) → eval lhs x ≡ eval rhs x

  v[_] : Fm → Set
  v[ lhs ==' rhs ] = {m : ℕ}(xs : Vec A m) → veval lhs xs ≡ veval rhs xs

  lemma1 : (t : Tm) → veval t [] ≡ []
  lemma1 var = refl
  lemma1 (cst x) = refl
  lemma1 (fun t t') rewrite lemma1 t | lemma1 t' = refl

  lemma2 : {m : ℕ}(x : A)(xs : Vec A m)(t : Tm) → veval t (x ∷ xs) ≡ eval t x ∷ veval t xs
  lemma2 _ _ var = refl
  lemma2 _ _ (cst c) = refl
  lemma2 x xs (fun t t') rewrite lemma2 x xs t | lemma2 x xs t' = refl

  prf : (t : Fm) → s[ t ] → v[ t ]
  prf (lhs ==' rhs) pr [] rewrite lemma1 lhs | lemma1 rhs = refl
  prf (l ==' r) pr (x ∷ xs) rewrite lemma2 x xs l | lemma2 x xs r = cong₂ (_∷_) (pr x) (prf (l ==' r) pr xs)

module MultiDataType {A : Set} {nrVar : ℕ} where
  data Tm : Set where
    var : Fin nrVar → Tm
    cst : A → Tm
    fun : Tm → Tm → Tm

  infixl 6 _+'_
  _+'_ : Tm → Tm → Tm
  _+'_ = fun

  infix 4 _≡'_
  record TmEq : Set where
    constructor _≡'_
    field
      lhs rhs : Tm

module multi (A : Set)(_+_ : A → A → A)(nrVar : ℕ) where
  open MultiDataType {A} {nrVar} public

  sEnv : Set
  sEnv = Vec A nrVar

  vEnv : ℕ → Set
  vEnv m = Vec (Vec A m) nrVar

  Var : Set
  Var = Fin nrVar

  _!_ : {X : Set} → Vec X nrVar → Var → X
  E ! v = lookup v E

  eval : Tm → sEnv → A
  eval (var x) G = G ! x
  eval (cst c) G = c
  eval (fun t t') G = eval t G + eval t' G

  veval : {m : ℕ} → Tm → vEnv m → Vec A m
  veval (var x) G = G ! x
  veval (cst c) G = replicate c
  veval (fun t t') G = zipWith _+_ (veval t G) (veval t' G)

  lemma1 : {xs : Vec (Vec A 0) nrVar} (t : Tm) → veval t xs ≡ []
  lemma1 {xs} (var x) with xs ! x
  ... | [] = refl
  lemma1 (cst x) = refl
  lemma1 {xs} (fun t t') rewrite lemma1 {xs} t | lemma1 {xs} t' = refl

  lemVar : {m n : ℕ}(G : Vec (Vec A (suc m)) n)(i : Fin n) → lookup i G ≡ lookup i (map head G) ∷ lookup i (map tail G)
  lemVar [] ()
  lemVar ((x ∷ G) ∷ G₁) Data.Fin.zero = refl
  lemVar (G ∷ G') (Data.Fin.suc i) = lemVar G' i

  lemma2 : {n : ℕ}(xs : vEnv (suc n))(t : Tm) → veval t xs ≡ eval t (map head xs) ∷ veval t (map tail xs)
  lemma2 G (var x) = lemVar G x
  lemma2 _ (cst x) = refl
  lemma2 G (fun t t') rewrite lemma2 G t | lemma2 G t' = refl

  s[_==_] : Tm → Tm → Set
  s[ l == r ] = (G : Vec A nrVar) → eval l G ≡ eval r G

  v[_==_] : Tm → Tm → Set
  v[ l == r ] = {m : ℕ}(G : Vec (Vec A m) nrVar) → veval l G ≡ veval r G

  prf : (l r : Tm) → s[ l == r ] → v[ l == r ]
  prf l r pr {zero} G rewrite lemma1 {G} l | lemma1 {G} r = refl
  prf l r pr {suc m} G rewrite lemma2 G l | lemma2 G r
     = cong₂ _∷_ (pr (replicate head ⊛ G)) (prf l r pr (map tail G))

module Full (A : Set)(_+_ : A → A → A) (m : ℕ) n where
  open multi A _+_ n public

  solve : ∀ (l r : Tm) → ∀ⁿ n (curryⁿ′ (λ G → eval l G ≡ eval r G))
         → ∀ⁿ n (curryⁿ′ (λ G → veval {m} l G ≡ veval r G))
  solve l r x = curryⁿ {n} {A = Vec A m} {B = curryⁿ′ f}
        (λ xs → subst id (sym (curry-$ⁿ′ f xs))
                   (prf l r (λ G → subst id (curry-$ⁿ′ g G) (x $ⁿ G)) xs))
    where f = λ G → veval {m} l G ≡ veval r G
          g = λ G → eval l G ≡ eval r G

  mkTm : N-ary n Tm TmEq → TmEq
  mkTm = go (tabulate id) where
    go : {m : ℕ} -> Vec (Fin n) m → N-ary m Tm TmEq → TmEq
    go [] f         = f
    go (x ∷ args) f = go args (f (var x))

  prove :  ∀ (t : N-ary n Tm TmEq) →
           let
             l = TmEq.lhs (mkTm t)
             r = TmEq.rhs (mkTm t)
           in ∀ⁿ n (curryⁿ′ (λ G → eval l G ≡ eval r G))
         → ∀ⁿ n (curryⁿ′ (λ G → veval {m} l G ≡ veval r G))
  prove t x = solve (TmEq.lhs (mkTm t)) (TmEq.rhs (mkTm t)) x

open import Data.Two

module example where

  open import Data.Fin
  open import Data.Product using (Σ ; proj₁)

  module VecBoolXorProps {m} = Full 𝟚 _xor_ m
  open MultiDataType

  coolTheorem : {m : ℕ} → (xs ys : Vec 𝟚 m) → zipWith _xor_ xs ys ≡ zipWith _xor_ ys xs
  coolTheorem = VecBoolXorProps.prove 2 (λ x y → x +' y ≡' y +' x) Xor°.+-comm

  coolTheorem2 : {m : ℕ} → (xs : Vec 𝟚 m) → _
  coolTheorem2 = VecBoolXorProps.prove 1 (λ x → (x +' x) ≡' (cst 0₂)) (proj₁ Xor°.-‿inverse)

test = example.coolTheorem (1₂ ∷ 0₂ ∷ []) (0₂ ∷ 0₂ ∷ [])
