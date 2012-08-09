module Category.Applicative.NP where

open import Data.Vec using (Vec; []; _∷_)
open import Data.Nat
open import Category.Applicative public hiding (module RawApplicative)

module RawApplicative {f} {F : Set f → Set f}
                      (app : RawApplicative F) where
    open Category.Applicative.RawApplicative app public

    replicateM : ∀ {n A} → F A → F (Vec A n)
    replicateM {zero}  _ = pure []
    replicateM {suc n} x = pure _∷_ ⊛ x ⊛ replicateM x
