open import Data.Bits.Search
open import Data.Nat.NP

open import Function.NP

import Relation.Binary.PropositionalEquality.NP as ≡
open ≡

module Data.Bits.Sum where
    open SimpleSearch _+_ using (module Comm; module SearchInterchange; module SearchUnit; module Bij)
    open SimpleSearch _+_ public using () renaming (search to sum; search-≗ to sum-≗; searchBit to sumBit;
                                                    search-≗₂ to sum-≗₂;
                                                    search-+ to sum-+)
    open Comm ℕ°.+-comm public renaming (search-comm to sum-comm)
    open SearchUnit 0 refl public renaming
       (search-constε≡ε to sum-const0≡0)
    open SearchInterchange +-interchange public renaming (
        search-dist to sum-dist;
        search-searchBit to sum-sumBit;
        search-search to sum-sum;
        search-swap to sum-swap)
    open Bij ℕ°.+-comm +-interchange public renaming (search-bij to sum-bij)

    sum-const : ∀ n x → sum {n} (const x) ≡ ⟨2^ n * x ⟩
    sum-const zero    _ = refl
    sum-const (suc n) x = cong₂ _+_ (sum-const n x) (sum-const n x)
