open import Prelude
open import Generic.Multirec

module Multirec.Patch {n : ℕ}(φ : Fam n) where

  open Treefix φ

  -- CS : ∀{n} → List (Fin n) → List (Fin n) → Set
  -- CS l₁ l₂ = Σ (Fin (length l₁) → Fin (length l₂))
  --              (λ f → ∀ x → 

  data Patch : Fin n → Set where
    patch : ∀{ν}{pd pi : Path (I ν)}
          → (cd : Tx ν pd)
          → (ci : Tx ν pi)
          -- → (R  : CS (pathType pd) (pathType pi))
          → Patch ν
  
  -- Assuming one has a map that indicates where
  -- each subtree is duplicated in the source
  -- and destination element, we can generate a patch.
  module Compute 
    {ν : Fin n}
    (hmap : ∀{ι} → Fix φ ι → Maybe ( List (Path (I ν))
                                   × List (Path (I ν))))
      where

    {-# TERMINATING #-}
    extractD : ∀{ι} → Fix φ ι → List (Path (I ν))
    extractD {ι} ⟨ el ⟩ with hmap {ι} ⟨ el ⟩
    ...| just (l , _) = l
    ...| nothing with sop el
    ...| tag C p      
       = concat (All-fgt (All-map (λ {α} → extractDₐ {α}) p))
      where
        extractDₐ : ∀{α} → ⟦ α ⟧A (Fix φ) → List (Path (I ν))
        extractDₐ {K _} x = []
        extractDₐ {I ι} x = extractD x