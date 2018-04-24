open import Prelude
open import Generic.Regular

module Regular.Internal.Fixpoint (μσ : Sum) where

  open DecEq (Fix μσ) _≟Fix_
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  
  -- * We need monadic functionality for Maybe
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus renaming (_<=<_ to _∙_)

-- ** Universe

  data Alμ : Set where
    peel : PathD μσ → PathI μσ → Patch Alμ μσ → Alμ

  -- Is a recursive alignment maximal?
  isMaximalμ : Alμ → Set
  isMaximalμ (peel d i p) = d ≡ here ⊎ i ≡ here

  isMaximalμ? : (p : Alμ) → Dec (isMaximalμ p)
  isMaximalμ? (peel here here           p) = yes (inj₁ refl)
  isMaximalμ? (peel here (peel _ _ _ _) p) = yes (inj₁ refl)
  isMaximalμ? (peel (peel _ _ _ _) here p) = yes (inj₂ refl)
  isMaximalμ? (peel (peel _ _ _ _) (peel _ _ _ _) _)
    = no λ { (inj₁ ()) ; (inj₂ ()) }

-- ** Interpretation

  {-# TERMINATING #-}
  applyAlμ : Alμ → Fix μσ → Maybe (Fix μσ)
  applyAlμ (peel d i p) x = Path-inj i 
                       <$> (Path-match d x 
                       >>= ⟨⟩-Maybe-map (applyPatch applyAlμ p))

-- ** Cost semantics

  {-# TERMINATING #-}
  costAlμ : Alμ → ℕ
  costAlμ (peel d i p) = Path-depth d + Path-depth i + costPatch costAlμ p

-- ** Aliasses

  Patchμ : Set
  Patchμ = Alμ

  applyμ : Patchμ → Fix μσ → Maybe (Fix μσ)
  applyμ = applyAlμ

  costμ : Patchμ → ℕ
  costμ = costAlμ
