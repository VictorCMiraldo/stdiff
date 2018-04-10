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
    peel : (del ins : Path μσ) → Patch Alμ μσ → Alμ

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
