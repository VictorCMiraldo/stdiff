open import Prelude
open import Generic.Regular

module Regular.Relations.Applies.Correctness.Fixpoint (μσ : Sum) where

  open import Regular.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Relations.Applies.Fixpoint μσ

  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus 

  open FixpointApplication

  {-# TERMINATING #-}
  AppAlμ-correct : ∀{x y p}
                 → AppAlμ x y p
                 → ⟪ p ⟫μ x ≡ just y

  open import Regular.Relations.Applies.Correctness.Functor
    (Fix μσ) _≟Fix_ Alμ AppAlμ ⟪_⟫μ AppAlμ-correct

  AppAlμ-correct (AppPeel d i {x} {x'} prf p hip)
    with Path-match d ⟨ x ⟩ 
  ...| nothing = Maybe-⊥-elim prf
  ...| just ⟨ z ⟩ with ⟨⟩-inj (just-inj prf)
  ...| refl = cong (λ P → Path-inj i <$> (⟨_⟩ <$> P)) (AppS-correct hip)
