open import Prelude
open import Generic.Regular

module Regular.Predicates.Applies.Correctness.Fixpoint (μσ : Sum) where

  open import Regular.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Applies.Fixpoint μσ

  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus 

  open FixpointApplication

  {-# TERMINATING #-}
  AppAlμ-correct : ∀{x y p}
                 → AppAlμ x y p
                 → ⟪ p ⟫μ x ≡ just y

  open import Regular.Predicates.Applies.Correctness.Functor
    (Fix μσ) _≟Fix_ Alμ AppAlμ ⟪_⟫μ AppAlμ-correct

  AppAlμ-correct (AppPeel d i {x} {y} p hip)
    rewrite Zipper-match-inj-lemma d ⟨ x ⟩ 
          = cong (λ P → Zipper-inj i <$> (⟨_⟩ <$> P)) (AppS-correct hip)
