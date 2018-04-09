open import Prelude
open import Generic.Regular

module Regular.Predicates.Applies.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_

  data AppAlμ : Fix μσ → Fix μσ → Alμ → Set

  open import Regular.Predicates.Applies.Functor
    (Fix μσ) _≟Fix_ Alμ AppAlμ
    public

  data AppAlμ where
    AppPeel : (d i : Zipper μσ){x y : ⟦ μσ ⟧S (Fix μσ)}
            → (p : Patch Alμ μσ)
            → AppS x  y  p
            → AppAlμ (Zipper-inj d ⟨ x ⟩) (Zipper-inj i ⟨ y ⟩) (peel d i p)
