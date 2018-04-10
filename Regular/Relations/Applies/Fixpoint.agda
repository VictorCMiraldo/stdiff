open import Prelude
open import Generic.Regular

module Regular.Relations.Applies.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_

  data AppAlμ : Fix μσ → Fix μσ → Alμ → Set

  open import Regular.Relations.Applies.Functor
    (Fix μσ) _≟Fix_ Alμ AppAlμ
    public

  data AppAlμ where
    -- Here, d and d' must be compatible zippers!
    -- that is: point to the SAME HOLE
    AppPeel : (d d' i : Path μσ){x y : ⟦ μσ ⟧S (Fix μσ)}
            → PathCompatible d' d
            → (p : Patch Alμ μσ)
            → AppS x  y  p
            → AppAlμ (Path-inj d ⟨ x ⟩) (Path-inj i ⟨ y ⟩) (peel d' i p)
