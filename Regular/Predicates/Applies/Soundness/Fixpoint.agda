open import Prelude
open import Generic.Regular

module Regular.Predicates.Applies.Soundness.Fixpoint (μσ : Sum) where

  open import Regular.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Applies.Fixpoint μσ

  -- * We need monadic functionality for Maybe
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus renaming (_<=<_ to _∙_)

  open FixpointApplication

  {-# TERMINATING #-}
  AppAlμ-sound : (x y : Fix μσ)(p : Alμ)
                 → ⟪ p ⟫μ x ≡ just y
                 → AppAlμ x y p

  open import Regular.Predicates.Applies.Soundness.Functor
    (Fix μσ) _≟Fix_ Alμ AppAlμ ⟪_⟫μ AppAlμ-sound
    public

  AppAlμ-sound x ⟨ y ⟩ (peel d i r) hip
    with Path-match d x | inspect (Path-match d) x
  ...| nothing     | _ = Maybe-⊥-elim hip
  ...| just ⟨ x' ⟩ | [ X ] 
    with ⟪ r ⟫S x' | inspect ⟪ r ⟫S x'
  ...| mk | [ RX ]
    with trans (cong (λ P → (Path-inj i <$> (Maybe-map ⟨_⟩ P))) (sym RX)) hip
  ...| hip' with mk
  ...| nothing = Maybe-⊥-elim hip'
  ...| just k  
    rewrite just-inj (sym hip')
    with Path-match-inj-inv d x ⟨ x' ⟩ X
  ...| d' , (prf , compat) 
    rewrite prf = AppPeel d' d i compat r (AppS-sound x' k r RX) 
