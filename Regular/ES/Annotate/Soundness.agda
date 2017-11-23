open import Prelude
open import Generic.Regular
open import Generic.RegularAnn

module Regular.ES.Annotate.Soundness (μσ : Sum) where

  open import Regular.Functor (Fix μσ) _≟Fix_
    hiding (diffS ; diffAt)
  open import Regular.Fixpoint μσ
    hiding (diffAlμ)
  open import Regular.Operations.Inverse.Fixpoint μσ
  open import Regular.Operations.Inverse.Correctness.Fixpoint μσ

  open DecEq (Fix μσ) _≟Fix_
  open FixpointApplication

  open import Regular.ES.Annotate.Enum μσ
  open import Regular.ES.Annotate.FromPatch μσ

  -- * The soundness consists of making sure
  --   that if we use a patch to annotate two
  --   trees, we'll get that same patch back
  --   when diffing the two annotated trees. 
  
  {-# TERMINATING #-}
  sound : (x y : Fix μσ)(p : Alμ)(hip : ⟪ p ⟫μ x ≡ just y)
        → let x' , y' = annAlμ x y p hip
           in diffAlμ x' y' ≡ p


  sound-S : ∀{σ}(x y : ⟦ σ ⟧S (Fix μσ))(p : Patch Alμ σ)
          → (hip : ⟪ p ⟫S x ≡ just y)
          → let x' , y' = annS x y p hip
             in diffS x' y' ≡ p
  sound-S x y p hip 
    with annS-src x p (IsJust-from≡ hip)
       | annS-dst y p (IsJust-from≡ (invS-correct x y p hip))
  ...| x' | y' with fmapS 𝓤 x' ≟S fmapS 𝓤 y'
  ...| yes x'≡y' = {!!}
  ...| no  _ with sop x' | sop y'
  ...| tag C₁ p₁ | tag C₂ p₂ with C₁ ≟F C₂
  ...| yes refl = {!!}
  ...| no  ¬q   = {!!}

  sound ⟨ x ⟩ ⟨ y ⟩ (spn s) hip 
    = cong spn {!!}
  sound ⟨ x ⟩ ⟨ y ⟩ (ins C₁ δ) hip = {!!}
  sound ⟨ x ⟩ ⟨ y ⟩ (del C₁ δ) hip = {!!}
