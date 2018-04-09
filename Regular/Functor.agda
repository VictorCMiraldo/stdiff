open import Prelude
open import Generic.Regular

module Regular.Functor
           (Rec : Set)
           (_≟Rec_ : (x y : Rec) → Dec (x ≡ y))
       where
 
  open import Data.List using (monadPlus)

  open import Regular.Internal.Functor Rec _≟Rec_
    public

  {-
  VCM: TODO

  open import Regular.Internal.ExtEnum.Functor Rec _≟Rec_ List Data.List.monadPlus
    public
  -}  
  
  module FunctorApplication
         (PatchRec : Set)
         (applyR   : PatchRec → Rec → Maybe Rec)
      where

    ⟪_⟫A : {α : Atom} → At PatchRec α → ⟦ α ⟧A Rec → Maybe (⟦ α ⟧A Rec)
    ⟪ a ⟫A = applyAt applyR a

    ⟪_⟫P : {π₁ π₂ : Prod} → Al (At PatchRec) π₁ π₂ → ⟦ π₁ ⟧P Rec → Maybe (⟦ π₂ ⟧P Rec)
    ⟪ as ⟫P = applyAl ⟪_⟫A as

    ⟪_⟫SP : {π : Prod} → All (At PatchRec) π → ⟦ π ⟧P Rec → Maybe (⟦ π ⟧P Rec)
    ⟪ ats ⟫SP = applySP ⟪_⟫A ats

    ⟪_⟫S : {σ : Sum} → Patch PatchRec σ → ⟦ σ ⟧S Rec → Maybe (⟦ σ ⟧S Rec)
    ⟪ p ⟫S = applyS ⟪_⟫A ⟪_⟫P p

                
