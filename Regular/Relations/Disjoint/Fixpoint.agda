open import Prelude
open import Generic.Regular

module Regular.Relations.Disjoint.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Relations.Identity.Fixpoint μσ
  open import Regular.Relations.Disjoint.Functor (Fix μσ) _≟Fix_ Alμ makeidAlμ identityAlμ
    renaming (module DisjSymmetry to DisjSymmetryF)
    public

  {-# TERMINATING #-}
  disjAlμ : Alμ → Alμ → Set
  disjCtx : ∀{π} → Ctx π → Ctx π → Set

  disjAtCtx : ∀{π} → All Atμ π → Ctx π → Set
  disjCtxAt : ∀{π} → Ctx π → All Atμ π → Set

  -- * Insertions are trivially disjoint from anything.
  disjAlμ (ins C₁ s₁) (ins C₂ s₂) = ⊥
  disjAlμ (ins C₁ s₁) (spn s₂)    = disjAlμ (getCtx s₁) (spn s₂)  
  disjAlμ (ins C₁ s₁) (del C₂ s₂) = disjAlμ (getCtx s₁) (del C₂ s₂)  
  disjAlμ (spn s₁)    (ins C₂ s₂) = disjAlμ (spn s₁)    (getCtx s₂)
  disjAlμ (del C₁ s₁) (ins C₂ s₂) = disjAlμ (del C₁ s₁) (getCtx s₂)

  -- * Two spines might be disjoint,
  disjAlμ (spn s₁) (spn s₂)       = disjS disjAlμ s₁ s₂

  -- * A deletion is disjoint from a copy
  disjAlμ (spn Scp) (del C₂ s₂)   = Unit

  -- * If the spine is a Scns and its recursive changes
  --   does NOT change the deleted context, they are still disjoint
  disjAlμ (spn (Scns C₁ at₁))  (del C₂ s₂)   
    = Σ (C₁ ≡ C₂) (λ { refl → disjAtCtx at₁ s₂ })

  -- * A Schg is never disjoint from a deletion.
  disjAlμ (spn (Schg _ _ _))  (del C₂ s₂)   
    = ⊥

  -- * Since disjointness is symmetric, here we just repeat the cases above.
  disjAlμ (del C₁ s₁) (spn Scp)   = Unit
  disjAlμ (del C₁ s₁) (spn (Scns C₂ at₂))   
    = Σ (C₁ ≡ C₂) (λ { refl → disjCtxAt s₁ at₂ })
  disjAlμ (del C₁ s₁) (spn (Schg _ _ _)) 
    = ⊥

  -- * Two deletions are never disjoint,
  --   since a patch is never disjoitn from itself.
  disjAlμ (del C₁ s₁) (del C₂ s₂) 
    = ⊥
  

  -- * disjCtx makes sure that the contexts are aligned and the patches
  --   within them are disjoint.
  disjCtx (here alμ₁ rest₁) (here alμ₂ rest₂) = disjAlμ alμ₁ alμ₂
  disjCtx (there a₁ ctx₁)   (there a₂ ctx₂)   = disjCtx ctx₁ ctx₂
  disjCtx _                 _                 = ⊥

  -- * disjAtCtx makes sure that the All At part of the Scns spine
  --   is all identities on the deleted part of the context and is
  --   disjoint in the field selected by the context.
  disjAtCtx [] ()
  disjAtCtx (fix a ∷ as) (here alμ rest) = disjAlμ a alμ × All-set identityAtμ as 
  disjAtCtx (a ∷ as)     (there a' ctx)  = identityAtμ a × disjAtCtx as ctx

  disjCtxAt () []
  disjCtxAt (here alμ rest) (fix a ∷ as) = disjAlμ alμ a × All-set identityAtμ as 
  disjCtxAt (there a' ctx)  (a ∷ as)     = identityAtμ a × disjCtxAt ctx as
  
  module DisjSymmetry where

    {-# TERMINATING #-}
    disjAlμ-sym : (alμ₁ alμ₂ : Alμ) → disjAlμ alμ₁ alμ₂ → disjAlμ alμ₂ alμ₁
 
    {-# TERMINATING #-}
    disjAlμ-sym-inv : (alμ₁ alμ₂ : Alμ)(hip : disjAlμ alμ₁ alμ₂)
                      → disjAlμ-sym alμ₂ alμ₁ (disjAlμ-sym alμ₁ alμ₂ hip) ≡ hip

    open DisjSymmetryF disjAlμ disjAlμ-sym disjAlμ-sym-inv public
   
    disjCtxAt-sym : ∀{π}(ctx : Ctx π)(atμs : All Atμ π)
                  → disjCtxAt ctx atμs → disjAtCtx atμs ctx
    disjCtxAt-sym () []
    disjCtxAt-sym (here alμ rest) (fix a ∷ as) (h0 , h1) 
      = disjAlμ-sym alμ a h0 , h1
    disjCtxAt-sym (there a' ctx)  (fix a ∷ as)     (h0 , h1)
      = h0 , disjCtxAt-sym ctx as h1 
    disjCtxAt-sym (there a' ctx)  (set a ∷ as)     (h0 , h1) 
      = h0 , disjCtxAt-sym ctx as h1
    
    disjAtCtx-sym : ∀{π}(atμs : All Atμ π)(ctx : Ctx π)
                  → disjAtCtx atμs ctx → disjCtxAt ctx atμs 
    disjAtCtx-sym [] () 
    disjAtCtx-sym (fix a ∷ as) (here alμ rest) (h0 , h1) 
      = disjAlμ-sym a alμ h0 , h1
    disjAtCtx-sym (fix a ∷ as) (there a' ctx) (h0 , h1) 
      = h0 , disjAtCtx-sym as ctx h1
    disjAtCtx-sym (set a ∷ as) (there a' ctx) (h0 , h1)
      = h0 , disjAtCtx-sym as ctx h1

    
    disjAlμ-sym (ins C₁ s₁) (ins C₂ s₂) ()
    disjAlμ-sym (ins C₁ s₁) (del C₂ s₂) hip                 = disjAlμ-sym (getCtx s₁) (del C₂ s₂) hip
    disjAlμ-sym (ins C₁ s₁) (spn s₂) hip                    = disjAlμ-sym (getCtx s₁) (spn s₂) hip
    disjAlμ-sym (del C₁ s₁) (ins C₂ s₂) hip                 = disjAlμ-sym (del C₁ s₁) (getCtx s₂) hip
    disjAlμ-sym (spn s₁)    (ins C₂ s₂) hip                 = disjAlμ-sym (spn s₁) (getCtx s₂) hip
    disjAlμ-sym (spn s₁) (spn s₂) hip                       = disjS-sym s₁ s₂ hip
    disjAlμ-sym (spn Scp) (del C₂ s₂) hip                   = unit
    disjAlμ-sym (spn (Scns C₁ at₁)) (del C₂ s₂) (refl , h1) = refl , disjAtCtx-sym at₁ s₂ h1 
    disjAlμ-sym (spn (Schg _ _ _)) (del C₂ s₂)    ()
    disjAlμ-sym (del C₁ s₁) (spn Scp) hip                   = unit
    disjAlμ-sym (del C₁ s₁) (spn (Scns C₂ at₂)) (refl , h1) = refl , disjCtxAt-sym s₁ at₂ h1
    disjAlμ-sym (del C₁ s₁) (spn (Schg _ _ _))  ()
    disjAlμ-sym (del C₁ s₁) (del C₂ s₂)  ()

    disjCtxAt-sym-inv : ∀{π}(ctx : Ctx π)(atμs : All Atμ π)
                      → (hip : disjAtCtx atμs ctx) 
                      → disjCtxAt-sym ctx atμs (disjAtCtx-sym atμs ctx hip) ≡ hip
    disjCtxAt-sym-inv () []
    disjCtxAt-sym-inv (here alμ rest) (fix a ∷ as) (h0 , h1)
      = cong (λ P → P , h1) (disjAlμ-sym-inv a alμ h0)
    disjCtxAt-sym-inv (there a' ctx) (fix a ∷ as) (h0 , h1)
      = cong (λ P → h0 , P) (disjCtxAt-sym-inv ctx as h1)
    disjCtxAt-sym-inv (there a' ctx) (set a ∷ as) (h0 , h1)
      = cong (λ P → h0 , P) (disjCtxAt-sym-inv ctx as h1)

    disjAtCtx-sym-inv : ∀{π}(atμs : All Atμ π)(ctx : Ctx π)
                     → (hip : disjCtxAt ctx atμs)
                     → disjAtCtx-sym atμs ctx (disjCtxAt-sym ctx atμs hip) ≡ hip
    disjAtCtx-sym-inv [] ()
    disjAtCtx-sym-inv (fix a ∷ as) (here alμ rest) (h0 , h1)
      = cong (λ P → P , h1) (disjAlμ-sym-inv alμ a h0)
    disjAtCtx-sym-inv (fix a ∷ as) (there a' ctx) (h0 , h1)
      = cong (λ P → h0 , P) (disjAtCtx-sym-inv as ctx h1)
    disjAtCtx-sym-inv (set a ∷ as) (there a' ctx) (h0 , h1)
      = cong (λ P → h0 , P) (disjAtCtx-sym-inv as ctx h1)

    disjAlμ-sym-inv (ins C₁ s₁) (ins C₂ s₂) ()
    disjAlμ-sym-inv (ins C₁ s₁) (del C₂ s₂) hip                 = disjAlμ-sym-inv (getCtx s₁) (del C₂ s₂) hip
    disjAlμ-sym-inv (ins C₁ s₁) (spn s₂) hip                    = disjAlμ-sym-inv (getCtx s₁) (spn s₂) hip
    disjAlμ-sym-inv (del C₁ s₁) (ins C₂ s₂) hip                 = disjAlμ-sym-inv (del C₁ s₁) (getCtx s₂) hip
    disjAlμ-sym-inv (spn s₁)    (ins C₂ s₂) hip                 = disjAlμ-sym-inv (spn s₁) (getCtx s₂) hip
    disjAlμ-sym-inv (spn s₁) (spn s₂) hip                       = disjS-sym-inv s₁ s₂ hip
    disjAlμ-sym-inv (spn Scp) (del C₂ s₂) unit                  = refl
    disjAlμ-sym-inv (spn (Scns C₁ at₁)) (del C₂ s₂) (refl , h1) 
      = cong (λ P → refl , P) (disjCtxAt-sym-inv s₂ at₁ h1)
    disjAlμ-sym-inv (spn (Schg _ _ _)) (del C₂ s₂)    ()
    disjAlμ-sym-inv (del C₁ s₁) (spn Scp) unit                  = refl
    disjAlμ-sym-inv (del C₁ s₁) (spn (Scns C₂ at₂)) (refl , h1) 
      = cong (λ P → refl , P) (disjAtCtx-sym-inv at₂ s₁ h1)
    disjAlμ-sym-inv (del C₁ s₁) (spn (Schg _ _ _))  ()
    disjAlμ-sym-inv (del C₁ s₁) (del C₂ s₂)  ()
