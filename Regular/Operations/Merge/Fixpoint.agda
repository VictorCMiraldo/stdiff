open import Prelude
open import Generic.Regular

module Regular.Operations.Merge.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Identity.Fixpoint μσ
  open import Regular.Predicates.Disjoint.Fixpoint μσ


  {-# TERMINATING #-}
  mergeAlμ : (alμ₁ alμ₂ : Alμ)(hip : disjAlμ alμ₁ alμ₂) → Alμ

  open import Regular.Operations.Merge.Functor (Fix μσ) _≟Fix_ Alμ makeidAlμ identityAlμ disjAlμ mergeAlμ
    public

  open DisjSymmetry


  mergeAtCtx : ∀{π}(atμs : All Atμ π)(ctx : Ctx π)(hip : disjAtCtx atμs ctx) 
             → Ctx π

  mergeCtxAt : ∀{π}(ctx : Ctx π)(atμs : All Atμ π)(hip : disjCtxAt ctx atμs) 
             → Alμ

  mergeCtxAlμ : ∀{π}(ctx : Ctx π)(alμ : Alμ)(hip : disjAlμ (getCtx ctx) alμ) 
              → All Atμ π
  mergeCtxAlμ (here alμ' rest) alμ hip 
    = fix (mergeAlμ alμ' alμ hip) ∷ All-map makeidAtμ rest 
  mergeCtxAlμ (there a   ctx) alμ hip 
    = makeidAtμ a ∷ mergeCtxAlμ ctx alμ hip


  mergeAlμCtx : ∀{π}(alμ : Alμ)(ctx : Ctx π)(hip : disjAlμ alμ (getCtx ctx)) → Ctx π
  mergeAlμCtx alμ (here alμ' rest) hip = here (mergeAlμ alμ alμ' hip) rest
  mergeAlμCtx alμ (there a   ctx)  hip = there a (mergeAlμCtx alμ ctx hip)

  mergeAlμ (ins C₁ s₁) (ins C₂ s₂) ()
  mergeAlμ (ins C₁ s₁) (spn s₂)    hip 
    = spn (Scns C₁ (mergeCtxAlμ s₁ (spn s₂) hip))
  mergeAlμ (ins C₁ s₁) (del C₂ s₂) hip 
    = spn (Scns C₁ (mergeCtxAlμ s₁ (del C₂ s₂) hip))
  mergeAlμ (spn s₁)   (ins C₂ s₂)  hip 
    = ins C₂ (mergeAlμCtx (spn s₁) s₂ hip)
  mergeAlμ (del C s₁) (ins C₂ s₂)  hip 
    = ins C₂ (mergeAlμCtx (del C s₁) s₂ hip)

  mergeAlμ (spn s₁) (spn s₂)       hip = spn (mergeS s₁ s₂ hip)

  mergeAlμ (spn Scp) (del C₂ s₂)   hip = del C₂ s₂ 

  mergeAlμ (spn (Scns C₁ at₁))  (del C₂ s₂) (refl , hip) 
    = del C₁ (mergeAtCtx at₁ s₂ hip)

  mergeAlμ (spn (Schg _ _ _)) (del C₂ s₂) ()

  mergeAlμ (del C₁ s₁) (spn Scp)   hip 
    = spn Scp
  mergeAlμ (del C₁ s₁) (spn (Scns C₂ at₂)) (refl , hip)
    = mergeCtxAt s₁ at₂ hip
  mergeAlμ (del C₁ s₁) (spn (Schg _ _ _)) ()

  mergeAlμ (del C₁ s₁) (del C₂ s₂) ()

  mergeAtCtx [] ()
  mergeAtCtx (fix a ∷ as) (here alμ rest) (ha , hip) 
    = here (mergeAlμ a alμ ha) rest
  mergeAtCtx {p ∷ ps} (fix a ∷ as) (there a' ctx) hip
    = there a' (mergeAtCtx as ctx (proj₂ hip))
  mergeAtCtx {p ∷ ps} (set a ∷ as) (there a' ctx) hip
    = there a' (mergeAtCtx as ctx (proj₂ hip))

  mergeCtxAt () [] 
  mergeCtxAt (here alμ rest) (fix a ∷ as) (ha , hip) 
    = mergeAlμ alμ a ha
  mergeCtxAt {p ∷ ps} (there a' ctx) (fix a ∷ as) hip
    = mergeCtxAt ctx as (proj₂ hip)
  mergeCtxAt {p ∷ ps} (there a' ctx) (set a ∷ as) hip
    = mergeCtxAt ctx as (proj₂ hip)

