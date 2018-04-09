open import Prelude
open import Generic.Regular

module Regular.Predicates.Applies.Correctness.Functor 
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (AppRec    : Rec → Rec → PatchRec → Set)
       (applyRec  : PatchRec → Rec → Maybe Rec)
       (AppRec-ok : {x y : Rec}{p : PatchRec}
                  → AppRec x y p
                  → applyRec p x ≡ just y)
    where

  open import Regular.Functor Rec _≟Rec_
  open FunctorApplication PatchRec applyRec
  open import Regular.Predicates.Applies.Functor
    Rec _≟Rec_ PatchRec AppRec

  AppAt-correct : ∀{α}{a₁ a₂ : ⟦ α ⟧A Rec}{p : At PatchRec α}
                → AppAt a₁ a₂ p
                → ⟪ p ⟫A a₁ ≡ just a₂
  AppAt-correct (AppSet k₁ k₂ q)
    with k₁ ≟K k₂
  ...| yes abs = ⊥-elim (q abs)
  ...| no  _ rewrite dec-refl _≟K_ k₁ = refl
  AppAt-correct (AppSetId k a) 
    rewrite dec-refl _≟K_ k = refl
  AppAt-correct (AppFix r₁ r₂ p x) 
    = AppRec-ok x

  AppAl-correct : ∀{π₁ π₂}{p₁ : ⟦ π₁ ⟧P Rec}{p₂ : ⟦ π₂ ⟧P Rec}
                → {al : Al (At PatchRec) π₁ π₂}
                → AppAl p₁ p₂ al
                → ⟪ al ⟫P p₁ ≡ just p₂
  AppAl-correct (AppA0 d d' i) 
    = refl
  AppAl-correct (AppAX {α} d d' i r rs {x} {x'} {xs} {xs'} hipR hipRS)
    rewrite Prod-del-cat-lemma d' d (_∷_ {x = α} x xs)
          | AppAt-correct hipR 
          | AppAl-correct hipRS
          = refl

  AppSP-correct : ∀{π}{p₁ p₂ : ⟦ π ⟧P Rec}
                → {ps : All (At PatchRec) π}
                → All-zip3-set AppAt p₁ p₂ ps
                → ⟪ ps ⟫SP p₁ ≡ just p₂
  AppSP-correct {_} {[]} {[]} {[]} hip = refl
  AppSP-correct {_} {x ∷ xs} {y ∷ ys} {p ∷ ps} (h , hip) 
    rewrite AppAt-correct h
          | AppSP-correct hip
          = refl
  
  AppS-correct : ∀{σ}{s₁ s₂ : ⟦ σ ⟧S Rec}{p : Patch PatchRec σ}
               → AppS s₁ s₂ p
               → ⟪ p ⟫S s₁ ≡ just s₂
  AppS-correct (AppScp x) = refl
  AppS-correct (AppScns {σ} C Pxs Pys pxy hip) 
    rewrite sop-inj-lemma {σ} C Pxs 
          | dec-refl _≟F_ C
          | AppSP-correct hip 
          = refl
  AppS-correct (AppSchg {σ} C₁ C₂ q Pxs Pys al hip) 
    rewrite sop-inj-lemma {σ} C₁ Pxs
          | dec-refl _≟F_ C₁
          | AppAl-correct hip
          = refl
