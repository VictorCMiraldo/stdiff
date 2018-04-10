open import Prelude
open import Generic.Regular

module Regular.Relations.Applies.Soundness.Functor 
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (AppRec    : Rec → Rec → PatchRec → Set)
       (applyRec  : PatchRec → Rec → Maybe Rec)
       (AppRec-ok : (x y : Rec)(p : PatchRec)
                  → applyRec p x ≡ just y
                  → AppRec x y p)
    where

  open import Regular.Functor Rec _≟Rec_
  open DecEq Rec _≟Rec_
  open FunctorApplication PatchRec applyRec
  open import Regular.Relations.Applies.Functor
    Rec _≟Rec_ PatchRec AppRec

  AppAt-sound : ∀{α}(a₁ a₂ : ⟦ α ⟧A Rec)(p : At PatchRec α)
                → ⟪ p ⟫A a₁ ≡ just a₂
                → AppAt a₁ a₂ p
  AppAt-sound {K _} a₁ a₂ (set (k₁ , k₂)) hip
    with k₁ ≟K k₂ 
  ...| yes refl rewrite just-inj hip = AppSetId k₁ a₂
  ...| no  abs with k₁ ≟K a₁
  ...| no _ = Maybe-⊥-elim hip
  ...| yes refl rewrite just-inj hip 
    = AppSet k₁ a₂ (λ k₁≡a₂ → abs (trans k₁≡a₂ (sym (just-inj hip))))
  AppAt-sound {I}   a₁ a₂ (fix p) hip 
    = AppFix a₁ a₂ p (AppRec-ok a₁ a₂ p hip)

  AppAl-sound : ∀{π₁ π₂}(p₁ : ⟦ π₁ ⟧P Rec)(p₂ : ⟦ π₂ ⟧P Rec)
                → (al : Al (At PatchRec) π₁ π₂)
                → ⟪ al ⟫P p₁ ≡ just p₂
                → AppAl p₁ p₂ al
  AppAl-sound xs ys (A0 d .ys) refl = AppA0 xs d ys
  AppAl-sound xs ys (AX {α = α} d i a p) hip 
    with Prod-del d xs | inspect (Prod-del d) xs
  ...| x' ∷ xs' | [ XS ] with ⟪ a ⟫A x' | inspect ⟪ a ⟫A x' 
  ...| nothing  | _ = Maybe-⊥-elim hip
  ...| just r   | [ R ] with ⟪ p ⟫P xs' | inspect ⟪ p ⟫P xs'
  ...| nothing  | _ = Maybe-⊥-elim hip
  ...| just rs  | [ RS ] 
    with Prod-del-cat-inv d xs (x' ∷ xs') XS
  ...| d' , KS rewrite KS 
                     | just-inj (sym hip)
                     = AppAX d' d i a p (AppAt-sound x' r a R) 
                                        (AppAl-sound xs' rs p RS)

  AppSP-sound : ∀{π}(p₁ p₂ : ⟦ π ⟧P Rec)
                → (ps : All (At PatchRec) π)
                → ⟪ ps ⟫SP p₁ ≡ just p₂
                → All-zip3-set AppAt p₁ p₂ ps
  AppSP-sound [] [] [] hip = unit
  AppSP-sound (x ∷ xs) (y ∷ ys) (p ∷ ps) hip 
    with ⟪ p ⟫A x | inspect ⟪ p ⟫A x
  ...| nothing | _ = Maybe-⊥-elim hip
  ...| just x' | [ X ] 
    with ⟪ ps ⟫SP xs | inspect ⟪ ps ⟫SP xs
  ...| nothing  | _ = Maybe-⊥-elim hip
  ...| just xs' | [ XS ] 
     rewrite proj₁ (All-∷-inj (just-inj hip))
           | proj₂ (All-∷-inj (just-inj hip))
           = AppAt-sound x y p X 
           , AppSP-sound xs ys ps XS

  AppS-sound : ∀{σ}(s₁ s₂ : ⟦ σ ⟧S Rec)(p : Patch PatchRec σ)
             → ⟪ p ⟫S s₁ ≡ just s₂
             → AppS s₁ s₂ p
  AppS-sound x y Scp hip 
    rewrite just-inj hip = AppScp y
  AppS-sound x y (Scns C ats) hip 
    with sop x | sop y
  ...| tag Cx Px | tag Cy Py 
    with C ≟F Cx
  ...| no _     = Maybe-⊥-elim hip
  ...| yes refl 
    with ⟪ ats ⟫SP Px | inspect ⟪ ats ⟫SP Px
  ...| nothing  | _      = Maybe-⊥-elim hip
  ...| just Px' | [ PX ] with inj-inj (just-inj hip)
  ...| refl , refl 
     = AppScns Cx Px Py ats (AppSP-sound Px Py ats PX)
  AppS-sound x y (Schg C₁ C₂ {q} al) hip
    with sop x | sop y
  ...| tag Cx Px | tag Cy Py 
    with C₁ ≟F Cx
  ...| no _     = Maybe-⊥-elim hip
  ...| yes refl 
    with ⟪ al ⟫P Px | inspect ⟪ al ⟫P Px
  ...| nothing  | _      = Maybe-⊥-elim hip
  ...| just Px' | [ PX ] with inj-inj (just-inj hip)
  ...| refl , refl 
     = AppSchg Cx C₂ q Px Px' al 
               (AppAl-sound Px Px' al PX)
