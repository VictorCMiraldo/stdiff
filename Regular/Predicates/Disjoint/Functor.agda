open import Prelude
open import Generic.Regular

module Regular.Predicates.Disjoint.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (identityR : PatchRec → Set)
       (disjRec   : PatchRec → PatchRec → Set)
    where

  open import Regular.Internal.Functor Rec _≟Rec_
  open import Regular.Predicates.Identity.Functor Rec _≟Rec_ PatchRec identityR

  disjS  : {σ        : Sum}  → (s₁ s₂ : Patch PatchRec σ) → Set
  disjAl : {π₁ π₂ π₃ : Prod} → Al (At PatchRec) π₁ π₂ → Al (At PatchRec) π₁ π₃ → Set
  disjAt : {α        : Atom} → (a₁ a₂ : At PatchRec α)                   → Set

  disjAtAll : ∀{l₁ l₂} → All (At PatchRec) l₁ → Al (At PatchRec) l₁ l₂ → Set
  disjAtAll []       _  = Unit
  disjAtAll (a ∷ as) (Ains at al) = disjAtAll (a ∷ as) al
  disjAtAll (a ∷ as) (Adel at al) = identityAt a × disjAtAll as al
  disjAtAll (a ∷ as) (AX at al)   = disjAt a at × disjAtAll as al

  disjAts : ∀{l}(a₁ a₂ : All (At PatchRec) l) → Set
  disjAts []         []         = Unit
  disjAts (a₁ ∷ as₁) (a₂ ∷ as₂) = disjAt a₁ a₂ × disjAts as₁ as₂

  -- * When one spine is a copy, they are obviously disjoint.
  disjS Scp              s   = Unit
  disjS s                Scp = Unit

  -- * For two changes to be disj we need their
  --   constructors to be the same and the recursive
  --   children to be pairwise disjs.
  disjS {σ} (Scns C₁ at₁)    (Scns C₂ at₂) 
    = Σ (C₁ ≡ C₂) (λ { refl → disjAts at₁ at₂ })

  -- * A constructor change can be disj with a change,
  --   as long as they start at the same constructor and their 
  --   changes are disjAtAll
  disjS (Scns C₁ at₁)    (Schg C₂ C₃ al₂)
    = Σ (C₁ ≡ C₂) (λ { refl → disjAtAll at₁ al₂ })

  -- * Disj is obviously symmetric, so the definition here
  --   is the very same.
  disjS (Schg C₁ C₂ al₁) (Scns C₃ at₂)
    = Σ (C₁ ≡ C₃) (λ { refl → disjAtAll at₂ al₁ })

  -- * Two constructor changes are never disjoint.
  --   
  disjS (Schg C₁ C₂ al₁) (Schg C₃ C₄ al₂)
    = ⊥ 
 
  -- * Two alignments al₁ and al₂ are disjoint whenever
  --   they change a different part of the product in question.
  --
  --   Insertions are trivially disjoint, so we ignore them.
  disjAl A0            A0            = Unit
  disjAl (Ains _ al₁)  (Ains _ al₂)  = disjAl al₁ al₂
  disjAl (Ains _ al₁)  al₂           = disjAl al₁ al₂
  disjAl al₁           (Ains _ al₂)  = disjAl al₁ al₂
  
  -- * Since we ignore the contents of a deletion in the application
  --   function, we do not require that a₁ and a₂ are equal.
  disjAl (Adel a₁ al₁) (Adel a₂ al₂) = disjAl al₁ al₂

  -- * If we have a change and a deletion, however, the change
  --   must be an identity.
  disjAl (Adel a₁ al₁) (AX at₂ al₂)  = identityAt at₂ × disjAl al₁ al₂
  disjAl (AX at₁ al₁)  (Adel a₂ al₂) = identityAt at₁ × disjAl al₁ al₂
  disjAl (AX at₁ al₁)  (AX at₂ al₂)  = disjAt at₁ at₂ × disjAl al₁ al₂

  disjAt (set ks₁)  (set ks₂)  = identityK ks₁ ⊎ identityK ks₂
  disjAt (fix spμ₁) (fix spμ₂) = disjRec spμ₁ spμ₂


  module DisjSymmetry (disjRecSym : (r₁ r₂ : PatchRec) → disjRec r₁ r₂ → disjRec r₂ r₁) where

    disjS-sym : {σ : Sum}(s₁ s₂ : Patch PatchRec σ) → disjS s₁ s₂ → disjS s₂ s₁
    
    disjAl-sym : {π₁ π₂ π₃ : Prod}(a₁ : Al (At PatchRec) π₁ π₂)(a₂ : Al (At PatchRec) π₁ π₃)
               → disjAl a₁ a₂ → disjAl a₂ a₁

    disjAt-sym : {α : Atom}(a₁ a₂ : At PatchRec α) → disjAt a₁ a₂ → disjAt a₂ a₁

    disjAts-sym : ∀{l}(a₁ a₂ : All (At PatchRec) l) → disjAts a₁ a₂ → disjAts a₂ a₁
    disjAts-sym []         []         hip       = unit
    disjAts-sym (a₁ ∷ as₁) (a₂ ∷ as₂) (h0 , h1) = disjAt-sym a₁ a₂ h0 , disjAts-sym as₁ as₂ h1

    disjS-sym Scp  (Scns _ _)    hip   = unit
    disjS-sym Scp  (Schg _ _ _)  hip   = unit
    disjS-sym s                Scp hip = unit
    disjS-sym {σ} (Scns C₁ at₁)    (Scns C₂ at₂) (refl , h1)
      = refl , disjAts-sym at₁ at₂ h1
    disjS-sym (Scns C₁ at₁)    (Schg C₂ C₃ al₂) (refl , h1)
      = refl , h1
    disjS-sym (Schg C₁ C₂ al₁) (Scns C₃ at₂) (refl , h1) 
      = refl , h1
    disjS-sym (Schg C₁ C₂ al₁) (S.Schg C₃ C₄ al₂) ()
    
    disjAl-sym A0            A0            hip = unit
    disjAl-sym (Ains _ al₁)  A0 hip = disjAl-sym al₁ A0 hip
    disjAl-sym (Ains _ al₁)  (Adel a₂ al₂) hip = disjAl-sym al₁ (Adel a₂ al₂) hip
    disjAl-sym (Ains _ al₁)  (AX at₂ al₂) hip = disjAl-sym al₁ (AX at₂ al₂) hip
    disjAl-sym A0            (Ains _ al₂)  hip = disjAl-sym A0 al₂ hip
    disjAl-sym (Adel a₁ al₁) (Ains _ al₂)  hip = disjAl-sym (Adel a₁ al₁) al₂ hip
    disjAl-sym (AX at₁ al₁)  (Ains _ al₂)  hip = disjAl-sym (AX at₁ al₁) al₂ hip
    disjAl-sym (Ains a₁ al₁) (Ains a₂ al₂)  hip = disjAl-sym al₁ al₂ hip
    disjAl-sym (Adel a₁ al₁) (Adel a₂ al₂) hip = disjAl-sym al₁ al₂ hip
    disjAl-sym (Adel a₁ al₁) (AX at₂ al₂)  (h0 , h1) = h0 , disjAl-sym al₁ al₂ h1 
    disjAl-sym (AX at₁ al₁)  (Adel a₂ al₂) (h0 , h1) = h0 , disjAl-sym al₁ al₂ h1
    disjAl-sym (AX at₁ al₁)  (AX at₂ al₂)  (h0 , h1) = disjAt-sym at₁ at₂ h0 , disjAl-sym al₁ al₂ h1

    disjAt-sym (set ks₁)  (set ks₂)  (inj₁ hip) = inj₂ hip
    disjAt-sym (set ks₁)  (set ks₂)  (inj₂ hip) = inj₁ hip
    disjAt-sym (fix spμ₁) (fix spμ₂) hip = disjRecSym spμ₁ spμ₂ hip