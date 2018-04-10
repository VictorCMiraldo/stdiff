open import Prelude
open import Generic.Regular

module Regular.Relations.Disjoint.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (makeidR   : Rec → PatchRec)
       (identityR : PatchRec → Set)
       (disjRec   : PatchRec → PatchRec → Set)
    where

  open import Regular.Internal.Functor Rec _≟Rec_
  open import Regular.Relations.Identity.Functor Rec _≟Rec_ PatchRec makeidR identityR

  disjS  : {σ        : Sum}  → (s₁ s₂ : Patch PatchRec σ) → Set
 --  disjAl : {π₁ π₂ π₃ : Prod} → Al (At PatchRec) π₁ π₂ → Al (At PatchRec) π₁ π₃ → Set
  disjAt : {α        : Atom} → (a₁ a₂ : At PatchRec α)                   → Set

  disj-At-Al : ∀{l₁ l₂} → All (At PatchRec) l₁ → Al (At PatchRec) l₁ l₂ → Set
  disj-At-Al []       _  = Unit
  disj-At-Al (a ∷ as) (Ains at al) = disj-At-Al (a ∷ as) al
  disj-At-Al (a ∷ as) (Adel at al) = identityAt a × disj-At-Al as al
  disj-At-Al (a ∷ as) (AX at al)   = disjAt a at × disj-At-Al as al

  disj-At-Al-ins : {α : Atom}{π₁ π₂ : Prod}(ats : All (At PatchRec) π₁)(at : ⟦ α ⟧A Rec)
                 → (al : Al (At PatchRec) π₁ π₂)
                 → disj-At-Al ats (Ains {α = α} at al)
                 → disj-At-Al ats al
  disj-At-Al-ins [] at al hip = unit
  disj-At-Al-ins (a ∷ as) at al hip = hip

  disj-Al-At : ∀{l₁ l₂} → Al (At PatchRec) l₁ l₂ → All (At PatchRec) l₁ → Set
  disj-Al-At _            []       = Unit
  disj-Al-At (Ains at al) (a ∷ as) = disj-Al-At al (a ∷ as) 
  disj-Al-At (Adel at al) (a ∷ as) = identityAt a × disj-Al-At al as
  disj-Al-At (AX at al)   (a ∷ as) = disjAt at a  × disj-Al-At al as

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
  --   changes are disj-At-Al
  disjS (Scns C₁ at₁)    (Schg C₂ C₃ al₂)
    = Σ (C₁ ≡ C₂) (λ { refl → disj-At-Al at₁ al₂ })

  -- * Disj is obviously symmetric, so the definition here
  --   is the very same.
  disjS (Schg C₁ C₂ al₁) (Scns C₃ at₂)
    = Σ (C₁ ≡ C₃) (λ { refl → disj-Al-At al₁ at₂ })

  -- * Two constructor changes are never disjoint.
  --   
  disjS (Schg C₁ C₂ al₁) (Schg C₃ C₄ al₂)
    = ⊥ 
{- 
  -- * Two alignments al₁ and al₂ are disjoint whenever
  --   they change a different part of the product in question.
  --
  --   Insertions are trivially disjoint, so we ignore them.
  disjAl A0            A0            = Unit
  disjAl (Ains _ al₁)  (Ains _ al₂)  = ⊥
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
-}

  disjAt (set ks₁)  (set ks₂)  = identityK ks₁ ⊎ identityK ks₂
  disjAt (fix spμ₁) (fix spμ₂) = disjRec spμ₁ spμ₂


  module DisjSymmetry 
         (disjRecSym    : (r₁ r₂ : PatchRec) → disjRec r₁ r₂ → disjRec r₂ r₁) 
         (disjRecSymInv : (r₁ r₂ : PatchRec)(h : disjRec r₁ r₂)
                          → disjRecSym r₂ r₁ (disjRecSym r₁ r₂ h) ≡ h) 
      where

    disjS-sym : {σ : Sum}(s₁ s₂ : Patch PatchRec σ) → disjS s₁ s₂ → disjS s₂ s₁
    disjAt-sym : {α : Atom}(a₁ a₂ : At PatchRec α) → disjAt a₁ a₂ → disjAt a₂ a₁

    disjAts-sym : ∀{l}(a₁ a₂ : All (At PatchRec) l) → disjAts a₁ a₂ → disjAts a₂ a₁
    disjAts-sym []         []         hip       = unit
    disjAts-sym (a₁ ∷ as₁) (a₂ ∷ as₂) (h0 , h1) = disjAt-sym a₁ a₂ h0 , disjAts-sym as₁ as₂ h1

    disj-At-Al-sym : ∀{l₁ l₂}(ats : All (At PatchRec) l₁)(al : Al (At PatchRec) l₁ l₂)
                   → disj-At-Al ats al → disj-Al-At al ats
    disj-At-Al-sym []       _  unit      = unit
    disj-At-Al-sym (a ∷ as) (Ains at al) hip = disj-At-Al-sym (a ∷ as) al hip
    disj-At-Al-sym (a ∷ as) (Adel at al) (h0 , h1) = h0 , disj-At-Al-sym as al h1
    disj-At-Al-sym (a ∷ as) (AX at al)   (h0 , h1) = disjAt-sym a at h0 , disj-At-Al-sym as al h1

    disj-Al-At-sym : ∀{l₁ l₂}(al : Al (At PatchRec) l₁ l₂)(ats : All (At PatchRec) l₁)
                   → disj-Al-At al ats → disj-At-Al ats al
    disj-Al-At-sym _            [] unit      = unit
    disj-Al-At-sym (Ains at al) (a ∷ as) hip = disj-Al-At-sym al (a ∷ as) hip
    disj-Al-At-sym (Adel at al) (a ∷ as) (h0 , h1) = h0 , disj-Al-At-sym al as h1
    disj-Al-At-sym (AX at al) (a ∷ as)   (h0 , h1) = disjAt-sym at a h0 , disj-Al-At-sym al as h1

    disjS-sym Scp  (Scns _ _)    hip   = unit
    disjS-sym Scp  (Schg _ _ _)  hip   = unit
    disjS-sym s                Scp hip = unit
    disjS-sym {σ} (Scns C₁ at₁)    (Scns C₂ at₂) (refl , h1)
      = refl , disjAts-sym at₁ at₂ h1
    disjS-sym (Scns C₁ at₁)    (Schg C₂ C₃ al₂) (refl , h1)
      = refl , disj-At-Al-sym at₁ al₂ h1
    disjS-sym (Schg C₁ C₂ al₁) (Scns C₃ at₂) (refl , h1) 
      = refl , disj-Al-At-sym al₁ at₂ h1
    disjS-sym (Schg C₁ C₂ al₁) (S.Schg C₃ C₄ al₂) ()

    disjAt-sym (set ks₁)  (set ks₂)  (inj₁ hip) = inj₂ hip
    disjAt-sym (set ks₁)  (set ks₂)  (inj₂ hip) = inj₁ hip
    disjAt-sym (fix spμ₁) (fix spμ₂) hip = disjRecSym spμ₁ spμ₂ hip

    disjS-sym-inv : {σ : Sum}(s₁ s₂ : Patch PatchRec σ)
                    → (h : disjS s₁ s₂)
                    → disjS-sym s₂ s₁ (disjS-sym s₁ s₂ h) ≡ h
    
    disjAt-sym-inv : {α : Atom}(a₁ a₂ : At PatchRec α)(h : disjAt a₁ a₂)
                     → disjAt-sym a₂ a₁ (disjAt-sym a₁ a₂ h) ≡ h

    disj-Al-At-sym-inv : ∀{l₁ l₂}(al : Al (At PatchRec) l₁ l₂)(ats : All (At PatchRec) l₁)
                       → (hip : disj-Al-At al ats)
                       → disj-At-Al-sym ats al (disj-Al-At-sym al ats hip) ≡ hip
    disj-Al-At-sym-inv _            [] unit      = refl
    disj-Al-At-sym-inv (Ains at al) (a ∷ as) hip = disj-Al-At-sym-inv al (a ∷ as) hip
    disj-Al-At-sym-inv (Adel at al) (a ∷ as) (h0 , h1) 
      = cong₂ _,_ refl (disj-Al-At-sym-inv al as h1)
    disj-Al-At-sym-inv (AX at al) (a ∷ as)   (h0 , h1) 
      = cong₂ _,_ (disjAt-sym-inv at a h0) (disj-Al-At-sym-inv al as h1)

    disj-At-Al-sym-inv : ∀{l₁ l₂}(ats : All (At PatchRec) l₁)(al : Al (At PatchRec) l₁ l₂)
                       → (hip : disj-At-Al ats al)
                       → disj-Al-At-sym al ats (disj-At-Al-sym ats al hip) ≡ hip
    disj-At-Al-sym-inv [] _ unit      = refl
    disj-At-Al-sym-inv (a ∷ as) (Ains at al) hip = disj-At-Al-sym-inv (a ∷ as) al hip
    disj-At-Al-sym-inv (a ∷ as) (Adel t al) (h0 , h1) 
      = cong₂ _,_ refl (disj-At-Al-sym-inv as al h1)
    disj-At-Al-sym-inv (a ∷ as)  (AX at al) (h0 , h1) 
      = cong₂ _,_ (disjAt-sym-inv a at h0) (disj-At-Al-sym-inv as al h1)

    disjAts-sym-inv : ∀{l}(a₁ a₂ : All (At PatchRec) l)(h : disjAts a₁ a₂)
                      → disjAts-sym a₂ a₁ (disjAts-sym a₁ a₂ h) ≡ h
    disjAts-sym-inv []         []         unit      = refl
    disjAts-sym-inv (a₁ ∷ as₁) (a₂ ∷ as₂) (h0 , h1) = cong₂ _,_ (disjAt-sym-inv a₁ a₂ h0) 
                                                                  (disjAts-sym-inv as₁ as₂ h1)

    disjS-sym-inv Scp  (Scns _ _)    unit   = refl
    disjS-sym-inv Scp  (Schg _ _ _)  unit   = refl
    disjS-sym-inv Scp              Scp unit = refl
    disjS-sym-inv (Scns _ _)       Scp unit = refl
    disjS-sym-inv (Schg _ _ _)     Scp unit = refl
    disjS-sym-inv {σ} (Scns C₁ at₁)    (Scns C₂ at₂) (refl , h1)
      = cong (λ P → refl , P) (disjAts-sym-inv at₁ at₂ h1)
    disjS-sym-inv (Scns C₁ at₁)    (Schg C₂ C₃ al₂) (refl , h1)
      rewrite disj-At-Al-sym-inv at₁ al₂ h1
        = refl
    disjS-sym-inv (Schg C₁ C₂ al₁) (Scns C₃ at₂) (refl , h1) 
      rewrite disj-Al-At-sym-inv al₁ at₂ h1
        = refl
    disjS-sym-inv (Schg C₁ C₂ al₁) (S.Schg C₃ C₄ al₂) ()
    disjAt-sym-inv (set ks₁)  (set ks₂)  (inj₁ hip) = refl
    disjAt-sym-inv (set ks₁)  (set ks₂)  (inj₂ hip) = refl
    disjAt-sym-inv (fix spμ₁) (fix spμ₂) hip = disjRecSymInv spμ₁ spμ₂ hip
