open import Prelude
open import Generic.Regular

module Regular.Internal.Functor
           (Rec : Set)
           (_≟Rec_ : (x y : Rec) → Dec (x ≡ y))
       where

  open DecEq Rec _≟Rec_

  TrivialA : Atom → Set
  TrivialA α = ⟦ α ⟧A Rec × ⟦ α ⟧A Rec

  TrivialP : Rel Prod _
  TrivialP π₁ π₂ = ⟦ π₁ ⟧P Rec × ⟦ π₂ ⟧P Rec

-- ** Spine

  data S (At : Atom → Set)(Al : Rel Prod _)(σ : Sum) : Set where
    Scp : S At Al σ
    Scns : (C : Constr σ)
           (ats : All At (typeOf σ C)) →
           S At Al σ
    Schg : (C₁ C₂ : Constr σ){q : C₁ ≢ C₂}
           (al : Al (typeOf σ C₁) (typeOf σ C₂)) →
           S At Al σ

  S-map : {σ : Sum}
           {At₁ At₂ : Atom → Set}
           {Al₁ Al₂ : Rel Prod _}
        → (At₁ ⊆ At₂)
        → (∀{π₁ π₂} → Al₁ π₁ π₂ → Al₂ π₁ π₂)
        → S At₁ Al₁ σ → S At₂ Al₂ σ
  S-map f g Scp                 = Scp
  S-map f g (Scns C ps)         = Scns C (All-map f ps)
  S-map f g (Schg C₁ C₂ {q} al) = Schg C₁ C₂ {q} (g al)

-- *** Spine application

  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus

  All-head-map : {A : Set}{l k : A}{ls ks : List A}{P Q : A → Set}
               → (f : P l → Maybe (Q k))(fs : All P ls → Maybe (All Q ks))
               → All P (l ∷ ls) → Maybe (All Q (k ∷ ks))
  All-head-map f fs (x ∷ xs) = _∷_ <$> f x ⊛ fs xs
               
  applySP : {π : Prod}{At : Atom → Set}
          → (applyAt : ∀ {α} → At α → ⟦ α ⟧A Rec → Maybe (⟦ α ⟧A Rec))
          → All At π → ⟦ π ⟧P Rec → Maybe (⟦ π ⟧P Rec)
  applySP         applyAt [] [] = just []
  applySP {α ∷ π} applyAt (at ∷ ats) prod
    = All-head-map (applyAt at) (applySP applyAt ats) prod

  applyS : {σ : Sum}{At : Atom → Set}{Al : Rel Prod _}
        → (applyAt : ∀ {α} → At α → ⟦ α ⟧A Rec → Maybe (⟦ α ⟧A Rec))
        → (applyAl : ∀ {π₁ π₂} → Al π₁ π₂ → ⟦ π₁ ⟧P Rec → Maybe (⟦ π₂ ⟧P Rec)) 
        → S At Al σ → ⟦ σ ⟧S Rec → Maybe (⟦ σ ⟧S Rec)
  applyS applyAt applyAl Scp s = just s
  applyS applyAt applyAl (Schg C₁ C₂ p) s with sop s
  ... | tag C₃ p₃ with C₁ ≟F C₃
  ... | yes refl = Maybe-map (inj C₂) (applyAl p p₃)
  ... | no ¬p = nothing
  applyS {At = At} applyAt applyAl (Scns C₁ p₁) s with sop s
  ... | tag C₂ p₂ with C₁ ≟F C₂
  ... | no ¬p = nothing
  ... | yes refl = Maybe-map (inj C₁) (applySP applyAt p₁ p₂)

-- *** Spine cost

  costS : ∀ {σ At Al}
          (costAt : ∀{α} → At α → ℕ)
          (costAl : ∀ {π₁ π₂} → Al π₁ π₂ → ℕ) 
        → S At Al σ → ℕ
  costS costAt costAl Scp = 0
  costS {At = At} costAt costAl (Scns C p) = All-sum p
    where All-sum : ∀ {π} → All At π → ℕ
          All-sum {[]} [] = 0
          All-sum {α ∷ π} (a ∷ p) = costAt a + All-sum p
  costS costAt costAl (Schg C₁ C₂ p) = costAl p

-- ** Alignment

  data Al (At : Atom → Set) : Prod → Prod → Set where
    A0 : ∀{π₀ π₁}(del : ⟦ π₀ ⟧P Rec)(ins : ⟦ π₁ ⟧P Rec)
       → Al At π₀ π₁
    AX : ∀{π₀ π₁ π₀' π₁' α}(del : ⟦ π₀ ⟧P Rec)(ins : ⟦ π₁ ⟧P Rec)
       → At α → Al At π₀' π₁' → Al At (π₀ ++ α ∷ π₀') (π₁ ++ α ∷ π₁')

  al-map : ∀{π₁ π₂}
            {At₁ At₂ : Atom → Set}
          → (At₁ ⊆ At₂) 
          → Al At₁ π₁ π₂ → Al At₂ π₁ π₂
  al-map f (A0 d i)      = A0 d i
  al-map f (AX d i r rs) = AX d i (f r) (al-map f rs)

-- *** Alignment application

  applyAl : ∀{π₁ π₂ At} → 
           (applyAt : ∀ {α} → At α → ⟦ α ⟧A Rec → Maybe (⟦ α ⟧A Rec)) →
           Al At π₁ π₂ → ⟦ π₁ ⟧P Rec → Maybe (⟦ π₂ ⟧P Rec)
  applyAl at (A0 d i)      p = just i -- should we check that 'd ≡ p' ?
  applyAl at (AX d i r rs) p = ins i <$> (del d p >>= All-head-map (at r) (applyAl at rs))
    where
      del : ∀{π₀ π₁} → ⟦ π₀ ⟧P Rec → ⟦ π₀ ++ π₁ ⟧P Rec → Maybe (⟦ π₁ ⟧P Rec)
      del {[]}           p       ps  = just ps
      del {α₀ ∷ π₀} (_ ∷ p) (_ ∷ ps) = del p ps

      ins : ∀{π₀ π₁} → ⟦ π₀ ⟧P Rec → ⟦ π₁ ⟧P Rec → ⟦ π₀ ++ π₁ ⟧P Rec
      ins {[]}      []       qs = qs
      ins {α₀ ∷ π₀} (p ∷ ps) qs = p ∷ ins ps qs

  costAl : ∀{π₁ π₂ At} 
          → (costAt : ∀ {α} → At α → ℕ) 
          → Al At π₁ π₂ → ℕ
  costAl costAt (A0 d i)      = length (All-fgt (All-map (λ {α} _ → α) d)) 
                              + length (All-fgt (All-map (λ {α} _ → α) i))
  costAl costAt (AX d i r rs) = length (All-fgt (All-map (λ {α} _ → α) d))
                              + length (All-fgt (All-map (λ {α} _ → α) i))
                              + costAt r
                              + costAl costAt rs

{-
  Is an alignment maximal? We are only interested in maximal alignments!
  ie, an alignment is maximal if it has the maximum possible number of AX constructors

  isMaximal : ∀{π₁ π₂}{At : Atom → Set} → Alnf At π₁ π₂ → Set
  isMaximal (A0 {π₁} {π₂} d i)     = Disj π₁ π₂
  isMaximal (AX {π₁} {π₂} d i x p) = Disj π₁ π₂ × isMaximal p

  isMaximal? : ∀{π₁ π₂}{At : Atom → Set}(al : Alnf At π₁ π₂) → Dec (isMaximal al)
  isMaximal? (A0 {π₁} {π₂} d i)     = disj-dec _≟Atom_ π₁ π₂
  isMaximal? (AX {π₁} {π₂} d i x p) 
    with disj-dec _≟Atom_ π₁ π₂ | isMaximal? p
  ...| yes l  | yes m  = yes (l , m)
  ...| yes l  | no abs = no (abs ∘ proj₂)
  ...| no abs | _      = no (abs ∘ proj₁)
-}


-- ** Normal Form Alignments

{-
  alnf-ins : ∀{π₁ π₂ α}{At : Atom → Set} 
           → ⟦ α ⟧A Rec → Alnf At π₁ π₂ → Alnf At π₁ (α ∷ π₂)
  alnf-ins a (A0 d i)      = A0 d (a ∷ i) 
  alnf-ins a (AX d i x al) = AX d (a ∷ i) x al

  alnf-del : ∀{π₁ π₂ α}{At : Atom → Set} 
           → ⟦ α ⟧A Rec → Alnf At π₁ π₂ → Alnf At (α ∷ π₁) π₂
  alnf-del a (A0 d i)      = A0 (a ∷ d) i
  alnf-del a (AX d i x al) = AX (a ∷ d) i x al

  normalizeAl : ∀{π₁ π₂}{At : Atom → Set} → Al At π₁ π₂ → Alnf At π₁ π₂
  normalizeAl A0           = A0 [] []
  normalizeAl (Ains a' al) = alnf-ins a' (normalizeAl al)
  normalizeAl (Adel a' al) = alnf-del a' (normalizeAl al)
  normalizeAl (AX   at al) = AX [] [] at (normalizeAl al)
-}

-- ** Atoms

  data At (PatchRec : Set) : Atom → Set where
    set : ∀ {κ} → TrivialK κ → At PatchRec (K κ)
    fix : PatchRec → At PatchRec I

  applyAt : ∀{α PatchRec} 
          → (applyR : PatchRec → Rec → Maybe Rec) 
          → At PatchRec α → ⟦ α ⟧A Rec → Maybe (⟦ α ⟧A Rec)
  applyAt applyR (set k₁k₂) k = applyK k₁k₂ k
  applyAt applyR (fix spμ) x = applyR spμ x

  costAt : ∀{α PatchRec}
         → (costR : PatchRec → ℕ)
         → At PatchRec α → ℕ
  costAt costR (set k₁k₂) = costK k₁k₂
  costAt costR (fix spμ) = costR spμ

-- * Mixing Everything

  applySAlAt : ∀{PatchRec}{σ : Sum}(applyR : PatchRec → Rec → Maybe Rec) 
             → S (At PatchRec) (Al (At PatchRec)) σ
             → ⟦ σ ⟧S Rec
             → Maybe (⟦ σ ⟧S Rec)
  applySAlAt applyR = applyS (applyAt applyR) (applyAl (applyAt applyR))

-- * Some renamings

  Patch : Set → Sum → Set
  Patch PatchRec = S (At PatchRec) (Al (At PatchRec))
