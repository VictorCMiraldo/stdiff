open import Prelude
open import Generic.Regular

module Regular.Internal.ExtEnum.Functor
         (Rec : Set)(_≟Rec_ : ∀ (⟨x⟩ ⟨y⟩ : Rec) → Dec (⟨x⟩ ≡ ⟨y⟩))
         (M : Set → Set)(m : RawMonadPlus M)
       where

  open import Regular.Internal.Functor Rec _≟Rec_
  open DecEq Rec _≟Rec_

  open RawMonadPlus m

  All-mapM : ∀ {A}{P : A → Set} {Q : A → Set} →
           (∀{a} → P a → M (Q a)) → ∀{xs} → All P xs → M (All Q xs)
  All-mapM g []         = return []
  All-mapM g (px ∷ pxs) = _∷_ <$> g px ⊛ All-mapM g pxs


-- ** Spine identification

  spine : ∀ {σ} → ⟦ σ ⟧S Rec → ⟦ σ ⟧S Rec → S TrivialA TrivialP σ
  spine s₁ s₂ with s₁ ≟S s₂
  ... | yes refl = Scp
  ... | no ¬p  with sop s₁ | sop s₂
  ... | tag C₁ p₁ | tag C₂ p₂ with C₁ ≟F C₂
  ... | yes refl = Scns C₁ (zipd p₁ p₂)
  ... | no ¬q = Schg C₁ C₂ {¬q} (p₁ , p₂)
  
  _⊆M_ : (At₁ At₂ : Atom → Set) → Set
  At₁ ⊆M At₂ = At₁ ⊆ M ∘ At₂

  _⇒M_ : (Al₁ Al₂ : Rel Prod _) → Set
  Al₁ ⇒M Al₂ = ∀{π₁ π₂} → Al₁ π₁ π₂ → M (Al₂ π₁ π₂)

  S-mapM : {σ : Sum}
           {At₁ At₂ : Atom → Set}
           {Al₁ Al₂ : Rel Prod _}
        → (At₁ ⊆M At₂)
        → (Al₁ ⇒M Al₂)
        → S At₁ Al₁ σ → M (S At₂ Al₂ σ)
  S-mapM f g Scp = return Scp
  S-mapM f g (Scns C ps) = Scns C <$> All-mapM f ps
  S-mapM f g (Schg C₁ C₂ {q} al) = Schg C₁ C₂ {q} <$> g al

-- ** Enumerating alignments

  -- create only maximal alignments.
  -- keeps an acumulator of things to delete or insert.
  -- PRECONDITION: πd ∩ πi ≡ ∅
  -- 
  alignmax : ∀{πd πi π₁ π₂} 
           → ⟦ πd ⟧P Rec → ⟦ πi ⟧P Rec
           → ⟦ π₁ ⟧P Rec → ⟦ π₂ ⟧P Rec 
           → M (Al TrivialA  (reverse πd ++ π₁) (reverse πi ++ π₂))

  align : ∀{π₁ π₂} → ⟦ π₁ ⟧P Rec → ⟦ π₂ ⟧P Rec → M (Al TrivialA π₁ π₂)
  align ats₁ ats₂ = alignmax [] [] ats₁ ats₂

  guardDisj : {A : Set}(πd πi : Prod) → M A → M A
  guardDisj πd πi m
    with disj-dec _≟Atom_ πd πi
  ...| no  _ = ∅
  ...| yes _ = m

  private
    reverse-lemma : ∀{a}{A : Set a}(xs ys : List A)(x : A)
                  → reverse (x ∷ xs) ++ ys ≡ reverse xs ++ x ∷ ys
    reverse-lemma xs ys x 
      rewrite unfold-reverse x xs 
            | ++-assoc (reverse xs) (x ∷ []) ys
            = refl

  alignmax-ins : ∀{πd πi π₁ π₂ α}
               → ⟦ πd ⟧P Rec → ⟦ πi ⟧P Rec
               → ⟦ π₁ ⟧P Rec → ⟦ π₂ ⟧P Rec → ⟦ α ⟧A Rec 
               → M (Al TrivialA (reverse πd ++ π₁) (reverse πi ++ α ∷ π₂))
  alignmax-ins {πd} {πi} {π₁} {π₂} {α} cd ci ats₁ ats₂ at 
    rewrite sym (reverse-lemma πi π₂ α) 
          = guardDisj πd (α ∷ πi) 
                      (alignmax cd (at ∷ ci) ats₁ ats₂)  

  alignmax-del : ∀{πd πi π₁ π₂ α}
               → ⟦ πd ⟧P Rec → ⟦ πi ⟧P Rec
               → ⟦ π₁ ⟧P Rec → ⟦ π₂ ⟧P Rec → ⟦ α ⟧A Rec 
               → M (Al TrivialA (reverse πd ++ α ∷ π₁) (reverse πi ++ π₂))
  alignmax-del {πd} {πi} {π₁} {π₂} {α} cd ci ats₁ ats₂ at 
    rewrite sym (reverse-lemma πd π₁ α) 
          = guardDisj (α ∷ πd) πi
                      (alignmax (at ∷ cd) ci ats₁ ats₂)  

{-
  alignmax-cpy : ∀{πd πi π₁ π₂ α}
               → ⟦ πd ⟧P Rec → ⟦ πi ⟧P Rec
               → ⟦ π₁ ⟧P Rec → ⟦ π₂ ⟧P Rec 
               → ⟦ α  ⟧A Rec → ⟦ α  ⟧A Rec 
               → M (Al TrivialA (reverse πd ++ α ∷ π₁) (reverse πi ++ π₂))
  alignmax-cpy {πd} {πi} {π₁} {π₂} {α} cd ci ats₁ ats₂ at₁ at₂
    = ?
-}

  alignmax {πd} {πi} cd ci [] [] 
    rewrite ++-identityʳ (reverse πd)
          | ++-identityʳ (reverse πi)
          = return (A0 (All-rev cd) (All-rev ci))
  alignmax {πd} {πi} {α ∷ π₁} cd ci (at₁ ∷ ats₁) [] 
     = alignmax-del cd ci ats₁ [] at₁
  alignmax {πd} {πi} {_} {α ∷ π₂} cd ci [] (at₂ ∷ ats₂)
     = alignmax-ins cd ci [] ats₂ at₂
  alignmax {πd} {πi} {α₁ ∷ π₁} {α₂ ∷ π₂} cd ci (at₁ ∷ ats₁) (at₂ ∷ ats₂) 
    with α₁ ≟Atom α₂
  ...| yes refl = AX (All-rev cd) (All-rev ci) (at₁ , at₂) <$> alignmax [] [] ats₁ ats₂ 
                ∣ alignmax-del cd ci        ats₁  (at₂ ∷ ats₂) at₁ 
                ∣ alignmax-ins cd ci (at₁ ∷ ats₁)        ats₂  at₂
  ...| no _     = alignmax-del cd ci        ats₁  (at₂ ∷ ats₂) at₁ 
                ∣ alignmax-ins cd ci (at₁ ∷ ats₁)        ats₂  at₂

  al-mapM : ∀{π₁ π₂}
            {At₁ At₂ : Atom → Set}
          → (At₁ ⊆M At₂) 
          → Al At₁ π₁ π₂ → M (Al At₂ π₁ π₂)
  al-mapM f (A0 d i)     = return (A0 d i)
  al-mapM f (AX d i x p) = AX d i <$> f x ⊛ al-mapM f p

  diffAt : ∀ {α PatchRec} → (Rec → Rec → M PatchRec) → ⟦ α ⟧A Rec → ⟦ α ⟧A Rec → M (At PatchRec α)
  diffAt {K κ} diffR k₁ k₂ = return (set (k₁ , k₂))
  diffAt {I} diffR x y = fix <$> diffR x y

  diffS : ∀{PatchRec σ} → (Rec → Rec → M PatchRec)
         → ⟦ σ ⟧S Rec → ⟦ σ ⟧S Rec → M (S (At PatchRec) (Al (At PatchRec)) σ)
  diffS {PatchRec} diffR s₁ s₂ = S-mapM (uncurry (diffAt diffR)) (uncurry alignP) (spine s₁ s₂)
         where alignP : ∀ {π₁ π₂} → ⟦ π₁ ⟧P Rec → ⟦ π₂ ⟧P Rec → M (Al (At PatchRec) π₁ π₂)
               alignP p₁ p₂ = align p₁ p₂ >>= al-mapM (uncurry (diffAt diffR))
