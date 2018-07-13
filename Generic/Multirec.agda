module Generic.Multirec where

open import Prelude
open import Generic.Opaque
  public

-- * We need monadic functionality for Maybe
open import Data.Maybe using (monadPlus)
open RawMonadPlus {lz} monadPlus renaming (_<=<_ to _∙_)

-- * Sum-of-product universe
-- ** Code

data Atom (n : ℕ) : Set where
  K : (κ : Konst) → Atom n 
  I : (ν : Fin n) → Atom n

Prod : ℕ → Set
Prod = List ∘ Atom

Sum : ℕ → Set
Sum = List ∘ Prod

-- ** Interpretation

Setⁿ : ℕ → Set₁
Setⁿ n = Fin n → Set

⟦_⟧A : {n : ℕ} → Atom n → Setⁿ n → Set
⟦ K κ ⟧A X = ⟦ κ ⟧K
⟦ I ν ⟧A X = X ν 

⟦_⟧P : {n : ℕ} → Prod n → Setⁿ n → Set
⟦ π ⟧P X = All (λ α → ⟦ α ⟧A X) π

⟦_⟧S : {n : ℕ} → Sum n → Setⁿ n → Set
⟦ σ ⟧S X = Any (λ π → ⟦ π ⟧P X) σ

-- ** Decidable equality

module DecEq {n : ℕ}(Rec : Setⁿ n)(_≟Rec_ : ∀{v}(x y : Rec v) → Dec (x ≡ y)) where

  _≟Atom_ : (α₁ α₂ : Atom n) → Dec (α₁ ≡ α₂)
  I i    ≟Atom I j with i ≟F j
  ...| yes refl = yes refl
  ...| no  ¬p   = no λ { refl → ¬p refl }   
  (K κ₁) ≟Atom (K κ₂) with κ₁ ≟Konst κ₂
  ...| yes refl = yes refl
  ...| no  ¬p  = no λ { refl → ¬p refl }
  I _ ≟Atom (K _) = no λ ()
  (K _) ≟Atom I _ = no λ ()

  _≟A_ :  ∀ {α} → (a₁ a₂ : ⟦ α ⟧A Rec) → Dec (a₁ ≡ a₂)
  _≟A_ {K κ} k₁ k₂ = k₁ ≟K k₂
  _≟A_ {I i} x  y  = x ≟Rec y

  _≟P_ : ∀ {π} → (p₁ p₂ : ⟦ π ⟧P Rec) → Dec (p₁ ≡ p₂)
  _≟P_ {[]} [] [] = yes refl
  _≟P_ {α ∷ π} (a₁ ∷ p₁) (a₂ ∷ p₂) with _≟A_ {α} a₁ a₂
  ... | no ¬p = no (λ { refl → ¬p refl })
  ... | yes refl with p₁ ≟P p₂
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }

  _≟S_ : ∀ {σ} → (s₁ s₂ : ⟦ σ ⟧S Rec) → Dec (s₁ ≡ s₂)
  _≟S_ {[]} () _
  _≟S_ {π ∷ σ} (here p₁) (here p₂) with p₁ ≟P p₂
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  _≟S_ {π ∷ σ} (here p₁) (there s₂) = no λ ()
  _≟S_ {π ∷ σ} (there s₁) (here s₂) = no λ ()
  _≟S_ {π ∷ σ} (there s₁) (there s₂) with s₁ ≟S s₂
  ... | yes refl = yes refl
  ... | no ¬p = no (λ { refl → ¬p refl })

-- ** Sum-of-product view

Constr : {n : ℕ} → Sum n → Set
Constr σ = Fin (length σ)


typeOf : {n : ℕ}(σ : Sum n) → Constr σ → Prod n
typeOf [] ()
typeOf (π ∷ σ) zero = π
typeOf (π ∷ σ) (suc C) = typeOf σ C

inj : {n : ℕ}{σ : Sum n}{X : Setⁿ n} → (C : Constr σ) → ⟦ typeOf σ C ⟧P X → ⟦ σ ⟧S X
inj {σ = []} () _
inj {σ = π ∷ σ} zero p = here p
inj {σ = x ∷ σ} (suc C) p = there (inj C p)

data SOP {n : ℕ}{σ : Sum n}{X : Setⁿ n} : ⟦ σ ⟧S X → Set where
  tag : (C : Constr σ)(p : ⟦ typeOf σ C ⟧P X) → SOP (inj C p)

sop : {n : ℕ}{σ : Sum n}{X : Setⁿ n} → (s : ⟦ σ ⟧S X) → SOP s
sop (here p) = tag zero p
sop (there s) with sop s
... | tag C p = tag (suc C) p

match : {n : ℕ}{σ : Sum n}{X : Setⁿ n}(C : Constr σ)
      → ⟦ σ ⟧S X → Maybe (⟦ typeOf σ C ⟧P X)
match C x with sop x
... | tag C₂ p with C ≟F C₂
... | yes refl = just p
... | no  _    = nothing

-- * Fixpoint

Fam : ℕ → Set
Fam n = Vec (Sum n) n

⟦_⟧F : {n : ℕ} → Fam n → Fin n → Sum n
⟦ φ ⟧F ν = Vec-lookup ν φ 

-- * Easier to type Constr and typeOf

Constr' : {n : ℕ} → Fam n → Fin n → Set
Constr' φ ν = Constr (⟦ φ ⟧F ν)

typeOf' : {n : ℕ}(φ : Fam n)(ν : Fin n) → Constr' φ ν → Prod n
typeOf' φ ν C = typeOf (⟦ φ ⟧F ν) C

data Fix {n : ℕ}(φ : Fam n) : Fin n → Set where
  ⟨_⟩ : ∀{ν} → ⟦ ⟦ φ ⟧F ν ⟧S (Fix φ) → Fix φ ν

unfix : ∀{n ν}{φ : Fam n} → Fix φ ν → ⟦ ⟦ φ ⟧F ν ⟧S (Fix φ)
unfix ⟨ x ⟩ = x

{-# TERMINATING #-}
_≟Fix_ : ∀{n i}{φ : Fam n} → (x y : Fix φ i) → Dec (x ≡ y)
_≟Fix_ {φ = φ} ⟨ sx ⟩ ⟨ sy ⟩ with DecEq._≟S_ (Fix φ) _≟Fix_ sx sy
... | yes refl = yes refl
... | no ¬p = no (λ { refl → ¬p refl })

-- * Paths over a Mutually Recursive Value

module Treefix {n : ℕ}(φ : Fam n) where

  open DecEq (Fix φ) _≟Fix_

  data Path : Atom n → Set where
    End  : ∀{κ} → Path (K κ)
    Hole : ∀{i} → Path (I i)
    Fork : ∀{i} 
         → (C : Constr' φ i)
         -- Ideally, we want a subset of (typeOf' φ i C)
         -- instead of 'All'; this would be harder to work with.
         -- Hence, we add the 'End' constructor.
         → All Path (typeOf' φ i C)
         → Path (I i)

  {-# TERMINATING #-}
  pathType : ∀{α} → Path α → List (Fin n)
  pathType End         = []
  pathType (Hole {i})  = i ∷ []
  pathType (Fork _ ps) = concat (All-fgt (All-map pathType ps))
    
  data TxNP : (p : Prod n) → All Path p → Set

  data Tx : (i : Fin n) → Path (I i) → Set where
    hole : ∀{i} → Tx i Hole
    peel : ∀{i} → (C : Constr' φ i)
                → {ps : All Path (typeOf' φ i C)}
                → TxNP (typeOf' φ i C) ps
                → Tx i (Fork C ps)

  data TxNP where
    nil   : TxNP [] []
    solid : ∀{κ π ps} 
          → ⟦ K κ ⟧A (Fix φ) → TxNP π ps → TxNP (K κ ∷ π) (End ∷ ps)
    into  : ∀{n π p ps}
          → Tx n p → TxNP π ps → TxNP (I n ∷ π) (p ∷ ps)

  visitNP : {π : Prod n} → ⟦ π ⟧P (Fix φ) → (ps : All Path π) → Maybe (TxNP π ps)

  visit : ∀{ν} → Fix φ ν → (p : Path (I ν)) → Maybe (Tx ν p)
  visit ⟨ el ⟩ Hole        = just hole
  visit ⟨ el ⟩ (Fork C ps) = match C el 
                         >>= λ pr → visitNP pr ps
                         >>= return ∘ peel C

  visitNP [] [] = just nil
  visitNP {K κ ∷ π} (a ∷ as) (End ∷ ps) 
    = visitNP as ps >>= return ∘ solid a 
  visitNP {I ν ∷ π} (a ∷ as) (p ∷ ps) 
    = visit a p >>= λ tx → visitNP as ps >>= return ∘ into tx

  TxNP-inj : {π : Prod n}{ps : All Path π}
           → TxNP π ps
           → All (Fix φ) (concat (All-fgt (All-map pathType ps)))
           → ⟦ π ⟧P (Fix φ)

  Tx-inj : ∀{ν}{p : Path (I ν)}
         → Tx ν p
         → All (Fix φ) (pathType p)  
         → Fix φ ν
  Tx-inj hole (el ∷ [])    = el
  Tx-inj (peel C txnp) els = ⟨ inj C (TxNP-inj txnp els) ⟩
  
  TxNP-inj nil []       = []
  TxNP-inj (solid a txnp) rs = a ∷ TxNP-inj txnp rs
  TxNP-inj (into {p = p} tx txnp) rs 
    = let (rs₀ , rs₁) = All-++-split (pathType p) rs
       in Tx-inj tx rs₀ ∷ TxNP-inj txnp rs₁


  TxNP-proj : {π : Prod n}{ps : All Path π}
            → TxNP π ps
            → ⟦ π ⟧P (Fix φ)
            → Maybe (All (Fix φ) (concat (All-fgt (All-map pathType ps))))

  Tx-proj : ∀{ν}{p : Path (I ν)}
         → Tx ν p
         → Fix φ ν
         → Maybe (All (Fix φ) (pathType p))
  Tx-proj hole el = just (el ∷ [])
  Tx-proj (peel C txnp) ⟨ el ⟩
    = match C el >>= TxNP-proj txnp 

  TxNP-proj nil [] = just []
  TxNP-proj (solid {κ} a txnp) (a' ∷ as) 
    with _≟A_ {α = K κ} a a'
  ...| no  _ = nothing
  ...| yes _ = TxNP-proj txnp as
  TxNP-proj (into tx txnp) (a  ∷ as) 
    = Tx-proj tx a >>= λ res 
    → TxNP-proj txnp as >>= λ res' 
    → return (All-++ res res')

{-
  visit : ∀{i p} → (p' : Path) → Tx i p → Maybe (Tx i (p ⊕ p'))
  visit Hole hole = hole
  visit End  hole = hole
  visit (Fork p) hole = hole
  visit (Fork p) (peel C txnp) = peel C {!!}
-}
{-

module Paths where

  -- A value of type (∂ φ i js) indicates a path inside
  -- some values of type Fix φ i leading to n subtrees, where
  -- n ≡ length js and the type of the k-th subtree is Fix φ (lookup k js) 
  --
  data ∂ {n}(φ : Fam n) : Fin n → List (Fin n) → Set where
    -- Hole is here; there is only one variable.
    here : ∀{i} → ∂ φ i (i ∷ [])
    -- Peeling one layer of recursion;
    -- We need a proof that a selection of variables is
    -- a subset of the type of the constructor
    --
    -- TODO: We are gonna roll with sub-sequences because I'm not willing
    -- to handle swaps right now. Ideally, we are looking at sub-multisets
    -- where order doesn't matter but number of occurences does!
    peel : ∀{i ks}{C : Constr' φ i} 
         → (prf : (List-map I ks) ⊆l (typeOf' φ i C))
         → ⟦ Subseq-compl prf ⟧P (Fix φ)
         → (paths : All (λ k → ∃ λ js → ∂ φ k js) ks)
         → ∂ φ i (concat (All-drop proj₁ paths))


  So : ∀{a}{A : Set a} → Dec A → Bool
  So (yes _) = true
  So (no  _) = false

  select-paths : ∀{n}{φ : Fam n}{ks : List (Fin n)}
               → (paths : All (λ k → ∃ λ js → ∂ φ k js) ks)
               → All (λ x → ⟦ x ⟧A (Fix φ)) (List-map I ks)
               → Maybe (All (Fix φ) (concat (All-drop proj₁ paths)))

  select : ∀{n}{φ : Fam n}{i : Fin n}{ks : List (Fin n)}
         → ∂ φ i ks → Fix φ i → Maybe (All (Fix φ) ks)
  select here               tree 
    = just (tree ∷ [])
  select {n} {φ} (peel {C = C} prf solid paths) ⟨ tree ⟩
    -- First we make sure the topmost constructor matches!
    = match C tree >>= λ ps 
    -- Then we split the underlying product into two parts:
    --   part0 : those elements where the many-paths follows through
    --   part1 : those elements where no holes are present within
    → let ps₀ = All-subseq-proj  prf ps
          ps₁ = All-subseq-compl prf ps
       -- compare the 'solid' parts for equality
       in if So (DecEq._≟P_ (Fix φ) _≟Fix_ solid ps₁) 
          then select-paths paths ps₀ 
          else nothing

  select-paths []                 prod = just []
  select-paths ((holes , w) ∷ ws) (px ∷ prod) 
    with select w px 
  ...| nothing = nothing
  ...| just rs 
    with select-paths ws prod
  ...| nothing = nothing
  ...| just rss = just (All-++ rs rss)
{-

  select : ∀{n k}{φ : Fam n}{π : Prod n} 
         → I k ∈ π → ⟦ π ⟧P (Fix φ) → Fix φ k
  select (here refl) (p ∷ ps) = p
  select (there prf) (p ∷ ps) = select prf ps

  match-∂ : ∀{n i j}{φ : Fam n} → ∂ φ i j → Fix φ i → Maybe (Fix φ j)
  match-∂ here                    el = just el
  match-∂ (peel {C = C} prf _ rest) ⟨ el ⟩ 
    = match C el >>= match-∂ rest ∘ select prf


  inject-∂ : ∀{n i j}{φ : Fam n} → ∂ φ i j → Fix φ j → Fix φ i
  inject-∂ here el = el
  inject-∂ (peel {C = C} prf els rest) el 
    = ⟨ inj C (fill prf (inject-∂ rest el) els) ⟩
-}

  -- I can envision defining an Alμ with ∂ above.
  --   data Alμ : Fin n → Set where
  --     peel : (del : ∂ φ i j)(ins : ∂ φ j i) → Patch Alμ (⟦ j ⟧F φ) → Alμ i
-}
