module Generic.Regular where

open import Prelude
open import Generic.Opaque
  public

data Atom : Set where
  K : (κ : Konst) → Atom 
  I :               Atom

Prod : Set
Prod = List Atom

Sum : Set
Sum = List Prod

-- ** Interpretation

⟦_⟧A : Atom → Set → Set
⟦ K κ ⟧A X = ⟦ κ ⟧K
⟦ I   ⟧A X = X 

⟦_⟧P : Prod → Set → Set
⟦ π ⟧P X = All (λ α → ⟦ α ⟧A X) π

⟦_⟧S : Sum → Set → Set
⟦ σ ⟧S X = Any (λ π → ⟦ π ⟧P X) σ

-- ** Functoriality

fmapA : ∀{α X Y}(f : X → Y) → ⟦ α ⟧A X → ⟦ α ⟧A Y
fmapA {I}   f x = f x
fmapA {K κ} f k = k

fmapP : ∀{π X Y}(f : X → Y) → ⟦ π ⟧P X → ⟦ π ⟧P Y
fmapP {[]}     _ _        = []
fmapP {α ∷ πs} f (x ∷ xs) = fmapA {α} f x ∷ fmapP f xs

fmapS : ∀{σ X Y}(f : X → Y) → ⟦ σ ⟧S X → ⟦ σ ⟧S Y
fmapS f (here  px) = here  (fmapP f px)
fmapS f (there px) = there (fmapS f px)

-- ** Consuming the recursive positions under a monoid.
--    WARNING: We are ignoring the constant types here!
--
module RegularConsume (𝕄 : Monoid lz lz) where

  M : Set
  M = Monoid.Carrier 𝕄

  ε : M
  ε = Monoid.ε 𝕄

  _∙_ : M → M → M
  _∙_ = Monoid._∙_ 𝕄

  consumeA : ∀{α} → ⟦ α ⟧A M → M
  consumeA {K _} _ = ε
  consumeA {I}   x = x

  consumeP : ∀{π} → ⟦ π ⟧P M → M
  consumeP {[]}    []       = ε
  consumeP {α ∷ π} (a ∷ ps) = consumeA {α} a ∙ consumeP ps

  consumeS : ∀{σ} → ⟦ σ ⟧S M → M
  consumeS (here p)  = consumeP p
  consumeS (there s) = consumeS s

-- ** Decidable equality

module DecEq (Rec : Set)(_≟Rec_ : (x y : Rec) → Dec (x ≡ y)) where

  _≟Atom_ : (α₁ α₂ : Atom) → Dec (α₁ ≡ α₂)
  I      ≟Atom I = yes refl
  I      ≟Atom (K _) = no λ ()
  (K _)  ≟Atom I     = no λ ()
  (K κ₁) ≟Atom (K κ₂) with κ₁ ≟Konst κ₂
  ...| yes refl = yes refl
  ...| no  ¬p  = no λ { refl → ¬p refl }

  _≟A_ :  ∀ {α} → (a₁ a₂ : ⟦ α ⟧A Rec) → Dec (a₁ ≡ a₂)
  _≟A_ {K κ} k₁ k₂ = k₁ ≟K k₂
  _≟A_ {I}   x  y  = x ≟Rec y

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

Constr : Sum → Set
Constr σ = Fin (length σ)

typeOf : (σ : Sum) → Constr σ → Prod
typeOf [] ()
typeOf (π ∷ σ) zero = π
typeOf (π ∷ σ) (suc C) = typeOf σ C

inj : {σ : Sum}{X : Set} → (C : Constr σ) → ⟦ typeOf σ C ⟧P X → ⟦ σ ⟧S X
inj {σ = []} () _
inj {σ = π ∷ σ} zero p = here p
inj {σ = x ∷ σ} (suc C) p = there (inj C p)

data SOP {σ : Sum}{X : Set} : ⟦ σ ⟧S X → Set where
  tag : (C : Constr σ)(p : ⟦ typeOf σ C ⟧P X) → SOP (inj C p)

sop : {σ : Sum}{X : Set} → (s : ⟦ σ ⟧S X) → SOP s
sop (here p) = tag zero p
sop (there s) with sop s
... | tag C p = tag (suc C) p

sop-inj-lemma : {σ : Sum}{X : Set}(C : Constr σ)(p : ⟦ typeOf σ C ⟧P X)
              → sop (inj C p) ≡ tag {σ} C p
sop-inj-lemma {[]} () p
sop-inj-lemma {x ∷ σ} zero    p = refl
sop-inj-lemma {x ∷ σ} (suc C) p 
  rewrite sop-inj-lemma {σ} C p = refl

-- * inj is an injection
inj-inj : {σ : Sum}{X : Set}{C₁ C₂ : Constr σ}
        → {P₁ : ⟦ typeOf σ C₁ ⟧P X}{P₂ : ⟦ typeOf σ C₂ ⟧P X}
        → _≡_ {A = ⟦ σ ⟧S X} (inj C₁ P₁) (inj C₂ P₂)
        → Σ (C₁ ≡ C₂) (λ { refl → P₁ ≡ P₂ })
inj-inj {[]}    {C₁ = ()}     {c2} hip
inj-inj {π ∷ σ} {C₁ = zero}   {zero} refl = refl , refl
inj-inj {π ∷ σ} {C₁ = zero}   {suc _} ()
inj-inj {π ∷ σ} {C₁ = suc c1} {zero}  ()
inj-inj {π ∷ σ} {C₁ = suc c1} {suc c2} hip 
  with inj-inj {σ} {C₁ = c1} {c2} (Any-there-inj hip) 
...| refl , p1≡p2 = refl , p1≡p2

-- * A simpler homogeneous variant
inj-injₕ  : {σ : Sum}{X : Set}{C : Constr σ}
          → {P₁ P₂ : ⟦ typeOf σ C ⟧P X}
          → _≡_ {A = ⟦ σ ⟧S X} (inj C P₁) (inj C P₂)
          → P₁ ≡ P₂
inj-injₕ hip with inj-inj hip
...| refl , p1≡p2 = p1≡p2

match : {σ : Sum}{X : Set}(C : Constr σ)
      → ⟦ σ ⟧S X → Maybe (⟦ typeOf σ C ⟧P X)
match C x with sop x
... | tag C₂ p with C ≟F C₂
... | yes refl = just p
... | no  _    = nothing 

-- * Fixpoint

data Fix (σ : Sum) : Set where
  ⟨_⟩ : ⟦ σ ⟧S (Fix σ) → Fix σ 

⟨⟩-inj : {σ : Sum}{x y : ⟦ σ ⟧S (Fix σ)}
       → ⟨ x ⟩ ≡ ⟨ y ⟩ → x ≡ y
⟨⟩-inj refl = refl

unfix : {σ : Sum} → Fix σ → ⟦ σ ⟧S (Fix σ)
unfix ⟨ x ⟩ = x

fix-unfix-lemma : {σ : Sum}(x : Fix σ) → ⟨ unfix x ⟩ ≡ x
fix-unfix-lemma ⟨ x ⟩ = refl

{-# TERMINATING #-}
_≟Fix_ : {σ : Sum} → (x y : Fix σ) → Dec (x ≡ y)
_≟Fix_ {σ = σ} ⟨ sx ⟩ ⟨ sy ⟩ with DecEq._≟S_ (Fix σ) _≟Fix_ sx sy
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })

{-# TERMINATING #-}
cata : ∀{σ A}(f : ⟦ σ ⟧S A → A) → Fix σ → A
cata f  = (f ∘ fmapS (cata f)) ∘ unfix
