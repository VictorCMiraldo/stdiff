open import Prelude
open import Generic.Regular

module Regular.Relations.PartialOrder.Functor 
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (AppRec    : Rec → Rec → PatchRec → Set)
       (_⊆Rec_    : {p₁ p₂ : PatchRec}{x y : Rec}
                  → AppRec x y p₁ → AppRec x y p₂ → Set)
    where

  open import Regular.Internal.Functor Rec _≟Rec_
  open import Regular.Relations.Applies.Functor Rec _≟Rec_ PatchRec AppRec

  data _⊆At_ : {α : Atom}{x y : ⟦ α ⟧A Rec}
             → {a₁ a₂ : At PatchRec α}
             → AppAt x y a₁ → AppAt x y a₂ → Set where
    SubId  : ∀{κ}{k k' a : ⟦ κ ⟧K}
           → AppSetId k a ⊆At AppSetId k' a 

    SubSet : ∀{κ}{k₁ k₂ : ⟦ κ ⟧K}(q : k₁ ≢ k₂)
           → AppSet k₁ k₂ q ⊆At AppSet k₁ k₂ q

    SubFix : {r₁ r₂ : Rec}{p₁ p₂ : PatchRec}
           → (hp₁ : AppRec r₁ r₂ p₁)
           → (hp₂ : AppRec r₁ r₂ p₂)
           → hp₁ ⊆Rec hp₂
           → AppFix r₁ r₂ p₁ hp₁ ⊆At AppFix r₁ r₂ p₂ hp₂

  -- VCM: Thisd doesn't cut it. We need to compare
  --      alignments sync-points pairwise.
  --      insertions might be different everywhere.
  data _⊆Al_ : {π₁ π₂ : Prod}{x : ⟦ π₁ ⟧P Rec}{y : ⟦ π₂ ⟧P Rec}
             → {p₁ p₂ : Al (At PatchRec) π₁ π₂}
             → AppAl x y p₁ → AppAl x y p₂ → Set where
    -- VCM: IMPORTANT: Note that anti-symmetry will not
    --      be satisfied under propositional-equality.
    --      Patch-equality is a bit weaker than propositional
    --      equality. The 'deletion products' don't really need data.
    --      Same for SubId above
    SubA0 : ∀{π₁ π₂}{d d' d'' : ⟦ π₁ ⟧P Rec}{i : ⟦ π₂ ⟧P Rec}
          → AppA0 d d' i ⊆Al AppA0 d d'' i

    -- VCM: Insertions could be different!
    SubAX : ∀{α π₁ π₁' π₂ π₂'}{d d' d'' : ⟦ π₁ ⟧P Rec}{i : ⟦ π₂ ⟧P Rec}
          → {x x' : ⟦ α ⟧A Rec}
          → {xs   : ⟦ π₁' ⟧P Rec}
          → {xs'  : ⟦ π₂' ⟧P Rec}
          → {r₁ r₂ : At PatchRec α}
          → {al₁ al₂ : Al (At PatchRec) π₁' π₂'}
          → (max₁ : isMaximal al₁)
          → (max₂ : isMaximal al₂)
          → (hr₁  : AppAt x  x'  r₁)
          → (hr₂  : AppAt x  x'  r₂)
          → (hal₁ : AppAl xs xs' al₁)
          → (hal₂ : AppAl xs xs' al₂)
          → hr₁ ⊆At hr₂
          → hal₁ ⊆Al hal₂
          → AppAX d d' i r₁ al₁ hr₁ hal₁ ⊆Al AppAX d d'' i r₂ al₂ hr₂ hal₂
