-- Annotated version of our regular types;
-- The annotations consists in a insert, delete or copy flag
-- on each constructor of a value.
module Generic.RegularAnn where

open import Prelude
open import Generic.Regular
open import Generic.Opaque

-- An annotation represents either a moving part,
-- or a copied part. A moving part in the source represents
-- a deletion whereas a moving part in the destinationa
-- represents a insertion
data Ann : Set where
  M C : Ann

⟦_⟧Sₐ : Sum → Set → Set
⟦ σ ⟧Sₐ X = Ann × ⟦ σ ⟧S X

fmapSₐ : ∀{σ X Y} → (X → Y) → ⟦ σ ⟧Sₐ X → ⟦ σ ⟧Sₐ Y
fmapSₐ f (ann , x) = ann , fmapS f x

data Fixₐ (σ : Sum) : Set where
  ⟨_⟩ : ⟦ σ ⟧Sₐ (Fixₐ σ) → Fixₐ σ 

{-# TERMINATING #-}
𝓤 : ∀{σ} → Fixₐ σ → Fix σ
𝓤 ⟨ _ , x ⟩ = ⟨ fmapS 𝓤 x ⟩

unfixₐ : {σ : Sum} → Fixₐ σ → ⟦ σ ⟧Sₐ (Fixₐ σ)
unfixₐ ⟨ ann , x ⟩ = ann , x

{-# TERMINATING #-}
cataₐ : ∀{σ A} → (⟦ σ ⟧Sₐ A → A) → Fixₐ σ → A
cataₐ f = f ∘ fmapSₐ (cataₐ f) ∘ unfixₐ
