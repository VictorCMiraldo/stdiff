module Prelude where

open import Level
  using () 
  renaming (zero to lz; suc to ls)
  public

open import Function 
  hiding (_⟨_⟩_)
  public

open import Algebra
  using ( Semigroup; CommutativeMonoid; Monoid)
  public

open import Algebra.Structures
  using ( IsSemigroup; IsCommutativeMonoid; IsMonoid)
  public

open import Category.Monad
  public

open import Relation.Nullary
  public

open import Relation.Unary 
  using (_⊆_)
  public

open import Relation.Binary.PropositionalEquality
  public

open import Relation.Binary
  using (_⇒_; Rel)
  public

open import Data.Unit.NonEta
  public

open import Data.Empty
  public

dec-refl : ∀{a}{A : Set a}(_≟_ : (a₁ a₂ : A) → Dec (a₁ ≡ a₂))(x : A)
         → (x ≟ x) ≡ yes refl
dec-refl _≟_ x with x ≟ x
...| no abs   = ⊥-elim (abs refl)
...| yes refl = refl

open import Data.Product
  public

open import Data.Sum
  renaming (map to Sum-map)
  public

open import Data.Maybe 
  using (Maybe ; nothing ; just ; maybe)
  renaming (map to Maybe-map)
  public

data IsJust {α}{A : Set α} : Maybe A → Set where
  indeed : (x : A) → IsJust (just x)

IsJust-map : {A B : Set}{f : A → B}{x : Maybe A}
            → IsJust x
            → IsJust (Maybe-map f x)
IsJust-map {f = f} (indeed x) = indeed (f x)

IsJust-unmap : {A B : Set}{f : A → B}{x : Maybe A}
             → IsJust (Maybe-map f x)
             → IsJust x
IsJust-unmap {x = nothing} ()
IsJust-unmap {x = just x} (indeed _) = indeed x

IsJust-magic : ∀{a}{A : Set a} → IsJust {A = A} nothing → ⊥
IsJust-magic ()

IsJust-ext : ∀{a}{A : Set a}{x : Maybe A} → IsJust x → ∃ (λ k → x ≡ just k)
IsJust-ext (indeed x) = x , refl

open import Data.Bool
  using (Bool ; true ; false) 
  renaming (_≟_ to _≟B_)
  public

open import Data.Fin 
  using (Fin ; suc ; zero)
  public

open import Data.Fin.Properties 
  using ()
  renaming (_≟_ to _≟F_)
  public

open import Data.Nat 
  renaming (_≟_ to _≟N_)
  hiding (_⊓_)
  public

open import Data.List
  using (List ; _∷_ ; [] ; length)
  renaming (map to List-map ; zip to List-zip)
  public

open import Data.List.All
  using (All ; _∷_ ; []) 
  renaming (map to All-map)
  public

open import Data.List.Any
  hiding (map)
  public

open import Data.String
  using (String ; primStringEquality)
  renaming (_++_ to strcat)
  public

open import Data.Vec
  using (Vec ; _∷_; [])
  renaming (map to Vec-map ; lookup to Vec-lookup)
  public

-- * Misc. Library functions

_≟Str_ : (x y : String) → Dec (x ≡ y)
x ≟Str y with primStringEquality x y
...| true  = yes primTrustMe
  where open import Agda.Builtin.TrustMe
...| false = no (const magic)
  where postulate magic : ⊥

all-foldr : {A : Set}{P : A → Set}{X : List A → Set}
          → (∀{x xs} → P x → X xs → X (x ∷ xs))
          → X [] → {l : List A}
          → All P l → X l
all-foldr f g [] = g
all-foldr {A} {P} {X} f g (x ∷ xs) = f x (all-foldr {A} {P} {X} f g xs)

zipd : {A : Set}{P Q : A → Set}{xs : List A} 
     → All P xs → All Q xs → All (λ x → P x × Q x) xs
zipd {xs = []} [] [] = []
zipd {xs = x ∷ xs} (px ∷ p) (qx ∷ q) = (px , qx) ∷ zipd p q

All-set : {A : Set}{P : A → Set}{xs : List A}
        → (f : ∀{a} → P a → Set)
        → All P xs
        → Set
All-set f [] = Unit
All-set f (x ∷ xs) = f x × All-set f xs
