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

postulate
  fun-ext : ∀{a b}{A : Set a}{B : Set b}{f g : A → B}
          → (∀ x → f x ≡ g x)
          → f ≡ g

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
  renaming (map to _><_)
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

IsJust-from≡ : ∀{a}{A : Set a}{x : Maybe A}{y : A}
             → x ≡ just y → IsJust x
IsJust-from≡ {y = y} refl = indeed y

just-inj : ∀{a}{A : Set a}{x y : A} 
         → _≡_ {A = Maybe A} (just x) (just y) → x ≡ y
just-inj refl = refl

Maybe-⊥-elim : ∀{a b}{A : Set a}{B : Set b}{x : A} 
             → _≡_ {A = Maybe A} nothing (just x) → B
Maybe-⊥-elim () 

Maybe-map-def : ∀{a b}{A : Set a}{B : Set b}{f : A → B}
              → (x : Maybe A){y : A}
              → x ≡ just y
              → Maybe-map f x ≡ just (f y)
Maybe-map-def nothing ()
Maybe-map-def (just y) refl = refl 

Maybe-unmap-def : ∀{a b}{A : Set a}{B : Set b}{f : A → B}
                → (f-inj : ∀{m n} → f m ≡ f n → m ≡ n)
                → (x : Maybe A){y : A}
                → Maybe-map f x ≡ just (f y)
                → x ≡ just y
Maybe-unmap-def f-inj nothing ()
Maybe-unmap-def f-inj (just y) hip = cong just (f-inj (just-inj hip)) 

open import Data.Bool
  using (Bool ; true ; false) 
  renaming (_≟_ to _≟B_)
  public

open import Data.Fin 
  using (Fin ; suc ; zero; inject₁)
  public

open import Data.Fin.Properties 
  using ()
  renaming (_≟_ to _≟F_)
  public

open import Data.Nat 
  renaming (_≟_ to _≟N_)
  hiding (_⊓_)
  public

NonZero : ℕ → Set
NonZero zero    = ⊥
NonZero (suc _) = Unit

open import Data.Nat.Properties.Simple
  public

open import Data.List
  using (List ; _∷_ ; [] ; length ; _++_)
  renaming (map to List-map ; zip to List-zip)
  public

open import Data.List.All
  using (All ; _∷_ ; []) 
  renaming (map to All-map)
  public

All-∷-inj 
  : ∀{a}{A : Set a}{P : A → Set}{x : A}{xs : List A}
  → {px py : P x}{pxs pys : All P xs}
  → _≡_ {A = All P (x ∷ xs)} (px ∷ pxs) (py ∷ pys) → px ≡ py × pxs ≡ pys
All-∷-inj refl = refl , refl

All-fgt 
  : ∀{a}{A : Set a}{xs : List A} 
  → All (const A) xs → List A
All-fgt []       = []
All-fgt (x ∷ xs) = x ∷ All-fgt xs

open import Data.List.Any
  hiding (map)
  public

Any-there-inj
  : ∀{a}{A : Set a}{P : A → Set}{x : A}{xs : List A}
  → {px py : Any P xs}
  → _≡_ {A = Any P (x ∷ xs)} (there px) (there py)
  → px ≡ py
Any-there-inj refl = refl

-- List disjointness

_∈_ : ∀{a}{A : Set a} → A → List A → Set a
x ∈ l = Any (_≡_ x) l

_∉_ : ∀{a}{A : Set a} → A → List A → Set a
x ∉ l = ¬ (x ∈ l)

∉-∷ : ∀{a}{A : Set a}{x y : A}{l : List A}
    → x ≢ y → x ∉ l → x ∉ (y ∷ l)
∉-∷ x≢y x∉l (here  abs) = x≢y abs
∉-∷ x≢y x∉l (there abs) = x∉l abs

∉-head : ∀{a}{A : Set a}{x y : A}{l : List A}
       → x ∉ (y ∷ l) → x ≢ y
∉-head hip abs = hip (here abs)

∉-tail : ∀{a}{A : Set a}{x y : A}{l : List A}
       → x ∉ (y ∷ l) → x ∉ l
∉-tail hip abs = hip (there abs)

data Disj {a}{A : Set a} : List A → List A → Set a where
  nil  : ∀{l}       → Disj l []
  cons : ∀{x l₁ l₂} → x ∉ l₁ → Disj l₁ l₂ → Disj l₁ (x ∷ l₂)

disj-prepend : ∀{a}{A : Set a}{l₁ l₂ : List A}{x : A}
             → x ∉ l₂ → Disj l₁ l₂ → Disj (x ∷ l₁) l₂
disj-prepend hip nil        = nil
disj-prepend hip (cons h d) 
  = cons (∉-∷ (∉-head hip ∘ sym) h) 
         (disj-prepend (∉-tail hip) d)

disj-nil : ∀{a}{A : Set a}{l : List A}
         → Disj [] l
disj-nil {l = []}    = nil
disj-nil {l = x ∷ l} = cons (λ ()) (disj-nil {l = l})

disj-sym : ∀{a}{A : Set a}{l₁ l₂ : List A} 
         → Disj l₁ l₂ → Disj l₂ l₁
disj-sym nil        = disj-nil
disj-sym (cons p h) = disj-prepend p (disj-sym h)

∈-dec : ∀{a}{A : Set a}(_≟A_ : (a₁ a₂ : A) → Dec (a₁ ≡ a₂))
      → (x : A) → (l : List A) → Dec (x ∈ l)
∈-dec _≟A_ x [] = no (λ ())
∈-dec _≟A_ x (y ∷ l) with x ≟A y
...| yes x≡y = yes (here x≡y)
...| no  x≢y with ∈-dec _≟A_ x l
...| yes x∈l = yes (there x∈l)
...| no  x∉l = no (∉-∷ x≢y x∉l)

disj-dec : ∀{a}{A : Set a}(_≟A_ : (a₁ a₂ : A) → Dec (a₁ ≡ a₂))
         → (l₁ l₂ : List A) → Dec (Disj l₁ l₂)
disj-dec _≟A_ l₁ []       = yes nil
disj-dec _≟A_ l₁ (x ∷ l₂) with ∈-dec _≟A_ x l₁ 
...| yes x∈l₁ = no (λ { (cons abs _) → abs x∈l₁ })
...| no  x∉l₁ with disj-dec _≟A_ l₁ l₂
...| no  ¬disj = no (λ { (cons _ abs) → ¬disj abs })  
...| yes  disj = yes (cons x∉l₁ disj)

open import Data.String
  using (String ; primStringEquality)
  renaming (_++_ to strcat)
  public

open import Data.Vec
  using (Vec ; _∷_; [])
  renaming (map to Vec-map ; lookup to Vec-lookup)
  public

vec-foldr : ∀{a b}{A : Set a}{B : Set b}{n : ℕ}
          → (A → B → B) → B → Vec A n → B
vec-foldr f g []       = g
vec-foldr f g (x ∷ xs) = f x (vec-foldr f g xs)

vec-max : ∀{n} → Vec ℕ (suc n) → Fin (suc n)
vec-max (x ∷ [])     = zero
vec-max {suc n} (x ∷ y ∷ ys) with vec-max (y ∷ ys)
...| my with x ≤? Vec-lookup my (y ∷ ys) 
...| yes _ = suc my
...| no _  = inject₁ my

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

all-max : {A : Set}{P : A → Set}{l : A}{ls : List A}
        → (measure : ∀{a} → P a → ℕ)
        → All P (l ∷ ls) → ∃ P
all-max mes (pa ∷ [])          = _ , pa
all-max mes (pa ∷ (pa' ∷ pas)) 
  with mes pa ≤? mes pa'
...| yes _ = all-max mes (pa' ∷ pas)
...| no  _ = all-max mes (pa ∷ pas)

all-lookup : {A : Set}{P : A → Set}{l : List A}
           → Fin (length l) → All P l → ∃ (λ a → P a)
all-lookup () []
all-lookup {l = l ∷ ls} zero      (px ∷ a) = l , px
all-lookup {l = l ∷ ls} (suc idx) (px ∷ a) = all-lookup idx a

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

All-head : {A : Set}{P : A → Set}{x : A}{xs : List A}
         → All P (x ∷ xs) → P x
All-head (px ∷ _) = px

All-tail : {A : Set}{P : A → Set}{x : A}{xs : List A}
         → All P (x ∷ xs) → All P xs
All-tail (_ ∷ pxs) = pxs
