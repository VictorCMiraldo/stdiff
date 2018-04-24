open import Prelude
open import Generic.Regular

module Regular.Lab.2-3-Tree where

  2-3-treeF : Sum
  2-3-treeF =
    let leafT = [] in
    let 2nodeT = K `ℕ ∷ I ∷ I ∷ [] in
    let 3nodeT = K `ℕ ∷ I ∷ I ∷ I ∷ [] in
    leafT ∷ 2nodeT ∷ 3nodeT ∷ []

  `leaf `2-node `3-node : Constr 2-3-treeF
  `leaf = zero
  `2-node = suc zero
  `3-node = suc (suc zero)

  is-2-node? : ∀ {A} → ⟦ 2-3-treeF ⟧S A → Bool
  is-2-node? x with sop x
  ... | tag (suc zero) ls = true
  ... | tag _ ls = false

  2-3-tree : Set
  2-3-tree = Fix 2-3-treeF

  leaf : 2-3-tree
  leaf = ⟨ here [] ⟩

  2-node : ℕ → 2-3-tree → 2-3-tree → 2-3-tree
  2-node n l r = ⟨ there (here (n ∷ l ∷ r ∷ [])) ⟩

  3-node : ℕ → 2-3-tree → 2-3-tree → 2-3-tree → 2-3-tree
  3-node n l c r = ⟨ (there (there (here (n ∷ l ∷ c ∷ r ∷ [])))) ⟩

  t₁ : 2-3-tree
  t₁ = 3-node 1 leaf (2-node 2 leaf leaf) (2-node 3 leaf leaf)

  t₂ : 2-3-tree
  t₂ = 3-node 1 leaf (2-node 5 leaf leaf) (2-node 3 leaf leaf)

  t₃ : 2-3-tree
  t₃ = 3-node 1 leaf (2-node 2 leaf leaf) (3-node 3 leaf leaf leaf)

  t₄ : 2-3-tree
  t₄ = 2-node 3 leaf leaf
  
  open import Regular.Functor 2-3-tree _≟Fix_
    public

  

  p1 p2 : Prod

  p1 = I ∷ K `ℕ ∷ K `ℕ ∷ I ∷ I ∷ []
  p2 = K `ℕ ∷ I ∷ I ∷ []

  ats₁ : ⟦ p1 ⟧P 2-3-tree
  ats₁ = leaf ∷ (4 ∷ (7 ∷ (leaf ∷ (leaf ∷ []))))

  ats₂ : ⟦ p2 ⟧P 2-3-tree
  ats₂ = 3 ∷ leaf ∷ leaf ∷ []

  als : List (Al TrivialA p1 p2)
  als = align ats₁ ats₂

  decide : {A : Set} → Dec A → Bool
  decide (yes _) = true
  decide (no  _) = false

  ok : List Bool
  ok = List-map (decide ∘ isMaximal?) als

  
{-
  open import Regular.Fixpoint 2-3-treeF
    public

  p12 : Alμ
  p12 = spn
        (Scns (suc (suc zero))
         (set (1 , 1) ∷
          fix (spn Scp) ∷
          fix
          (spn
           (Scns (suc zero)
            (set (2 , 5) ∷ fix (spn Scp) ∷ fix (spn Scp) ∷ [])))
          ∷ fix (spn Scp) ∷ []))
  
  p13 : Alμ
  p13 = spn
        (Scns (suc (suc zero))
        (set (1 , 1) ∷
          fix (spn Scp) ∷
          fix (spn Scp) ∷
          fix
          (spn
          (Schg (suc zero) (suc (suc zero)) {λ ()}
            (AX (set (3 , 3))
            (AX (fix (spn Scp)) (AX (fix (spn Scp)) (Ains ⟨ here [] ⟩ A0))))))
          ∷ []))


  p23 : Alμ
  p23 = spn (Scns (suc (suc zero)) 
             ( (set ((1 , 1))) 
             ∷ fix (spn Scp) 
             ∷ fix (spn (Scns (suc zero) 
                        ( set ((5 , 2)) 
                        ∷ fix (spn Scp)
                        ∷ fix (spn Scp)
                        ∷ [])))
             ∷ fix (spn (Schg (suc zero) (suc (suc zero)) {λ ()}
                   (AX (set (1 , 1)) 
                   (Ains ⟨ here [] ⟩ 
                   (AX (fix (spn Scp)) 
                   (AX (fix (spn Scp)) 
                   A0)))))) 
             ∷ []))
       

  p14 : Alμ
  p14 = del (suc (suc zero))
        (there 1
        (there ⟨ here [] ⟩
          (there ⟨ there (here (2 ∷ ⟨ here [] ⟩ ∷ ⟨ here [] ⟩ ∷ [])) ⟩
          (here (spn Scp) []))))


  open import Regular.ES.Fixpoint 2-3-treeF
  open import Regular.ES.MemoEnum 2-3-treeF

  es23 : ES (I ∷ []) (I ∷ [])
  es23 = getDiff (diffT (t₂ ∷ []) (t₃ ∷ []))
-}
