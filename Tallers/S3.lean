-- Obre els recursos per a treballar amb conjunts
-- https://leanprover-community.github.io/mathlib_docs/data/set/basic.html

import data.set.basic  
open set 
-- open classical


-- Assumirem en tot l'exercici que 
-- Ω és un tipus que farà de contenidor
variable (Ω : Type)
-- a b c x y z seran elements de tipus Ω 
variables a b c x y z : Ω    
-- P és una proposició sobre elements de tipus Ω
variable P : Ω → Prop 

-- Igualtats en Lean
-- https://leanprover.github.io/theorem_proving_in_lean/quantifiers_and_equality.html

-- Reflexiva
#check eq.refl    
lemma LRefl : x = x :=
begin
  exact eq.refl x,
end

-- Simètrica
#check eq.symm  
lemma LSim (h1: x = y) : y = x :=  
begin
  exact eq.symm h1,
end

-- Transitiva
#check eq.trans
lemma LTrans (h1: x = y) (h2: y = z) : x = z :=  
begin
  exact eq.trans h1 h2,
end

-- Substitució
#check eq.subst
lemma LSubs (h1: x = y) (h2: P x) : P y :=  
begin
  exact eq.subst h1 h2,
end

----------------------
-- Comencem a treballar amb conjunts
-- A B C X Y Z són conjunts amb elements de tipus Ω 
variables A B C X Y Z : set Ω

-- Definició de la inclusió
-- X ⊆ Y és equivalent a ∀ (a:Ω), a ∈ X → a ∈ Y
lemma T1 : X ⊆ Y ↔ ∀ (a:Ω), a ∈ X → a ∈ Y :=
begin
  split,
  -- D'esquerra a dreta
  assume h1,
  intro x,
  assume h2,
  exact h1 h2,
  -- De dreta a esquerra
  assume h1,
  intro x,
  exact h1 x,
end

-- Reflexivitat de la inclusió
lemma T2 : X ⊆ X :=
begin
  intro x,
  assume h1, 
  exact h1,
end

#check set.subset.rfl
lemma T2b : X ⊆ X :=
begin
  exact set.subset.rfl, 
end

-- Transitivitat de la inclusió
lemma T3 (h1 : X ⊆ Y) (h2 : Y ⊆ Z) : X ⊆ Z :=
begin
  intro x,
  assume h3,
  exact h2 (h1 h3),
end

#check set.subset.trans
-- Transitivitat de la inclusió
lemma T3b (h1 : X ⊆ Y) (h2 : Y ⊆ Z) : X ⊆ Z :=
begin
  exact set.subset.trans h1 h2,
end

-- Igualtat de conjunts
#check set.ext_iff
#check iff.elim
#check x ∈ X
lemma T4 : X = Y ↔ (∀ (a:Ω), a ∈ X ↔ a ∈ Y) :=
begin
  split,
  -- D'esquerra a dreta
  assume h1,
  intro x,
  split,
  --
  assume h2,
  exact (eq.subst h1 h2),
  --
  assume h2,
  exact (eq.subst (eq.symm h1) h2),
  -- De dreta a esquerra
  assume h1,
  exact (iff.elim_right set.ext_iff) h1,
end

lemma T4b : X = Y ↔ (∀ (a:Ω), a ∈ X ↔ a ∈ Y) :=
begin
  exact set.ext_iff,
end

-- Antisimetria de la inclusió
lemma T5 (h1: X ⊆ Y) (h2: Y ⊆ X) : X = Y :=
begin
  have h3: ∀ (a:Ω), a ∈ X ↔ a ∈ Y,
  intro x,
  split,
  assume h4,
  exact h1 h4,
  assume h4,
  exact h2 h4,
  exact (iff.elim_right set.ext_iff) h3,
end 

#check set.eq_of_subset_of_subset
lemma T5b (h1: X ⊆ Y) (h2: Y ⊆ X) : X = Y :=
begin
  exact set.eq_of_subset_of_subset h1 h2,
end 

-- Intersecció de conjunts
-- ∩ cap
lemma T6 (h1: x ∈ X) (h2: x ∈ Y) : x ∈ X ∩ Y:=
begin
  exact and.intro h1 h2,
end 

-- Unió de conjunts
-- ∪ cup 
-- a esquerra
lemma T7e (h1: x ∈ X) : x ∈ X ∪ Y:=
begin
  exact or.inl h1,
end 

-- a dreta
lemma T7d (h1: x ∈ Y) : x ∈ X ∪ Y:=
begin
  exact or.inr h1,
end 

-- Conjunt buit
-- ∅ empty emptyset
#check ∅ 
#check set.mem_empty_eq 
lemma T8 : ∅ ⊆ X :=
begin
  intro x,
  assume h1,
  have h2: x ∈ ∅ = false, from set.mem_empty_eq x,
  have h3: false, from eq.subst h2 h1,
  exact false.elim h3,
end

lemma T8b : ∅ ⊆ X :=
begin
  intro x,
  assume h1,
  exact false.elim h1,
end

#check ∅ 
lemma T9 : x ∉ (∅ : set Ω) :=
begin
  by_contradiction,
  exact h,
end

lemma T10: A \ (B ∪ C) = (A \ B) ∩ (A \ C) :=
begin
  -- rewrite
  rw [set.ext_iff],
  intro x,
  split,
  -- D'esquerra a dreta
  assume h1,
  have h2: x ∈ A, from and.elim_left h1,
  have h3: x ∉ B ∪ C, from and.elim_right h1,
  have h4: x ∉ B,
  by_contradiction h4,
  exact h3 (or.inl h4), 
  have h5: x ∉ C,
  by_contradiction h5,
  exact h3 (or.inr h5), 
  exact (and.intro (and.intro h2 h4) (and.intro h2 h5)),
  -- De dreta a esquerra
  assume h1,
  have h2: x ∈ A \ B, from and.elim_left h1,
  have h3: x ∈ A \ C, from and.elim_right h1,
  have h4: x ∈ A, from and.elim_left h2,
  have h5: x ∉ B, from and.elim_right h2,
  have h6: x ∉ C, from and.elim_right h3,
  have h7: x ∉ B ∪ C,
  by_contradiction h7,
  cases h7,
  exact h5 h7,
  exact h6 h7,
  exact and.intro h4 h7,
end

-- Conjunt potència
-- 𝒫  powerset
#check 𝒫 X
lemma T11 (h1: X ⊆ Y) : X ∈ 𝒫 Y :=
begin
  exact h1,
end

#check (𝒫 (∅: set Ω)) ≠ (∅ : set (set Ω))
lemma T12 : (𝒫 (∅: set Ω)) ≠ (∅ : set (set Ω)) :=
begin
  assume h1,
  have h2: (∅ : set Ω) ⊆ (∅: set Ω), 
  exact set.subset.rfl, 
  have h3: (∅ : set Ω) ∈ (𝒫 (∅: set Ω)), exact h2,
  have h4: (∅ : set Ω) ∈ (∅ : set (set Ω)), from eq.subst h1 h3,
  exact h4,
end 



