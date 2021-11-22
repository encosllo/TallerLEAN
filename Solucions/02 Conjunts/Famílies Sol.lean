-- Obre els recursos per a treballar amb conjunts
-- https://leanprover-community.github.io/mathlib_docs/data/set/basic.html

import data.set.basic  
open set 
-- open classical

-- Assumirem en tot l'exercici que 
-- Ω és un tipus que farà de contenidor
variables {I Ω : Type}
-- a b c x y z seran elements de tipus Ω 
variables a b c x y z : Ω  
-- a b c x y z seran elements de tipus Ω 
variables X Y Z : set Ω    
-- P és una proposició sobre elements de tipus Ω
variable P : Ω → Prop 
-- famílies de conjunts de tipus Ω 
variables 𝔸 𝔹 ℂ : I → set Ω
-- bbA bbB bbC

-- Definició de la unió i la intersecció d'una família
-- https://leanprover.github.io/logic_and_proof/sets_in_lean.html
def Union (𝔸 : I → set Ω) : set Ω := { x | ∃ (i : I), x ∈ 𝔸 i }
def Inter (𝔸 : I → set Ω) : set Ω := { x | ∀ (i : I), x ∈ 𝔸 i }

notation `⋃` binders `, ` r:(scoped f, Union f) := r
notation `⋂` binders `, ` r:(scoped f, Inter f) := r

-- ⋃    Un
-- ⋂    I


#check Union 𝔸 
#check Inter 𝔸 

#check ⋃ i, 𝔸 i 
#check ⋂ i, 𝔸 i

-- Inter 𝔸 està per davall de cada conjunt en la família
lemma L1 : ∀ (i : I), ((⋂ (i:I), 𝔸 i) ⊆ 𝔸 i) :=
begin
  intro i,
  intro z,
  assume h1,
  exact h1 i,
end

-- Inter 𝔸 és el major conjunt per davall de tots els conjunts de la família
lemma L2 (Z : set Ω) (h1: ∀ (i : I), Z ⊆ 𝔸 i) : Z ⊆ ⋂ i, 𝔸 i:=
begin
  intro z,
  assume h2,
  have h3: ∀ (i : I), z ∈ 𝔸 i,
  intro i,
  exact (h1 i) h2,
  exact h3,
end

#check (⋂ (i : I), ((𝔸 i) ∩ (𝔹 i)))
#check (⋂ (i:I), 𝔸 i) ∩ (⋂ (i:I), 𝔹 i) 
-- Inter distribueix sobre ∩ 
lemma L3  : (⋂ (i : I), ((𝔸 i) ∩ (𝔹 i))) = (⋂ (i:I), 𝔸 i) ∩ (⋂ (i:I), 𝔹 i) :=
begin
  ext z,
  split,
  -- D'esquerra a dreta
  assume h2,
  have h3: z ∈ (⋂ (i : I), 𝔸 i) ,
  intro i, 
  exact and.elim_left (h2 i),
  have h4: z ∈ (⋂ (i : I), 𝔹 i) ,
  intro i, 
  exact and.elim_right (h2 i),
  exact and.intro h3 h4,
  -- De dreta a esquerra
  assume h2,
  intro i,
  exact and.intro ((and.elim_left h2) i) ((and.elim_right h2) i), 
end

------------------

-- Union 𝔸 està per damunt de cada conjunt de la família
lemma L4 : ∀ (i : I), 𝔸 i ⊆ ⋃ (i:I), 𝔸 i:=
begin
  intro i,
  intro z,
  assume h1,
  exact exists.intro i h1,
end

-- Union 𝔸 és el menor conjunt per damunt de tots els conjunts de la família
lemma L5 (Z : set Ω) (h1: ∀ (i : I), 𝔸 i ⊆ Z) : (⋃ (i:I), 𝔸 i) ⊆ Z :=
begin
  intro x,
  assume h2,
  cases h2 with i h3,
  exact (h1 i) h3,
end 

#check (⋃ (i : I), ((𝔸 i) ∪ (𝔹 i)))
#check (⋃ (i:I), 𝔸 i) ∪ (⋃ (i:I), 𝔹 i) 
-- Inter distribueix sobre ∩ 
lemma L6  : (⋃ (i : I), ((𝔸 i) ∪ (𝔹 i))) = (⋃ (i:I), 𝔸 i) ∪ (⋃ (i:I), 𝔹 i) :=
begin
  ext z,
  split,
  -- D'esquerra a dreta
  assume h1,
  have h2: (z ∈ (⋃ (i:I), 𝔸 i)) ∨ (z ∉ (⋃ (i:I), 𝔸 i)), from em (z ∈ (⋃ (i:I), 𝔸 i)),
  cases h2,
  exact or.inl h2,
  --
  have h3: z ∈ (⋃ (i:I), 𝔹 i),
  by_contradiction h3,
  cases h1 with i h4,
  have h5: z ∈ (𝔸 i) ∪ (𝔹 i), exact h4,
  cases h5,
  --
  have h6: z ∈ (⋃ (i:I), 𝔸 i),
  exact exists.intro i h5,
  exact h2 h6,
  --
  have h6: z ∈ (⋃ (i:I), 𝔹 i),
  exact exists.intro i h5,
  exact h3 h6,
  --
  exact or.inr h3,
  -- De dreta a esquerra
  assume h1,
  cases h1,
  --
  cases h1 with i h1,
  exact exists.intro i (or.inl h1),
  --
  cases h1 with i h1,
  exact exists.intro i (or.inr h1),
end







