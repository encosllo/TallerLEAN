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
  sorry,
end

-- Inter 𝔸 és el major conjunt per davall de tots els conjunts de la família
lemma L2 (Z : set Ω) (h1: ∀ (i : I), Z ⊆ 𝔸 i) : Z ⊆ ⋂ i, 𝔸 i:=
begin
  sorry,
end

#check (⋂ (i : I), ((𝔸 i) ∩ (𝔹 i)))
#check (⋂ (i:I), 𝔸 i) ∩ (⋂ (i:I), 𝔹 i) 
-- Inter distribueix sobre ∩ 
lemma L3  : (⋂ (i : I), ((𝔸 i) ∩ (𝔹 i))) = (⋂ (i:I), 𝔸 i) ∩ (⋂ (i:I), 𝔹 i) :=
begin
  sorry,
end

------------------

-- Union 𝔸 està per damunt de cada conjunt de la família
lemma L4 : ∀ (i : I), 𝔸 i ⊆ ⋃ (i:I), 𝔸 i:=
begin
  sorry,
end

-- Union 𝔸 és el menor conjunt per damunt de tots els conjunts de la família
lemma L5 (Z : set Ω) (h1: ∀ (i : I), 𝔸 i ⊆ Z) : (⋃ (i:I), 𝔸 i) ⊆ Z :=
begin
  sorry,
end 

#check (⋃ (i : I), ((𝔸 i) ∪ (𝔹 i)))
#check (⋃ (i:I), 𝔸 i) ∪ (⋃ (i:I), 𝔹 i) 
-- Inter distribueix sobre ∩ 
lemma L6  : (⋃ (i : I), ((𝔸 i) ∪ (𝔹 i))) = (⋃ (i:I), 𝔸 i) ∪ (⋃ (i:I), 𝔹 i) :=
begin
  sorry,
end







