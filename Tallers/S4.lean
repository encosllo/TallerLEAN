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
variable 𝔸 : I → set Ω
-- R S T relacions sobre Ω
variables R S T : Ω → Ω → Prop  

def Temp : set nat := {3,2,1}
#check Temp 1

example : 3 ∈ Temp :=
begin
  have h1: 3 = 3, from refl 3,
  exact (or.inl h1),
end

example : 2 ∈ Temp :=
begin
  have h1: 2 = 2, from refl 2,
  exact or.inr (or.inl h1),
end

example : 1 ∈ Temp :=
begin
  have h1: 1 = 1, from refl 1,
  exact or.inr (or.inr h1),
end

example (x : Ω) : x ∈ ({x} : set Ω) :=
begin
  have h1: x = x, from refl x,
  exact h1,
end

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
lemma L1 : ∀ (i : I), Inter 𝔸 ⊆ 𝔸 i :=
begin
  intro i,
  intro z,
  assume h1,
  exact h1 i,
end

-- Union 𝔸 està per damunt de cada conjunt de la família
lemma L2 : ∀ (i : I), 𝔸 i ⊆ Union 𝔸 :=
begin
  intro i,
  intro z,
  assume h1,
  exact exists.intro i h1,
end

-----------------------------
-----------------------------
-- Relacions
-- https://leanprover.github.io/logic_and_proof/relations_in_lean.html

#check reflexive 
#check reflexive R 

-- reflexive R és una abreviatura per a 
-- ∀ (x : Ω), R x x
lemma L3 (h1 : reflexive R) (x : Ω) : R x x :=
begin
  exact h1 x,
end 

#check symmetric
#check symmetric R

-- symmetric R és una abreviatura per a 
-- ∀ (x y: Ω), (R x y) → (R y x)
lemma L4 (h1 : symmetric R) (x y : Ω) (h2 : R x y) : R y x :=
begin
  exact h1 h2,
end 

#check anti_symmetric
#check anti_symmetric R

-- anti_symmetric R és una abreviatura per a 
-- ∀ (x y: Ω), (R x y) → (R y x) → x = y
lemma L5 (h1 : anti_symmetric R) (x y : Ω) (h2 : R x y) (h3 : R y x) : x = y :=
begin
  exact h1 h2 h3,
end 

#check transitive
#check transitive R 

-- transitive R és una abreviatura per a 
-- ∀ (x y z : Ω), (R x y) → (R y z) → (R x z)
lemma L6 (h1 : transitive R) (x y z : Ω) (h2: R x y) (h3: R y z) : R x z :=
begin
  exact h1 h2 h3,
end

-- equivalence R és una abreviatura per a 
-- reflexive R ∧ (symmetric R ∧ transitive R)
#check equivalence
#print equivalence
#check equivalence R 

lemma L7 (h1 : equivalence R) : reflexive R :=
begin
  exact and.elim_left h1,
end

lemma L8 (h1 : equivalence R) : symmetric R :=
begin
  exact and.elim_left (and.elim_right h1),
end

lemma L9 (h1 : equivalence R) : transitive R :=
begin
  exact and.elim_right (and.elim_right h1),
end

-- 
-- Definim la igualtat entre relacions 
-- Aquesta igualtat és semàntica
def Igual (R S: Ω → Ω → Prop) : Prop := ∀ (x y : Ω), R x y ↔ S x y
-- Emprar l'infix == en compte de Igual
local infix == := Igual 

#check Igual
#check Igual R 
#check Igual R S

#check R = S 
#check R == S

theorem TRefl : R = R :=
begin
  exact refl R,
end

#print eq

theorem TReflDobleIgual : R == R :=
begin
  intros x y,
  split,
  assume h1,
  exact h1,
  assume h1,
  exact h1,
end

theorem TImpl : R=S → R==S :=
begin 
  assume h1,
  exact eq.subst h1 (TReflDobleIgual R),
end







