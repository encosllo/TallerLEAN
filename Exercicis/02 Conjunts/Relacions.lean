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

----------------
----------------
----------------

-- Definim la relació diagonal
-- Diagonal Ω = {(x,y) ∈ Ω × Ω ∣ x = y}
def Diagonal (Ω : Type) : Ω → Ω → Prop := λ x, λ y, x = y

#check Diagonal 
#check Diagonal Ω

-- La Diagonal és reflexiva
theorem TDiagRefl : reflexive (Diagonal Ω) :=
begin
  sorry,
end

-- La Diagonal és simètrica
theorem TDiagSim : symmetric (Diagonal Ω) :=
begin
  sorry,
end

-- La Diagonal és transitiva
theorem TDiagTrans : transitive (Diagonal Ω) :=
begin
  sorry, 
end

-- La Diagonal és una relació d'equivalència
theorem TDiagEq : equivalence (Diagonal Ω) :=
begin
  sorry,
end

----------------
----------------
----------------

-- Definim la relació codiagonal
-- Codiagonal Ω = {(x,y) ∈ Ω × Ω ∣ x, y ∈ Ω}
def Codiagonal (Ω : Type) : Ω → Ω → Prop := λ x, λ y, true

#check true.intro
#check Codiagonal 
#check Codiagonal Ω

-- La Codiagonal és reflexiva
theorem TCoDiagRefl : reflexive (Codiagonal Ω) :=
begin
  sorry,
end

-- La Codiagonal és simètrica
theorem TCoDiagSim : symmetric (Codiagonal Ω) :=
begin
  sorry,
end

-- La Codiagonal és transitiva
theorem TCoDiagTrans : transitive (Codiagonal Ω) :=
begin
  sorry,
end

-- La Codiagonal és una relació d'equivalència
theorem TCoDiagEq : equivalence (Codiagonal Ω) :=
begin
  sorry,
end

----------------
----------------
----------------

-- Definim la relació d'inclusió i d'igualtat entre relacions
def inclosa (R S: Ω → Ω → Prop) : Prop := ∀ (x y : Ω), R x y → S x y
local infix ⊆ := inclosa
def igual (R S: Ω → Ω → Prop) : Prop := ∀ (x y : Ω), R x y ↔ S x y
local infix == := igual

#check R ⊆ S 
#check R == S 


-- La inclusió de relacions és reflexiva
theorem TIncRelRefl : R ⊆ R :=
begin
  sorry,
end

-- La inclusió de relacions és antisimètrica
theorem TIncRelAntiSim (h1: R ⊆ S) (h2: S ⊆ R) : R == S :=
begin
  sorry,
end

-- La inclusió de relacions és transitiva
theorem TIncRelTrans (h1: R ⊆ S) (h2: S ⊆ T) : R ⊆ T :=
begin
  sorry,
end

-- La igualtat és reflexiva
theorem TEqRefl : R == R :=
begin
  sorry,
end

-- La igualtat és simètrica
theorem TEqSim (h1: R == S) : S == R :=
begin
  sorry,
end

-- La igualtat és transitiva
theorem TEqTrans (h1: R == S) (h2: S == T) : R == T :=
begin
  sorry,
end

-- Una relació és reflexiva si, i només si, té a la Diagonal inclosa
theorem TReflDiag : reflexive R ↔ Diagonal Ω ⊆ R :=
begin
  sorry,
end

-- Tota relació està per davall de la Codiagonal
theorem TCoDiagMax : R ⊆ Codiagonal Ω := 
begin
  sorry,
end

----------------
----------------
----------------

-- Definim la inversa d'una relació
def inv (R: Ω → Ω → Prop) : Ω → Ω → Prop := λ (x y : Ω), R y x

-- La inversa de la inversa d'una relació és la mateixa relació
theorem TInvInv : inv (inv R) == R :=
begin
  sorry,
end

-- Una relació és simètrica si, i només si, té la seua inversa inclosa
theorem TSimInv : symmetric R ↔ (inv R) ⊆ R :=
begin
  sorry,
end

----------------
----------------
----------------

-- Definim la composició de relacions
def comp (R S: Ω → Ω → Prop) : Ω → Ω → Prop := λ x, λ y, ∃ (z : Ω), R x z ∧ S z y
local infix ∘ := comp 
-- ∘ comp

#check R ∘ S

-- La composició de relacions és associativa
theorem TCompAss : R ∘ (S ∘ T) == (R ∘ S) ∘ T :=
begin
  sorry,
end

-- La diagonal fa de neutre a esquerra per a la composició
theorem TDiagNeutEsq : R ∘ (Diagonal Ω) == R :=
begin
  sorry, 
end 

-- La diagonal fa de neutre a dreta per a la composició
theorem TDiagNeutDrt : (Diagonal Ω) ∘ R == R :=
begin
  sorry,
end 

-- Una relació és transitiva si, i només si, té el seu quadrat inclós
theorem TTransComp : transitive R ↔ R ∘ R ⊆ R :=
begin
  sorry,
end
