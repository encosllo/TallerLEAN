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
  intro x,
  have h1: x = x, from eq.refl x,
  exact h1,
end

-- La Diagonal és simètrica
theorem TDiagSim : symmetric (Diagonal Ω) :=
begin
  intros x y,
  assume h1,
  have h2: x = y, exact h1,
  have h3: y = x, from eq.symm h2,
  exact h3,
end

-- La Diagonal és transitiva
theorem TDiagTrans : transitive (Diagonal Ω) :=
begin
  intros x y z,
  assume h1,
  assume h2,
  have h3: x = y, exact h1,
  have h4: y = z, exact h2,
  have h5: x = z, from eq.trans h3 h4,
  exact h5, 
end

-- La Diagonal és una relació d'equivalència
theorem TDiagEq : equivalence (Diagonal Ω) :=
begin
  exact (and.intro TDiagRefl (and.intro TDiagSim TDiagTrans)),
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
  intro x,
  exact true.intro,
end

-- La Codiagonal és simètrica
theorem TCoDiagSim : symmetric (Codiagonal Ω) :=
begin
  intros x y,
  assume h1,
  exact true.intro,
end

-- La Codiagonal és transitiva
theorem TCoDiagTrans : transitive (Codiagonal Ω) :=
begin
  intros x y z,
  assume h1,
  assume h2,
  exact true.intro,
end

-- La Codiagonal és una relació d'equivalència
theorem TCoDiagEq : equivalence (Codiagonal Ω) :=
begin
  exact (and.intro TCoDiagRefl (and.intro TCoDiagSim TCoDiagTrans)),
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
  intros x y,
  assume h1,
  exact h1,
end

-- La inclusió de relacions és antisimètrica
theorem TIncRelAntiSim (h1: R ⊆ S) (h2: S ⊆ R) : R == S :=
begin
  intros x y,
  split,
  --
  assume h3,
  exact h1 x y h3,
  --
  assume h3,
  exact h2 x y h3,
end

-- La inclusió de relacions és transitiva
theorem TIncRelTrans (h1: R ⊆ S) (h2: S ⊆ T) : R ⊆ T :=
begin
  intros x y,
  assume h3,
  have h4: S x y, from h1 x y h3, 
  exact h2 x y h4,
end

-- La igualtat és reflexiva
theorem TEqRefl : R == R :=
begin
  intros x y,
  split,
  --
  assume h1,
  exact h1,
  --
  assume h1,
  exact h1,
end

-- La igualtat és simètrica
theorem TEqSim (h1: R == S) : S == R :=
begin
  have h2: ∀ (x y : Ω), R x y ↔ S x y, from h1,
  have h3: ∀ (x y : Ω), S x y ↔ R x y, 
  intros x y,
  split,
  --
  assume h1,
  exact iff.elim_right (h2 x y) h1,
  -- 
  assume h1,
  exact iff.elim_left (h2 x y) h1,
  --
  exact h3,
end

-- La igualtat és transitiva
theorem TEqTrans (h1: R == S) (h2: S == T) : R == T :=
begin
  have h3: ∀ (x y : Ω), R x y ↔ S x y, from h1,
  have h4: ∀ (x y : Ω), S x y ↔ T x y, from h2,
  have h5: ∀ (x y : Ω), R x y ↔ T x y, 
  intros x y,
  split,
  --
  assume h5,
  have h6: S x y, from iff.elim_left (h3 x y) h5, 
  exact iff.elim_left (h4 x y) h6,
  --
  assume h5,
  have h6: S x y, from iff.elim_right (h4 x y) h5, 
  exact iff.elim_right (h3 x y) h6,
  --
  exact h5,
end

-- Una relació és reflexiva si, i només si, té a la Diagonal inclosa
theorem TReflDiag : reflexive R ↔ Diagonal Ω ⊆ R :=
begin
  split,
  --
  assume h1,
  intros x y,
  assume h2,
  have h3: x = y, exact h2,
  have h4: R x x, from h1 x,
  exact eq.subst h3 h4,
  --
  assume h1,
  intro x,
  have h2: x = x, from eq.refl x,
  have h3: Diagonal Ω x x, from h2,
  exact h1 x x h3,
end

-- Tota relació està per davall de la Codiagonal
theorem TCoDiagMax : R ⊆ Codiagonal Ω := 
begin
  intros x y,
  assume h1,
  exact true.intro,
end

----------------
----------------
----------------

-- Definim la inversa d'una relació
def inv (R: Ω → Ω → Prop) : Ω → Ω → Prop := λ (x y : Ω), R y x

-- La inversa de la inversa d'una relació és la mateixa relació
theorem TInvInv : inv (inv R) == R :=
begin
  intros x y,
  split,
  --
  assume h1,
  have h2: (inv R) y x, from h1,
  exact h2,
  --
  assume h1,
  have h2: (inv R) y x, from h1,
  exact h2,
end

-- Una relació és simètrica si, i només si, té la seua inversa inclosa
theorem TSimInv : symmetric R ↔ (inv R) ⊆ R :=
begin
  split,
  -- 
  assume h1,
  intros x y,
  assume h2,
  have h3: R y x, from h2,
  exact h1 h3,
  --
  assume h1,
  intros x y,
  assume h2,
  have h3: (inv R) y x, from h2,
  exact h1 y x h3,
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
  intros x y,
  split,
  --
  assume h1,
  cases h1 with z h1,
  have h2: R x z, from and.elim_left h1,
  have h3: (S ∘ T) z y, from and.elim_right h1,
  cases h3 with t h3,
  have h4: S z t, from and.elim_left h3,
  have h5: T t y, from and.elim_right h3, 
  -- 
  have h6: (R∘S) x t, from exists.intro z (and.intro h2 h4),
  exact exists.intro t (and.intro h6 h5),
  --
  --
  assume h1,
  cases h1 with z h1,
  have h2: (R ∘ S) x z, from and.elim_left h1,
  have h3: T z y, from and.elim_right h1,
  cases h2 with t h2,
  have h4: R x t, from and.elim_left h2,
  have h5: S t z, from and.elim_right h2,
  --
  have h6: (S ∘ T) t y, from exists.intro z (and.intro h5 h3),
  exact exists.intro t (and.intro h4 h6),
end

-- La diagonal fa de neutre a esquerra per a la composició
theorem TDiagNeutEsq : R ∘ (Diagonal Ω) == R :=
begin
  intros x y,
  split,
  --
  assume h1,
  cases h1 with z h1,
  have h2: R x z, from and.elim_left h1,
  have h3: Diagonal Ω z y, from and.elim_right h1,
  have h4: z = y, from h3,
  exact eq.subst h4 h2,
  --
  assume h1,
  have h2: y = y, from eq.refl y,
  have h3: Diagonal Ω y y, from h2,
  exact exists.intro y (and.intro h1 h3), 
end 

-- La diagonal fa de neutre a dreta per a la composició
theorem TDiagNeutDrt : (Diagonal Ω) ∘ R == R :=
begin
  intros x y,
  split,
  --
  assume h1,
  cases h1 with z h1,
  have h2: Diagonal Ω x z, from and.elim_left h1,
  have h3: R z y, from and.elim_right h1,
  have h4: z = x, from eq.symm h2,
  exact eq.subst h4 h3,
  --
  assume h1,
  have h2: x = x, from eq.refl x,
  have h3: Diagonal Ω x x, from h2,
  exact exists.intro x (and.intro h3 h1),
end 

-- Una relació és transitiva si, i només si, té el seu quadrat inclós
theorem TTransComp : transitive R ↔ R ∘ R ⊆ R :=
begin
  split,
  --
  assume h1,
  intros x y,
  assume h2,
  cases h2 with z h2,
  have h3: R x z, from and.elim_left h2,
  have h4: R z y, from and.elim_right h2,
  exact h1 h3 h4,
  --
  assume h1,
  intros x y z,
  assume h2,
  assume h3,
  have h4: (R∘R) x z, from exists.intro y (and.intro h2 h3),
  exact h1 x z h4, 
end
