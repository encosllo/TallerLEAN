-- Obre els recursos per a treballar amb conjunts
-- https://leanprover-community.github.io/mathlib_docs/data/set/basic.html

import data.set.basic data.set.function
open set 
-- open classical

-- Assumirem en tot l'exercici que 
-- Ω és un tipus que farà de contenidor
variables {I Ω Γ: Type}
-- a b c x y z seran elements de tipus Ω 
variables a b c x y z : Ω  
-- a b c x y z seran elements de tipus Ω 
variables A B C X Y Z : set Ω    
-- P és una proposició sobre elements de tipus Ω
variable P : Ω → Prop 
-- famílies de conjunts de tipus Ω
variable 𝔸 : I → set Ω
-- R S T relacions sobre Ω
variables R S T : Ω → Ω → Prop  
-- funcions sobre elements de tipus Ω
variables f g : Ω → Ω

-- En aquesta sessió treballarem amb aplicacions
-- https://leanprover-community.github.io/mathematics_in_lean/sets_functions_and_relations.html#functions

#print function.injective 
#check function.injective f

#print function.surjective
#check function.surjective f

#print function.bijective
#check function.bijective f

-- La identitat és injectiva
theorem TIdInj : function.injective (id: Ω → Ω) :=
begin
  intros x y,
  assume h1,
  exact (calc
    x   = id x  : by refl
    ... = id y  : h1
    ... = y     : by refl
  ),
end

-- La identitat és sobrejectiva
theorem TIdSob : function.surjective (id: Ω → Ω) :=
begin
  intro x,
  have h1: id x = x, by refl,
  exact exists.intro x h1,
end

-- La identitat és bijectiva
theorem TIdBij : function.bijective (id: Ω → Ω) :=
begin
  exact and.intro TIdInj TIdSob,
end

-- Nucli d'una aplicació
variable h : Ω → Γ
def Ker : (Ω → Γ) → (Ω → Ω → Prop) := λ (h: Ω → Γ), λ (x y : Ω), h x = h y

#check Ker h

theorem TKerRefl : reflexive (Ker h) :=
begin
  intro x,
  exact eq.refl (h x),
end

theorem TKerSym : symmetric (Ker h) :=
begin
  intros x y,
  assume h1,
  exact eq.symm h1,
end

theorem TKerTrans : transitive (Ker h) :=
begin
  intros x y z,
  assume h1,
  assume h2,
  exact eq.trans h1 h2,
end

#print equivalence
theorem TKerEqv : equivalence (Ker h) :=
begin
  exact and.intro (TKerRefl h) (and.intro (TKerSym h) (TKerTrans h)),
end
