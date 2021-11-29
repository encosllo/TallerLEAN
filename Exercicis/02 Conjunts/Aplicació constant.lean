-- Obre els recursos per a treballar amb conjunts
-- https://leanprover-community.github.io/mathlib_docs/data/set/basic.html

import data.set.basic  
open set nat
-- open classical

-- Assumirem en tot l'exercici que 
-- Ω és un tipus que farà de contenidor
variables {I Ω : Type}
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
variables f g h : Ω → Ω

-- En aquesta sessió treballarem amb aplicacions
-- https://leanprover-community.github.io/mathematics_in_lean/sets_functions_and_relations.html#functions

-- Definim les aplicacions constants
-- κ  kappa 

def κ : Ω → (Ω → Ω) := λ (x:Ω), λ (z:Ω), x

-- κ kappa és un operador que agafa una variable (z:Ω)
-- i retorna una aplicació κ x d'Ω en Ω, 
-- que a cada (z:Ω), li fa correspondre, x

#check κ
#check κ x

-- Les aplicacions constants són zeros a esquerra
theorem TConsZEsq : (κ x) ∘ (κ y) = κ x :=
begin
  sorry,
end

-- En particular les aplicacions constants són idempotents
theorem TConsId : (κ x) ∘ (κ x) = κ x :=
begin
  sorry,
end

-- La composició d'aplicacions constants amb 
-- qualsevol aplicació retorna aplicacions constants

-- A esquerra
theorem TConsCompEsq : f ∘ (κ x) = κ (f x) :=
begin
  sorry,
end

-- A dreta
theorem TConsCompD : (κ x) ∘ f = κ x :=
begin
  sorry,
end