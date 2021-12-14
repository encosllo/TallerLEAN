-- Obre els recursos per a treballar amb conjunts
-- https://leanprover-community.github.io/mathlib_docs/data/set/basic.html

import data.set.basic data.set.function
open set 
-- open classical

-- Assumirem en tot l'exercici que 
-- Ω és un tipus que farà de contenidor
variables {I Ω Γ Δ: Type}
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

-- Negació de la injectivitat
theorem TNegInj (f: Ω → Γ) : ¬ function.injective f ↔ ∃ (x y: Ω), f x = f y ∧ x ≠ y :=
begin
  sorry,
end  

-- La composició d'injectives és injectiva
theorem TCompInj (f: Ω → Γ) (g: Γ → Δ) (h1: function.injective f) (h2: function.injective g) : function.injective (g ∘ f) :=
begin
  sorry,
end

#check function.injective f 

-- Si la composició (g∘f) és injectiva, aleshores f és injectiva
theorem TCompDInj (f: Ω → Γ) (g: Γ → Δ) (h1: function.injective (g ∘ f)) : (function.injective f) :=
begin 
  sorry,
end

-- Negació de la sobrejectivitat
theorem TNegSob (f: Ω → Γ) : ¬ function.surjective f ↔ ∃ (z: Γ), ∀ (x : Ω), f x ≠ z :=
begin
  sorry,
end  

-- La composició de sobrejectives és sobrejectiva
theorem TCompSob (f: Ω → Γ) (g: Γ → Δ) (h1: function.surjective f) (h2: function.surjective g) : function.surjective (g ∘ f) :=
begin
  sorry,
end

-- Si la composició (g∘f) és sobrejectiva, aleshores g és sobrejectiva
theorem TCompDSob (f: Ω → Γ) (g: Γ → Δ) (h1: function.surjective (g ∘ f)) : (function.surjective g) :=
begin 
  sorry,
end

-- Monos (simplificable a esquerra)
-- Si f ∘ g = f ∘ h, aleshores g = h 
def function.mono : (Ω → Γ) → Prop := λ (f : Ω → Γ), ∀ (Δ : Type), ∀ (g h: Δ → Ω), (f ∘ g = f ∘ h) → (g = h)   

-- Definim l'aplicació constant a x
-- κ kappa
-- (κ x) y = x 
def κ : Ω → (Ω → Ω) := λ (x: Ω), λ (y:Ω), x 

-- Una aplicació és mono si, i només si, és injectiva
theorem TCarMonoInj (f : Ω → Γ) : function.mono f ↔ function.injective f :=
begin
  sorry,
end

-- Epis (simplificable a dreta)
-- Si g ∘ f = h ∘ f, aleshores g = h 
def function.epi : (Ω → Γ) → Prop := λ (f : Ω → Γ), ∀ (Δ : Type), ∀ (g h: Γ → Δ), (g ∘ f = h ∘ f) → (g = h)   

-- Definim l'aplicació constant a true
def veritat : Γ → Prop := λ (x : Γ), true 
-- Definim l'aplicació noigual que depén d'una variable x
def noigual : Γ → (Γ → Prop) := λ (x y : Γ), ¬ y = x 

-- Una aplicació és epi si, i només si, és sobrejectiva
theorem TCarEpiSob (f : Ω → Γ) : function.epi f ↔ function.surjective f :=
begin
  sorry,
end
