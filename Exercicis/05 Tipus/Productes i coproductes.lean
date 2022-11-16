import tactic
open classical

variables A B : Type
variable a : A 
variable b : B 

/-
#check A×B
#print prod 
#check prod A B 
#check (a,b)
#check prod.fst
#check prod.snd
-/

-- En el producte dos tuples són iguals 
-- si, i només si, ho són component a component
theorem E (A B: Type) (a a' : A) (b b' : B) : (a,b)=(a',b') ↔ (a=a') ∧ (b=b') :=
begin
sorry,
end

-- Definició de la primera projecció
def fst : A×B → A :=
sorry,

-- Definició de la segona projecció
def snd : A×B → B :=
sorry,

-- Definició del producte de dues aplicacions
def prd (A B C : Type) (f : C → A) (g : C → B) : C → A × B :=
sorry,

-- Propietat Universal del Producte
theorem PUProd (A B C : Type) (f : C → A) (g : C → B) : 
∃! (h : C → A × B), fst A B ∘ h = f ∧ snd A B ∘ h = g :=
begin
sorry,
end

------

/-
#check A ⊕ B
#print sum 
#check sum A B 
#check sum.inl
#check sum.inr
-/

-- Definició de la primera inclusió
def inl : A → A ⊕ B :=
sorry,

-- Definició de la segona projecció
def inr : B → A ⊕ B :=
sorry,

-- Definició del coproducte de dues aplicacions
def cprd (A B C : Type) (f : A → C) (g : B → C) : A ⊕ B → C :=
sorry,

-- Propietat Universal del Coproducte
theorem PUCprod (A B C : Type) (f : A → C) (g : B → C) : 
∃! (h : A ⊕ B → C), h ∘ inl A B = f ∧ h ∘ inr A B = g :=
sorry,
end

