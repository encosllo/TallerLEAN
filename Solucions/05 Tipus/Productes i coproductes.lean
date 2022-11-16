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
split,
--
assume h1,
apply and.intro,
have h2: (a,b).fst = (a',b').fst,
exact congr_arg prod.fst h1,
exact h2,
have h2: (a,b).snd = (a',b').snd,
exact congr_arg prod.snd h1,
exact h2,
--
assume h1,
have h2: a=a', 
exact and.elim_left h1,
have h3: b=b', 
exact and.elim_right h1,
exact congr (congr_arg prod.mk h2) h3,
end

-- Definició de la primera projecció
def fst : A×B → A :=
λ z, z.fst

-- Definició de la segona projecció
def snd : A×B → B :=
λ z, z.snd

-- Definició del producte de dues aplicacions
def prd (A B C : Type) (f : C → A) (g : C → B) : C → A × B :=
λ c, (f c, g c)

-- Propietat Universal del Producte
theorem PUProd (A B C : Type) (f : C → A) (g : C → B) : 
∃! (h : C → A × B), fst A B ∘ h = f ∧ snd A B ∘ h = g :=
begin
use prd A B C f g,
apply and.intro,
--
apply and.intro,
refl,
refl,
--
intros j h1,
have h2: fst A B ∘ j = f,
exact and.elim_left h1,
have h3: snd A B ∘ j = g,
exact and.elim_right h1,
funext c,
--
have h4: (fst A B ∘ j) c = f c,
exact congr_fun h2 c,
have h5: (j c).fst = (fst A B ∘ j) c,
refl,
have h6: (j c).fst = f c,
exact (rfl.congr h4).mp h5,
--
have h7: (snd A B ∘ j) c = g c,
exact congr_fun h3 c,
have h8: (j c).snd = (snd A B ∘ j) c,
refl,
have h9: (j c).snd = g c,
exact (rfl.congr h7).mp h8,
--
have h10 : (prd A B C f g c).fst = f c,
refl,
have h11 : (prd A B C f g c).snd = g c,
refl,
--
have h12 : (j c).fst = (prd A B C f g c).fst,
exact (rfl.congr (eq.symm h10)).mp h6,
--
have h13 : (j c).snd = (prd A B C f g c).snd,
exact (rfl.congr (eq.symm h11)).mp h9,
--
exact prod.ext h12 h13,
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
λ a, sum.inl a 

-- Definició de la segona projecció
def inr : B → A ⊕ B :=
λ b, sum.inr b

-- Definició del coproducte de dues aplicacions
def cprd (A B C : Type) (f : A → C) (g : B → C) : A ⊕ B → C :=
begin
assume z,
cases z with za zb,
exact f za,
exact g zb,
end

-- Propietat Universal del Coproducte
theorem PUCprod (A B C : Type) (f : A → C) (g : B → C) : 
∃! (h : A ⊕ B → C), h ∘ inl A B = f ∧ h ∘ inr A B = g :=
begin
use cprd A B C f g,
apply and.intro,
--
apply and.intro,
refl,
refl,
--
intros j h1,
have h2: j ∘ inl A B = f,
exact and.elim_left h1,
have h3: j ∘ inr A B = g,
exact and.elim_right h1,
funext c,
--
cases c with ca cb,
--
have h4: (j ∘ inl A B) ca = f ca,
exact congr_fun h2 ca,
have h5: (j ∘ inl A B) ca = j (sum.inl ca),
refl,
have h6: j (sum.inl ca) = f ca,
exact (rfl.congr h4).mp (eq.symm h5),
rw h6,
refl,
--
have h4: (j ∘ inr A B) cb = g cb,
exact congr_fun h3 cb,
have h5: (j ∘ inr A B) cb = j (sum.inr cb),
refl,
have h6: j (sum.inr cb) = g cb,
exact (rfl.congr h4).mp (eq.symm h5),
rw h6,
refl,
end

