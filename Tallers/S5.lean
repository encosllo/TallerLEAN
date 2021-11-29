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

#check f 
#check x
#check f x 

#check funext

-- Dues aplicacions són iguals si, i només si, 
-- sobre els mateixos elements retornen les mateixes imatges
lemma L1 : f = g ↔ ∀(x:Ω), f x = g x :=
begin
  split,
  assume h1,
  intro x,
  have h2 : f x = f x, from eq.refl (f x),
  exact eq.subst h1 h2,
  --
  exact funext,
end

-- Resultat anàleg per a relacions
lemma L1b : R = S ↔ ∀(x y : Ω), R x y = S x y :=
begin
  split,
  assume h1,
  intros x y,
  have h2: R x y = R x y, from eq.refl (R x y),
  exact eq.subst h1 h2,
  --
  intro h1,
  funext x,
  funext y,
  exact h1 x y, 
end

-- Composició d'aplicacions
-- ∘ comp
#check f ∘ g 

#print function.comp
#check refl

theorem TDefComp : ∀(x:Ω), (f ∘ g) x = f (g x):=
begin
  intro x,
  refl,
end

#print function.comp.assoc
#print refl
-- La composició d'aplicacions és associativa
theorem TCompAss : f ∘ (g ∘ h) = (f ∘ g) ∘ h :=
begin
  refl,
end

-- Aplicació identitat
#check id
#print id
#check (id : Ω → Ω) 
#check f ∘ id 

#print function.comp.right_id
-- La composició d'aplicacions té a id com a neutre a dreta
theorem TCompNeutDreta : f ∘ id = f :=
begin
  refl,
end

#print function.comp.left_id
-- La composició d'aplicacions té a id com a neutre a esquerra
theorem TCompNeutEsq : id ∘ f = f :=
begin
  refl,
end

-- La identitat és idempotent
theorem TIdIdem : (id : Ω → Ω) ∘ (id : Ω → Ω) = (id : Ω → Ω) :=
begin
  refl,
end

-- Definició de l'aplicació identitat
-- Amb notació de càlcul lambda
-- https://en.wikipedia.org/wiki/Lambda_calculus
def idOmega (Ω : Type) : Ω → Ω := λ (x:Ω), x
#check idOmega 

-- La nova aplicació identitat és idempotent
-- Notem que cal especificar el tipus
theorem TidOmegaIdem  : (idOmega Ω ∘ idOmega Ω) = idOmega Ω :=
begin
  refl,
end

-- Aplicació identitat sobre naturals
def idnat : ℕ → ℕ := λ (n : ℕ), n
#check idnat

-- La nova aplicació identitat és idempotent
-- Notem que no cal especificar tipus
theorem TidnatIdem  : (idnat ∘ idnat) = idnat :=
begin
  refl,
end

-- Es presenten les següents aplicacions entre naturals
-- Aquesta part és prospectiva
-- Més avant entrarem a estudiar amb més detall els naturals
def t1 : ℕ → ℕ := λ (n : ℕ), n + 5
#check t1

theorem Taux1 : t1 3 = 8 :=
begin
  refl,
end

def t2 : ℕ → ℕ := λ (n : ℕ), n - 5
#check t2

theorem Taux2 : t2 3 = 0 :=
begin
  refl,
end

#check nat.one_ne_zero
theorem TAux : t1 ∘ t2 ≠ id :=
begin
  assume h1,
  have h2 : (t1 ∘ t2) 3 = 5, by refl,
  have h3 : id 3 = 3, by refl,
  have h4: 3 = 5, 
  exact (calc 
    3 = id 3 : h3
    ... = (t1 ∘ t2) 3 : by rw h1
    ... = 5 : h2
  ),
  have h5: 3 - 4 = 0, by refl,
  have h6: 5 - 4 = 1, by refl,
  have h7: ∀ (n: ℕ), 3 - n = 3 - n, 
  intro n, exact eq.refl (3 - n),
  have h8: ∀ (n: ℕ), 3 - n = 5 - n, 
  intro n, exact eq.subst h4 (h7 n),
  have h9: 3 - 4 = 5 - 4, exact (h8 4),
  have h10: 0 = 1, 
  exact (calc 
    0 = 3 - 4  : by rw h5
    ... = 5 - 4  : h9
    ... = 1 : h6
  ),
  have h11: 1 ≠ 0, from nat.one_ne_zero,
  have h12: 1 = 0, from eq.symm h10,
  exact h11 h12,
end

-- Demostració alternativa de TAux
#check nat.add_right_cancel
theorem TAux2 : t1 ∘ t2 ≠ id :=
begin
  assume h1,
  have h2 : (t1 ∘ t2) 3 = 5, by refl,
  have h3 : id 3 = 3, by refl,
  have h4: 3 = 5, 
  exact (calc 
    3 = id 3 : h3
    ... = (t1 ∘ t2) 3 : by rw h1
    ... = 5 : h2
  ),
  have h5: 0 + 3 = 3, by refl,
  have h6: 2 + 3 = 5, by refl,
  have h7: 0 + 3 = 2 + 3, 
  exact (calc
    0 + 3 = 3 : h5
    ... = 5 : h4
    ... = 2 + 3 : by rw h6
  ),
  have h8: 0 = 2, exact nat.add_right_cancel h7,
  have h9: 0 = 1, 
  exact (calc
    0 = 0 - 1 : by refl
    ... = 2 - 1 : by rw h8
    ... = 1 : by refl
  ),
  have h10: 1 ≠ 0, from nat.one_ne_zero,
  have h11: 1 = 0, from eq.symm h9,
  exact h10 h11,
end

-- Exemple de definició per casos
def t3 : ℤ → ℤ := λ (z:ℤ), if z < 4 then 4 else 5
#check t3 









