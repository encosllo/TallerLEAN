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

-- En aquesta sessió treballarem amb quocients
-- https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#quotients
-- https://xenaproject.wordpress.com/maths-in-lean-quotients-and-equivalence-classes/

-- Quot agafa relacions i torna un nou tipus
#check quot 

-- Per a R relació
-- R: Ω → Ω → Prop
#check quot R 

-- Formació de classes
#check quot.mk
-- Si x és un objecte de tipus Ω
-- x : Ω
-- La seua classe en quot R ve donada per 
-- Lean entén la mínima relació d'equivalència generada per R
#check quot.mk R x 

#check eqv_gen R 
#print eqv_gen 

-- Quot.ind és un axioma que ens diu que si una proposició β
-- es demostra per a tot element de la forma classe 
-- d'un element, aleshores la proposició és certa per a tot
-- objecte del tipus quot 
#check quot.ind
/- Esta és la definició
axiom quot.ind :
  ∀ {α : Sort u} {r : α → α → Prop} {β : quot r → Prop},
    (∀ a, β (quot.mk r a)) → ∀ (q : quot r), β q
-/

-- Donada una aplicació f : α → β i una demostració
-- de que si tots els elements a b : α que estiguen
-- R-relacionats satisfan que f a = f b, aleshores
-- existeix una aplicació del quocient en β
-- És la forma de comprovar que l'aplicació està ben definida
#check quot.lift
/- Esta és la definició
constant quot.lift :
  Π {α : Sort u} {r : α → α → Prop} {β : Sort u} (f : α → β),
    (∀ a b, r a b → f a = f b) → quot r → β
-/

#check quot.eqv_gen_sound
#check eqv_gen.rel x y 

theorem TClassR (R : Ω → Ω → Prop) (x y : Ω) (h1: R x y) : quot.mk R x = quot.mk R y :=
begin
  have h2: eqv_gen R x y, exact eqv_gen.rel x y h1,
  exact quot.eqv_gen_sound h2,
end 

theorem TREqv (R: Ω → Ω → Prop) (h1: equivalence R) : eqv_gen R = R :=
begin
  have t1: reflexive R, exact and.elim_left h1,
  have t2: symmetric R, exact and.elim_left (and.elim_right h1),
  have t3: transitive R, exact and.elim_right (and.elim_right h1),
  funext x y,
  have h2: eqv_gen R x y ↔ R x y,
  split,
  --
  assume h3,
  /-
  A continuació anem a fer la primera demostració per inducció
  Notem que h3 ens diu que x i y estan relacionats per a eqv_gen R
  Com eqv_gen és un operador inductiu, podríem fer cassos sobre h3
  però açò començaria a obrir-nos cassos indefinidament. 
  En compte de fer cassos, fem inducció
  Aleshores, cada vegada que el cas ens done com a hipòtesi algun estament
  de la forma eqv_gen R x y, ens inclourà també el que volem demostrar com a 
  hipòtesi (el pas inductiu)
  -/
  induction h3 with c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15,
  exact c3,
  exact t1 c4,
  exact t2 c8,
  exact t3 c14 c15,
  --
  assume h3,
  exact eqv_gen.rel x y h3,
  --
  exact (calc 
  eqv_gen R x y = R x y : by rw h2
  ),
end

theorem TREqv2 (R: Ω → Ω → Prop) (h1: equivalence R) (x y : Ω) : quot.mk R x = quot.mk R y ↔ R x y :=
begin
  split,
  -- Primera implicació
  assume h2,
  have h3: eqv_gen R x y, exact iff.elim_left quot.eq h2,
  have h4: eqv_gen R = R, exact (TREqv R) h1,
  exact eq.subst h4 h3,
  -- Segona implicació
  assume h2,
  have h3: eqv_gen R x y, exact eqv_gen.rel x y h2,
  exact iff.elim_right quot.eq h3,
end  


