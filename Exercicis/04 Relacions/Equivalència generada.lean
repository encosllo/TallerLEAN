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

/- 
En aquest document treballarem les propietats bàsiques 
de l'operador d'equivalència generada
-/

#check eqv_gen
#print eqv_gen

-- Anem a definir-nos una relació entre relacions
-- Aquesta relació serà un ordre. 
-- Per a relacions R i S sobre Ω, direm que R ≤ S
-- si per a tot x y de tipus Ω,
-- la condició R x y implica que S x y

def menor : (Ω → Ω → Prop) → (Ω → Ω → Prop) → Prop := λ (R S: Ω → Ω → Prop), ∀ (x y : Ω), R x y → S x y
infixr ⊆ := menor

-- Anem a demostrar en primer lloc que ⊆ 
-- és un ordre 

-- Reflexiva
theorem TMenor.refl : R ⊆ R :=
begin
  sorry,
end

-- Antisimètrica
theorem TMenor.antisymm : R ⊆ S ∧ S ⊆ R → R = S  :=
begin
  sorry,
end

-- Transitiva
theorem TMenor.trans : R ⊆ S ∧ S ⊆ T → R ⊆ T :=
begin
  sorry,
end

-- El primer resultat ens mostra que l'equivalència generada
-- per una relació R conté a R
#check eqv_gen.rel

theorem TEqv.rel : R ⊆ eqv_gen R :=
begin
  sorry,
end

-- El segon resultat ens mostra que l'equivalència generada
-- és una relació d'equivalència

-- L'equivalència generada és reflexiva
#check eqv_gen.refl

theorem TEqv.refl : reflexive (eqv_gen R) :=
begin
  sorry,
end

-- L'equivalència generada és simètrica
#check eqv_gen.symm

theorem TEqv.symm : symmetric (eqv_gen R) :=
begin
  sorry,
end

-- L'equivalència generada és transitiva
#check eqv_gen.trans

theorem TEqv.trans : transitive (eqv_gen R) :=
begin
  sorry,
end

-- L'equivalència generada és una equivalència
theorem TEqv.eqv : equivalence (eqv_gen R) :=
begin
  sorry,
end

-- El tercer resultat que demostrarem és que 
-- l'equivalència generada per R és la menor 
-- equivalència que conté a R

theorem TEqv.menor : (equivalence S) ∧ (R ⊆ S) → (eqv_gen R ⊆ S) :=
begin
  sorry,
end

-- A continuació demostrarem que l'equivalència generada 
-- per una relació d'equivalència és la pròpia relació d'equivalència

theorem TEqv.closed (h1: equivalence R) : eqv_gen R = R :=
begin
  sorry,
end 

-----------------------
-- Operador clausura --
-----------------------

-- L'operador és extensiu : per a tota relació R, R ⊆ eqv_gen R 
theorem TEqv.extensiu : R ⊆ eqv_gen R :=
begin
  sorry,
end

-- L'operador és monòton : per a tot parell de relacions R i S
-- tals que R ⊆ S, aleshores eqv_gen R ⊆ eqv_gen S
theorem TEqv.monoton (h1: R ⊆ S) : eqv_gen R ⊆ eqv_gen S :=
begin
  sorry, 
end

-- L'operador és idempotent : per a tota relació R, eqv_gen (eqv_gen R) = eqv_gen R
theorem TEqv.idempotent : eqv_gen (eqv_gen R) = eqv_gen R :=
begin
  sorry,
end










