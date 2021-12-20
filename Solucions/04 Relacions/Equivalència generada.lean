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
  intros x y,
  assume h1,
  exact h1,
end

-- Antisimètrica
theorem TMenor.antisymm : R ⊆ S ∧ S ⊆ R → R = S  :=
begin
  assume h1,
  have h2: R ⊆ S, exact and.elim_left h1,
  have h3: S ⊆ R, exact and.elim_right h1,
  have h4: ∀ (x y : Ω), R x y ↔ S x y,
  intros x y,
  split,
  -- Cas 1
  assume h4,
  exact h2 x y h4,
  -- Cas 2
  assume h4,
  exact h3 x y h4,
  funext x y,
  have h5: R x y ↔ S x y, exact h4 x y,
  exact (calc
    R x y = S x y : by rw h5
  ), 
end

-- Transitiva
theorem TMenor.trans : R ⊆ S ∧ S ⊆ T → R ⊆ T :=
begin
  assume h1,
  have h2: R ⊆ S, exact and.elim_left h1,
  have h3: S ⊆ T, exact and.elim_right h1,
  intros x y,
  assume h4,
  have h5: S x y, exact h2 x y h4,
  exact h3 x y h5,
end

-- El primer resultat ens mostra que l'equivalència generada
-- per una relació R conté a R
#check eqv_gen.rel

theorem TEqv.rel : R ⊆ eqv_gen R :=
begin
  intros x y,
  assume h1,
  exact eqv_gen.rel x y h1, 
end

-- El segon resultat ens mostra que l'equivalència generada
-- és una relació d'equivalència

-- L'equivalència generada és reflexiva
#check eqv_gen.refl

theorem TEqv.refl : reflexive (eqv_gen R) :=
begin
  intro x,
  exact eqv_gen.refl x,
end

-- L'equivalència generada és simètrica
#check eqv_gen.symm

theorem TEqv.symm : symmetric (eqv_gen R) :=
begin
  intros x y,
  assume h1,
  exact eqv_gen.symm x y h1,
end

-- L'equivalència generada és transitiva
#check eqv_gen.trans

theorem TEqv.trans : transitive (eqv_gen R) :=
begin
  intros x y z,
  assume h1 h2,
  exact eqv_gen.trans x y z h1 h2,
end

-- L'equivalència generada és una equivalència
theorem TEqv.eqv : equivalence (eqv_gen R) :=
begin
  exact and.intro (TEqv.refl R) (and.intro (TEqv.symm R) (TEqv.trans R)),
end

-- El tercer resultat que demostrarem és que 
-- l'equivalència generada per R és la menor 
-- equivalència que conté a R

theorem TEqv.menor : (equivalence S) ∧ (R ⊆ S) → (eqv_gen R ⊆ S) :=
begin
  assume h1,
  have h2: equivalence S, exact and.elim_left h1,
  have h3: R ⊆ S, exact and.elim_right h1,
  have h4: reflexive S, exact and.elim_left h2,
  have h5: symmetric S, exact and.elim_left (and.elim_right h2),
  have h6: transitive S, exact and.elim_right (and.elim_right h2),
  --
  intros x y,
  assume h7,
  induction h7 with d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15,
  exact h3 d1 d2 d3,
  exact h4 d4,
  exact h5 d8,
  exact h6 d14 d15,
end

-- A continuació demostrarem que l'equivalència generada 
-- per una relació d'equivalència és la pròpia relació d'equivalència

theorem TEqv.closed (h1: equivalence R) : eqv_gen R = R :=
begin
  have h2: R ⊆ R, exact TMenor.refl R,
  have h3: eqv_gen R ⊆ R, exact TEqv.menor R R (and.intro h1 h2),
  have h4: R ⊆ eqv_gen R, exact TEqv.rel R,
  exact TMenor.antisymm (eqv_gen R) R (and.intro h3 h4),
end 

-----------------------
-- Operador clausura --
-----------------------

-- L'operador és extensiu : per a tota relació R, R ⊆ eqv_gen R 
theorem TEqv.extensiu : R ⊆ eqv_gen R :=
begin
  exact TEqv.rel R, 
end

-- L'operador és monòton : per a tot parell de relacions R i S
-- tals que R ⊆ S, aleshores eqv_gen R ⊆ eqv_gen S
theorem TEqv.monoton (h1: R ⊆ S) : eqv_gen R ⊆ eqv_gen S :=
begin
  have h2: equivalence (eqv_gen S), exact TEqv.eqv S,
  have h3: S ⊆ eqv_gen S, exact TEqv.rel S,
  have h4: R ⊆ eqv_gen S, exact TMenor.trans R S (eqv_gen S) (and.intro h1 h3),
  exact TEqv.menor R (eqv_gen S) (and.intro h2 h4),  
end

-- L'operador és idempotent : per a tota relació R, eqv_gen (eqv_gen R) = eqv_gen R
theorem TEqv.idempotent : eqv_gen (eqv_gen R) = eqv_gen R :=
begin
  have h1: equivalence (eqv_gen R), exact TEqv.eqv R,
  exact TEqv.closed (eqv_gen R) h1,
end










