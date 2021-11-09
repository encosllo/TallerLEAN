open classical
-- Ω és un tipus que farà de contenidor
variable (Ω : Type)
variables x y z : Ω
-- P Q R seran proposicions sobre Ω
variables P Q : Ω → Prop
variables R : Prop

-- ∀  forall
-- ∃  exists
-- Tots els quantificadors necessiten dir sobre què quantifiquen

-- Eliminació per a tot
lemma L1 (h1: ∀(x : Ω), P x) (a : Ω) : P a :=
begin
  exact h1 a,
end  

-- Introducció del per a tot
lemma L2 (h1: ∀(x : Ω), P x → Q x) (h2: ∀(x : Ω), P x) : ∀(x : Ω), Q x :=
begin
  intro z,
  have h3: P z, from h2 z,
  have h4: P z → Q z, from h1 z,
  exact h4 h3,
end  

#check exists.elim
-- Eliminació de l'existencial
lemma L3 (h1: ∀(x : Ω), P x → R) (h2: ∃(x : Ω), P x) : R :=
begin
  apply exists.elim,
  exact h2,
  exact h1,
  --exact (exists.elim h2) h1,
end 

-- Eliminació de l'existencial, emprant cases
lemma L4 (h1: ∀(x : Ω), P x → R) (h2: ∃(x : Ω), P x) : R :=
begin
  cases h2 with x h2,
  have h3: P x → R, from h1 x,
  exact h3 h2,
end 

#check exists.intro
-- Introducció de l'existencial
lemma L5 (h1: ∀(x : Ω), P x) (a : Ω) : ∃ (x : Ω), P x :=
begin
  have h2: P a, exact h1 a,
  exact exists.intro a h2,
end  

-- Introducció de l'existencial
lemma L6 (h1: ∀(x : Ω), P x) (a : Ω) : ∃ (x : Ω), P x :=
begin
  apply exists.intro,
  apply h1,
  exact a,
end 
