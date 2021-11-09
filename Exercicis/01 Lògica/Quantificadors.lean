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

-- Les següents proposicions venen de 
-- https://github.com/leanprover/tutorial/blob/master/04_Quantifiers_and_Equality.org

lemma E1 : (∃ (x : Ω), R) → R := 
begin
  sorry,
end

lemma E2 (x : Ω) : R → (∃ (x : Ω), R) :=
begin
  sorry,
end

lemma E3 : (∃ (x : Ω), P x ∧ R) ↔ (∃ (x : Ω), P x) ∧ R := 
begin
  sorry,
end

lemma E4 : (∃ (x : Ω), P x ∨ Q x) ↔ (∃ (x : Ω), P x) ∨ (∃ (x : Ω), Q x) := 
begin
  sorry,
end

lemma E5 : (∀ (x : Ω), P x) ↔ ¬ (∃ (x : Ω), ¬ P x) :=
begin
  sorry,
end

#check P 
lemma E6 : (∃ (x : Ω), P x) ↔ ¬ (∀ (x : Ω), ¬ P x) :=
begin
  sorry,
end

lemma E7 : (¬ ∃ (x : Ω), P x) ↔ (∀ (x : Ω), ¬ P x) :=
begin
  sorry,
end

lemma E8 : (¬ ∀ (x : Ω), P x) ↔ (∃ (x : Ω), ¬ P x) :=
begin
  sorry,
end

lemma E9 : (∀ (x : Ω), P x → R) ↔ (∃ (x : Ω), P x) → R :=
begin
  sorry,
end

lemma E10 (x : Ω) : (∃ (x : Ω), P x → R) ↔ (∀ (x : Ω), P x) → R :=
begin
  sorry,
end

lemma E11 (x : Ω) : (∃ (x : Ω), R  →  P x) ↔ (R → ∃ (x : Ω), P x):=
begin
  sorry,
end
