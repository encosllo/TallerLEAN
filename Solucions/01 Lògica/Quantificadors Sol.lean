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
  intro h1,
  cases h1 with x h2,
  exact h2,
end

lemma E2 (x : Ω) : R → (∃ (x : Ω), R) :=
begin
  assume h1,
  apply exists.intro,
  exact x,
  exact h1,
end

lemma E3 : (∃ (x : Ω), P x ∧ R) ↔ (∃ (x : Ω), P x) ∧ R := 
begin
  split,
  assume h1,
  cases h1 with x h2,
  have h3: P x, from and.elim_left h2,
  have h4 : ∃ (x : Ω), P x, apply exists.intro, exact h3,
  have h5: R, from and.elim_right h2,
  exact and.intro h4 h5,
  assume h1,
  have h2 : ∃ (x : Ω), P x, from and.elim_left h1,
  have h3 : R, from and.elim_right h1,
  cases h2 with x h2,
  have h4: P x ∧ R, from and.intro h2 h3,
  exact exists.intro x h4,
end

lemma E4 : (∃ (x : Ω), P x ∨ Q x) ↔ (∃ (x : Ω), P x) ∨ (∃ (x : Ω), Q x) := 
begin
  split,
  -- Implicació 1
  assume h1,
  cases h1 with x h1,
  cases h1,
  have h2: ∃ (x : Ω), P x, from exists.intro x h1,
  exact or.inl h2,
  have h2: ∃ (x : Ω), Q x, from exists.intro x h1,
  exact or.inr h2,
  -- Implicació 2
  assume h1,
  cases h1,
  cases h1 with x h1,
  have h2: P x ∨ Q x, from or.inl h1,
  exact exists.intro x h2,
  cases h1 with x h1,
  have h2: P x ∨ Q x, from or.inr h1,
  exact exists.intro x h2,
end

lemma E5 : (∀ (x : Ω), P x) ↔ ¬ (∃ (x : Ω), ¬ P x) :=
begin
  split,
  -- Implicació 1
  assume h1,
  by_contradiction h2,
  cases h2 with x h3,
  have h4: P x, from h1 x,
  exact h3 h4,
  -- Implicació 2
  assume h1,
  intro x,
  by_contradiction h2,
  have h3: ∃ (x : Ω), ¬ P x, from exists.intro x h2,
  exact h1 h3,
end

#check P 
lemma E6 : (∃ (x : Ω), P x) ↔ ¬ (∀ (x : Ω), ¬ P x) :=
begin
  split,
  -- Implicació 1
  assume h1,
  by_contradiction h2,
  cases h1 with x h1,
  have h3: ¬ P x, from h2 x,
  exact h3 h1,
  -- Implicació 2
  assume h1,
  by_contradiction h2,
  have h3: ∀ (x:Ω), ¬ P x,
  intro x,
  by_contradiction h3,
  have h4: ∃ (x:Ω), P x,
  exact exists.intro x h3,
  exact h2 h4,
  exact h1 h3,
end

lemma E7 : (¬ ∃ (x : Ω), P x) ↔ (∀ (x : Ω), ¬ P x) :=
begin
  split,
  -- Implicació 1
  assume h1,
  intro x,
  by_contradiction h2,
  have h3: ∃ (x:Ω), P x, from exists.intro x h2,
  exact h1 h3,
  -- Implicació 2
  assume h1,
  by_contradiction h2,
  cases h2 with x h2,
  exact (h1 x) h2, 
end

lemma E8 : (¬ ∀ (x : Ω), P x) ↔ (∃ (x : Ω), ¬ P x) :=
begin
  split,
  -- Implicació 1
  assume h1,
  by_contradiction h2,
  have h3: ∀ (x : Ω), P x,
  intro x,
  by_contradiction h3,
  have h4: ∃ (x : Ω), ¬ P x, from exists.intro x h3,
  exact h2 h4,
  exact h1 h3,
  -- Implicació 2
  assume h1,
  by_contradiction h2,
  cases h1 with x h1,
  exact h1 (h2 x),
end

lemma E9 : (∀ (x : Ω), P x → R) ↔ (∃ (x : Ω), P x) → R :=
begin
  split,
  -- Implicació 1
  assume h1,
  assume h2,
  cases h2 with x h2,
  have h3: P x → R, from h1 x,
  exact h3 h2,
  -- Implicació 2
  assume h1,
  intro x,
  assume h2,
  have h3: ∃ (x : Ω), P x, from exists.intro x h2,
  exact h1 h3, 
end

lemma E10 (x : Ω) : (∃ (x : Ω), P x → R) ↔ (∀ (x : Ω), P x) → R :=
begin
  split,
  -- Implicació 1
  assume h1,
  assume h2,
  have h3: P x, from h2 x,
  cases h1 with z h1,
  have h4: P z, from h2 z,
  exact h1 h4,
  -- Implicació 2
  assume h1,
  have h2: (∀ (x : Ω), P x) ∨ ¬ (∀ (x : Ω), P x), from em (∀ (x : Ω), P x),
  cases h2 with h2,
  have h3: R, from h1 h2,
  have h4: P x → R,
  assume h4, exact h3,
  exact exists.intro x h4,
  have h3: ∃ (x : Ω), ¬ P x,
  exact iff.elim_left (E8 Ω P) h2,
  cases h3 with z h3,
  have h4: P z → R, assume h4,
  exact false.elim (h3 h4),
  exact exists.intro z h4,
end

lemma E11 (x : Ω) : (∃ (x : Ω), R  →  P x) ↔ (R → ∃ (x : Ω), P x):=
begin
  split,
  -- Implicació 1
  assume h1,
  assume h2,
  cases h1 with x h1,
  have h3: P x, from h1 h2,
  exact exists.intro x h3,
  -- Implicació 2
  assume h1,
  have h2: R ∨ ¬R, from em R,
  cases h2 with h2,
  have h3: ∃ (x : Ω), P x, from h1 h2,
  cases h3 with z h3,
  have h4: R → P z, 
  assume h4, exact h3,
  exact exists.intro z h4,
  have h3: R → P x, assume h3,
  exact false.elim (h2 h3),
  exact exists.intro x h3,
end
