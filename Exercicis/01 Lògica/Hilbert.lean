/-Hilbert - Solutions-/
open classical

-- Hilbert Systems
-- https://en.wikipedia.org/wiki/Hilbert_system
-- Logical Axioms P1 P2 P3 P4
theorem P1 (Φ: Prop) : Φ → Φ :=
begin
  sorry,
end

theorem P2 (Φ Ψ : Prop) : Φ → Ψ → Φ :=
begin
  sorry,
end

theorem P3 (Φ Ψ ξ : Prop) : (Φ → (Ψ → ξ)) → ((Φ → Ψ) → (Φ → ξ)) :=
begin
  sorry,
end

theorem P4 (Φ Ψ : Prop) : (¬ Φ → ¬ Ψ) → (Ψ → Φ) :=
begin
  sorry,
end

-- Minimal Logic [Replace P4 with P4m]
-- https://en.wikipedia.org/wiki/Minimal_logic
theorem P4m (Φ Ψ : Prop) : (Φ → Ψ) → ((Φ → ¬ Ψ) → ¬ Φ) :=
begin
  sorry,
end

-- Intuitionistic Logic [Replace P4 with P4i and P5i]
-- https://en.wikipedia.org/wiki/Intuitionistic_logic
theorem P4i (Φ : Prop) : (Φ → ¬ Φ) → ¬ Φ :=
begin
  sorry, 
end

theorem P5i (Φ Ψ : Prop) : ¬ Φ → (Φ → Ψ) :=
begin
  sorry,
end

-- Some useful theorems in Classical Logic and their proofs
-- https://en.wikipedia.org/wiki/Hilbert_system#Some_useful_theorems_and_their_proofs

-- Hypothetical syllogism
-- https://en.wikipedia.org/wiki/Hypothetical_syllogism#Alternative_form
theorem HS1 (p q r : Prop) : (q → r) → ((p → q) → (p → r)) :=
begin
  sorry,
end

theorem L1 (p q : Prop) : p → ((p → q)→ q) :=
begin
  sorry,
end

-- Double negation 1
-- https://en.wikipedia.org/wiki/Double_negation
theorem DN1 (p : Prop) : ¬¬p → p :=
begin
  sorry,
end

-- Double negation 2
theorem DN2 (p : Prop) : p → ¬¬p :=
begin
  sorry,
end

theorem L2 (p q r : Prop) : (p → (q → r)) → (q → (p → r)) :=
begin
  sorry,
end

--An alternative form of the hypothetical syllogism
theorem HS2 (p q r : Prop) : (p → q) → ((q → r) → (p → r)) :=
begin
  sorry,
end

-- Transposition
theorem TR1 (p q : Prop) : (p → q) → (¬ q → ¬ p) :=
begin
  sorry,
end

--Another form of Transposition
theorem TR2 (p q : Prop) : (¬p → q) → (¬q → p) :=
begin
  sorry,
end

theorem L3 (p : Prop) : (¬p → p) → p :=
begin
  sorry,
end
