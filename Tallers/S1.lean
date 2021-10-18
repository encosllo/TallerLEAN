-- Sessió 2021.10.18
-- Treballarem amb lògica clàssica
open classical  

-- En esta sessió introdïm 
-- les regles de deducció natural de connectors lògics
-- https://es.wikipedia.org/wiki/Deducci%C3%B3n_natural
-- https://leanprover.github.io/logic_and_proof/propositional_logic_in_lean.html

-- Notació per a les constants i els  connectors
-- false
-- true
-- ¬ ¬
-- ∧ \and
-- ∨ ∨
-- → →
-- ↔ \iff

-- Introducció de la negació (Reducció a l'absurde)
lemma IN (P : Prop) (h1: false) : ¬P :=
begin
  exact false.elim h1,
end

-- Eliminació de la negació 
lemma EN (P : Prop) (h1: ¬¬P) : P :=
begin
  by_contradiction h2,
  exact h1 h2,
end

-- Introducció de la conjunció 
lemma IC (P Q: Prop) (h1: P) (h2: Q) : P ∧ Q :=
begin
  exact and.intro h1 h2,
end

-- Eliminació de la conjunció (esquerra)
lemma ECE (P Q: Prop) (h1: P ∧ Q) : P := 
begin
  exact and.elim_left h1,
  -- (a dreta per a demostrar Q) 
  -- exact and.elim_right h1,
end

-- Introducció de la disjunció (esquerra)
lemma IDE (P Q: Prop) (h1: P) : P ∨ Q :=
begin
  exact or.inl h1,
  -- (a dreta, si la hipòtesi és Q)
  -- exact or.inr h1,
end

-- Eliminació de la disjunció (esquerra)
lemma EDE (P Q: Prop) (h1: P ∨ Q) (h2: ¬ P): Q := 
begin
  cases h1 with h3 h3,
  -- Cas 1
  have h4: false, from h2 h3,
  exact false.elim h4,
  -- Cas 2
  exact h3,
end

-- Introducció de la implicació 
lemma II (P Q: Prop) (h1: Q) : P → Q :=
begin
  assume h2: P,
  exact h1,
end

-- Eliminació de la implicació (Modus Ponens)
lemma EI (P Q: Prop) (h1: P → Q) (h2: P): Q :=
begin
  exact h1 h2,
end

-- Introducció de la doble implicació 
lemma IDI (P Q: Prop) (h1: P → Q) (h2: Q → P) : P ↔ Q :=
begin
  exact iff.intro h1 h2,
end

-- Eliminació de la doble implicació (a esquerra)
lemma EDI (P Q: Prop) (h1: P ↔ Q) : P → Q :=
begin
  exact iff.elim_left h1,
end



