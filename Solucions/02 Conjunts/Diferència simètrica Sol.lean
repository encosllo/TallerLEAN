-- En este exercici obtindrem les propietats bàsiques de la 
-- diferència simètrica de dos conjunts
-- Per a més informació 
-- https://en.wikipedia.org/wiki/Symmetric_difference

-- Obre els recursos per a treballar amb conjunts
-- https://leanprover-community.github.io/mathlib_docs/data/set/basic.html
import data.set.basic  
open set   

-- Assumirem en tot l'exercici que 
-- Ω és un tipus que farà de contenidor
variable (Ω : Type)   
variable x : Ω    
-- A B C són conjunts amb elements de tipus Ω 
variables A B C : set Ω

-- Definició de la diferència simètrica 
-- A Δ B = (A\B) ∪ (B\A)
-- Δ Barra D o Barra Delta per a escriure l'operador
-- Definició de l'operador extreta de 
-- https://leanprover-community.github.io/archive/stream/113488-general/topic/Set.3A.20symmetric.20difference.html
def set.symmetric_difference {α :Type*} (A B : set α) := (A \ B) ∪ (B \ A)
class has_symm_diff (α : Type*) := (symm_diff : α → α → α)

infixr Δ : 70 := has_symm_diff.symm_diff
instance set.has_symm_diff {α : Type*}: has_symm_diff (set α) := ⟨set.symmetric_difference⟩
lemma set.has_symm_diff.def {α : Type*} {A B : set α}: A Δ B = (A \ B) ∪ (B \ A) := rfl

#check A Δ B 

-- TEOREMA 1 
-- Definició de la diferència simètrica
theorem TDifSimDef : A Δ B = (A \ B) ∪ (B \ A) :=
begin
  -- Per definició
  refl,
end

-- TEOREMA Aux1
-- Negació de la diferència simètrica a esquerra
theorem TDifSimNegEsq (h1: x ∉ A Δ B) : x ∉ A \ B :=
begin
  by_contradiction h2,
  exact h1 (or.inl h2),
end

-- TEOREMA Aux2
-- Negació de la diferència simètrica a dreta
theorem TDifSimNegDre (h1: x ∉ A Δ B) : x ∉ B \ A :=
begin
  by_contradiction h2,
  exact h1 (or.inr h2),
end

-- TEOREMA 2
-- Definició alternativa de la diferència simètrica
theorem TDifSimDef2 : A Δ B = (A ∪ B) \ (A ∩ B) :=
begin
  ext x,
  split,
  -- ++++++++++++++++++++++++++++++
  -- +++ D'esquerra a dreta +++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  cases h1,
  -- CAS 1 --------------------
  -----------------------------
  have h2: x ∈ A, from and.elim_left h1,
  have h3: x ∉ B, from and.elim_right h1,
  have h4: x ∉ A ∩ B,
  by_contradiction h4,
  exact h3 (and.elim_right h4), 
  exact and.intro (or.inl h2) h4,
  -- CAS 2 --------------------
  -----------------------------
  have h2: x ∈ B, from and.elim_left h1,
  have h3: x ∉ A, from and.elim_right h1,
  have h4: x ∉ A ∩ B,
  by_contradiction h4,
  exact h3 (and.elim_left h4), 
  exact and.intro (or.inr h2) h4,
  -- ++++++++++++++++++++++++++++++
  -- +++ De dreta a esquerra ++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  have h2: x ∉ A ∩ B, from and.elim_right h1,
  have h3: x ∈ A ∪ B, from and.elim_left h1,
  cases h3,
  -- CAS 1 --------------------
  -----------------------------
  have h4: x ∉ B, 
  by_contradiction h4,
  exact h2 (and.intro h3 h4),
  exact or.inl (and.intro h3 h4),
  -- CAS 2 --------------------
  -----------------------------
  have h4: x ∉ A, 
  by_contradiction h4,
  exact h2 (and.intro h4 h3),
  exact or.inr (and.intro h3 h4),
end

-- TEOREMA 3
-- La diferència simètrica és commutativa
theorem TDifSimCom : A Δ B = B Δ A :=
begin
  ext x,
  split,
  -- ++++++++++++++++++++++++++++++
  -- +++ D'esquerra a dreta +++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  cases h1,
  exact or.inr h1,
  exact or.inl h1,
  -- ++++++++++++++++++++++++++++++
  -- +++ De dreta a esquerra ++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  cases h1,
  exact or.inr h1,
  exact or.inl h1,
end

-- TEOREMA 4
-- La diferència simètrica és associativa
theorem TDifSimAss : A Δ (B Δ C) = (A Δ B) Δ C :=
begin
  ext x,
  split,
  -- ++++++++++++++++++++++++++++++
  -- +++ D'esquerra a dreta +++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  cases h1,
  -- CAS 1 --------------------
  -----------------------------
  have h2: x ∈ A, from and.elim_left h1,
  have h3: x ∉ B Δ C, from and.elim_right h1,
  -- D'h3 concloem que x ∉ B \ C 
  have h4: x ∉ B \ C, 
  exact (TDifSimNegEsq Ω x B C h3),
  -- D'h3 concloem que x ∉ C \ B 
  have h5: x ∉ C \ B, 
  exact (TDifSimNegDre Ω x B C h3),
  -- D'h4 concloem que x ∈ C o x ∉ B 
  have h6: x ∈ C ∨ x ∉ B, 
  have h7: x ∈ C ∨ x ∉ C, from em (x ∈ C),
  cases h7,
  exact or.inl h7,
  have h8: x ∉ B,
  by_contradiction h8,
  exact h4 (and.intro h8 h7),
  exact or.inr h8, 
  -- Fem cassos sobre h6
  cases h6, 
  -------------------
  -- Primer cas x ∈ C 
  -- Si x ∈ C, aleshores x ∈ B ja que, altrament, x ∈ C \ B
  have h7: x ∈ B,
  by_contradiction h7,
  exact h5 (and.intro h6 h7),
  -- Aleshores x ∈ A, x ∈ B, x ∈ C
  -- Anem a demostrar que x ∉ A Δ B 
  have h8: x ∉ A Δ B,
  by_contradiction h8,
  cases h8,
  exact (and.elim_right h8) h7,
  exact (and.elim_right h8) h2,
  -- Concloem que x ∈ C \ (A Δ B)
  exact (or.inr (and.intro h6 h8)),
  ------------------
  -- Segon cas x ∉ B
  -- Si x ∉ B, aleshores x ∉ C ja que, altrament, x ∈ C \ B
  have h7: x ∉ C,
  by_contradiction h7,
  exact h5 (and.intro h7 h6),  
  -- Aleshores x ∈ A, x ∉ B, x ∉ C
  -- Anem a demostrar que x ∈ A Δ B
  have h8: x ∈ A Δ B,
  exact or.inl (and.intro h2 h6),
  -- Concloem que x ∈ (A Δ B) \ C
  exact or.inl (and.intro h8 h7),
  -- CAS 2 --------------------
  -----------------------------
  have h2: x ∉ A, from and.elim_right h1,
  have h3: x ∈ B Δ C, from and.elim_left h1,
  -- Fem cassos sobre h2
  cases h3,
  -- Primer cas x ∈ B \ C
  have h4: x ∈ B, from and.elim_left h3,
  have h5: x ∉ C, from and.elim_right h3,
  -- Aleshores x ∉ A, x ∈ B, x ∉ C
  -- Anem a demostrar que x ∈ A Δ B
  have h6: x ∈ A Δ B,
  exact or.inr (and.intro h4 h2), 
  -- Concloem que x ∈ (A Δ B) \ C
  exact or.inl (and.intro h6 h5), 
  -- Segon cas x ∈ C \ B
  have h4: x ∈ C, from and.elim_left h3,
  have h5: x ∉ B, from and.elim_right h3,
  -- Aleshores x ∉ A, x ∉ B, x ∈ C
  -- Anem a demostrar que x ∉ A Δ B
  have h6: x ∉ A Δ B,
  by_contradiction h6,
  cases h6,
  exact h2 (and.elim_left h6),  
  exact h5 (and.elim_left h6),
  exact or.inr (and.intro h4 h6),
  -- ++++++++++++++++++++++++++++++
  -- +++ De dreta a esquerra ++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  cases h1,
  -- CAS 1 --------------------
  -----------------------------
  have h2: x ∉ C, from and.elim_right h1,
  have h3: x ∈ A Δ B, from and.elim_left h1,
  cases h3,
  -- Subcas 1
  have h4: x ∈ A, from and.elim_left h3,
  have h5: x ∉ B, from and.elim_right h3,
  -- Aleshores x ∈ A, x ∉ B, x ∉ C
  -- Anem a demostrar que x ∉ B Δ C
  have h6: x ∉ B Δ C, by_contradiction h6,
  cases h6,
  exact h5 (and.elim_left h6),
  exact h2 (and.elim_left h6),
  exact or.inl (and.intro h4 h6),
  -- Subcas 2
  have h4: x ∈ B, from and.elim_left h3,
  have h5: x ∉ A, from and.elim_right h3,
  -- Aleshores x ∉ A, x ∈ B, x ∉ C
  -- Anem a demostrar que x ∈ B Δ C
  have h6: x ∈ B Δ C, from or.inl (and.intro h4 h2),  
  exact or.inr (and.intro h6 h5),
  -- CAS 2 --------------------
  -----------------------------
  have h2: x ∈ C, from and.elim_left h1,
  have h3: x ∉ A Δ B, from and.elim_right h1,
  -- D'h3 concloem que x ∉ A \ B 
  have h4: x ∉ A \ B, 
  exact (TDifSimNegEsq Ω x A B h3),
  -- D'h3 concloem que x ∉ B \ A 
  have h5: x ∉ B \ A, 
  exact (TDifSimNegDre Ω x A B h3),
  -- D'h4 concloem que x ∈ B o x ∉ A 
  have h6: x ∈ B ∨ x ∉ A, 
  have h7: x ∈ B ∨ x ∉ B, from em (x ∈ B),
  cases h7,
  exact or.inl h7,
  have h8: x ∉ A,
  by_contradiction h8,
  exact h4 (and.intro h8 h7),
  exact or.inr h8, 
  -- Fem cassos sobre h6
  cases h6, 
  -------------------
  -- Primer cas x ∈ B 
  -- Si x ∈ B, aleshores x ∈ A ja que, altrament, x ∈ B \ A
  have h7: x ∈ A,
  by_contradiction h7,
  exact h5 (and.intro h6 h7),
  -- Aleshores x ∈ A, x ∈ B, x ∈ C
  -- Anem a demostrar que x ∉ B Δ C 
  have h8: x ∉ B Δ C,
  by_contradiction h8,
  cases h8,
  exact (and.elim_right h8) h2,
  exact (and.elim_right h8) h6,
  -- Concloem que x ∈ A \ (B Δ C)
  exact (or.inl (and.intro h7 h8)),
  ------------------
  -- Segon cas x ∉ A
  -- Si x ∉ A, aleshores x ∉ B ja que, altrament, x ∈ B \ A
  have h7: x ∉ B,
  by_contradiction h7,
  exact h5 (and.intro h7 h6),  
  -- Aleshores x ∉ A, x ∉ B, x ∈ C
  -- Anem a demostrar que x ∈ B Δ C
  have h8: x ∈ B Δ C,
  exact or.inr (and.intro h2 h7),
  -- Concloem que x ∈ (A Δ B) \ C
  exact or.inr (and.intro h8 h6),
end

-- TEOREMA 5
-- El conjunt buit és neutre per a la diferència simètrica 
-- per l'esquerra
-- Considera les següents funcions auxiliars
#check mem_empty_eq
#check eq.subst 
theorem TDifSimNeutEs : A Δ ∅ = A :=
begin
  ext x,
  split,
  -- ++++++++++++++++++++++++++++++
  -- +++ D'esquerra a dreta +++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  cases h1,
  exact and.elim_left h1,
  exact false.elim (and.elim_left h1),
  -- ++++++++++++++++++++++++++++++
  -- +++ De dreta a esquerra ++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  have h2: x ∉ ∅, 
  by_contradiction h2,
  exact eq.subst (mem_empty_eq x) h2,
  exact or.inl (and.intro h1 h2),
end

-- TEOREMA 6
-- El conjunt buit és neutre per a la diferència simètrica 
-- per la dreta
#check eq.trans
theorem TDifSimNeutDr : ∅ Δ A = A :=
begin
  have h1: ∅ Δ A = A Δ ∅, from TDifSimCom Ω ∅ A,
  have h2: A Δ ∅ = A, from TDifSimNeutEs Ω A,
  exact eq.trans h1 h2,
end

-- TEOREMA 7
-- Tot conjunt és el seu invers per 
-- a la diferència simètrica
theorem TDifSimInv : A Δ A = ∅ :=
begin
  ext x,
  split,
  -- ++++++++++++++++++++++++++++++
  -- +++ D'esquerra a dreta +++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  cases h1,
  exact false.elim ((and.elim_right h1) (and.elim_left h1)),
  exact false.elim ((and.elim_right h1) (and.elim_left h1)),
  -- ++++++++++++++++++++++++++++++
  -- +++ De dreta a esquerra ++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  exact false.elim (eq.subst (mem_empty_eq Ω) h1),
end

-- Com a conseqüència dels teorems anteriors,
-- el conjunt de les parts d'un conjunt, 𝒫(X),
-- és un grup abelià amb l'operació
-- diferència simètrica que té el buit com a neutre,
-- és a dir, (𝒫(X),Δ,∅) és un grup abelià.

-- Si 0=∅, 1={0}, 2={0,1}, aleshores
-- (𝒫(0),Δ,∅) és isomorf al grup trivial C1
-- (𝒫(1),Δ,∅) és isomorf al grup cíclic C2
-- (𝒫(2),Δ,∅) és isomorf al 4-grup de Klein V4 (C2×C2)

-- TEOREMA 8
-- La diferència simètrica de diferències simètriques
-- torna a ser una diferència simètrica
theorem TDifSimIt : (A Δ B) Δ (B Δ C) = A Δ C :=
begin
  ext x,
  split,
  -- ++++++++++++++++++++++++++++++
  -- +++ D'esquerra a dreta +++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  cases h1,
  -- CAS 1 --------------------
  -----------------------------
  have h2: x ∈ A Δ B, from and.elim_left h1,
  have h3: x ∉ B Δ C, from and.elim_right h1, 
  -- D'h3 concloem que x ∉ B \ C 
  have h4: x ∉ B \ C, 
  exact (TDifSimNegEsq Ω x B C h3),
  -- D'h3 concloem que x ∉ C \ B 
  have h5: x ∉ C \ B, 
  exact (TDifSimNegDre Ω x B C h3),
  -- D'h4 concloem que x ∈ C o x ∉ B 
  have h6: x ∈ C ∨ x ∉ B, 
  have h7: x ∈ C ∨ x ∉ C, from em (x ∈ C),
  cases h7,
  exact or.inl h7,
  have h8: x ∉ B,
  by_contradiction h8,
  exact h4 (and.intro h8 h7),
  exact or.inr h8, 
  cases h2,
  ----
  cases h6,
  -- Subcas 1
  exact false.elim (h5 (and.intro h6 (and.elim_right h2))),
  -- Subcas 2
  have h7: x ∈ A, from and.elim_left h2,
  have h8: x ∉ C, 
  by_contradiction h8,
  exact h5 (and.intro h8 h6),
  exact or.inl (and.intro h7 h8),
  ----
  cases h6,
  -- Subcas 1
  exact or.inr (and.intro h6 (and.elim_right h2)),
  -- Subcas 2
  exact (false.elim (h6 (and.elim_left h2))),
  -- CAS 2 --------------------
  -----------------------------
  have h2: x ∈ B Δ C, from and.elim_left h1,
  have h3: x ∉ A Δ B, from and.elim_right h1,
  -- D'h3 concloem que x ∉ A \ B 
  have h4: x ∉ A \ B, 
  exact (TDifSimNegEsq Ω x A B h3),
  -- D'h3 concloem que x ∉ B \ A 
  have h5: x ∉ B \ A, 
  exact (TDifSimNegDre Ω x A B h3),
  cases h2,
  -- Subcas 1
  have h6: x ∈ A, 
  by_contradiction h6,
  exact (h5 (and.intro (and.elim_left h2) h6)),
  exact (or.inl (and.intro h6 (and.elim_right h2))),
  -- Subcas 2
  have h6: x ∉ A,
  by_contradiction h6,
  exact (h4 (and.intro h6 (and.elim_right h2))),
  exact (or.inr (and.intro (and.elim_left h2) h6)),
  -- ++++++++++++++++++++++++++++++
  -- +++ De dreta a esquerra ++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  cases h1,
  -- CAS 1 --------------------
  -----------------------------
  have h2: x ∈ A, from and.elim_left h1,
  have h3: x ∉ C, from and.elim_right h1,
  have h4: x ∈ B ∨ x ∉ B, from em (x ∈ B),
  cases h4,
  -- Cas x ∈ B
  have h5: x ∈ B Δ C, from or.inl (and.intro h4 h3),
  have h6: x ∉ A Δ B,
  by_contradiction h6,
  cases h6,
  exact ((and.elim_right h6) h4),
  exact ((and.elim_right h6) h2),
  exact (or.inr (and.intro h5 h6)),
  -- Cas x ∉ B
  have h5: x ∈ A Δ B, from or.inl  (and.intro h2 h4), 
  have h6: x ∉ B Δ C,
  by_contradiction h6,
  cases h6,
  exact (h4 (and.elim_left h6)), 
  exact (h3 (and.elim_left h6)), 
  exact (or.inl (and.intro h5 h6)),
  -- CAS 2 --------------------
  -----------------------------
  have h2: x ∈ C, from and.elim_left h1,
  have h3: x ∉ A, from and.elim_right h1,
  have h4: x ∈ B ∨ x ∉ B, from em (x ∈ B),
  cases h4,
  -- Cas x ∈ B
  have h5: x ∈ A Δ B, from or.inr (and.intro h4 h3),
  have h6: x ∉ B Δ C,
  by_contradiction h6,
  cases h6,
  exact ((and.elim_right h6) h2),
  exact ((and.elim_right h6) h4),
  exact (or.inl (and.intro h5 h6)),
  -- Cas x ∉ B
  have h5: x ∈ B Δ C, from or.inr (and.intro h2 h4), 
  have h6: x ∉ A Δ B,
  by_contradiction h6,
  cases h6,
  exact (h3 (and.elim_left h6)), 
  exact (h4 (and.elim_left h6)), 
  exact (or.inr (and.intro h5 h6)),
end

-- TEOREMA 9
-- La intersecció distribueix sobre la diferència simètrica
theorem TDifSimIntDist : A ∩ (B Δ C) = (A ∩ B) Δ (A ∩ C) :=
begin
  ext x,
  split,
  -- ++++++++++++++++++++++++++++++
  -- +++ D'esquerra a dreta +++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  have h2: x ∈ A, from and.elim_left h1,
  have h3: x ∈ B Δ C, from and.elim_right h1,
  cases h3,
  -- Cas x ∈ B \ C
  have h4: x ∈ A ∩ B, from and.intro h2 (and.elim_left h3),
  have h5: x ∉ A ∩ C,
  by_contradiction h5,
  exact (and.elim_right h3) (and.elim_right h5),   
  exact (or.inl (and.intro h4 h5)),
  -- Cas x ∈ C \ B
  have h4: x ∈ A ∩ C, from and.intro h2 (and.elim_left h3),
  have h5: x ∉ A ∩ B,
  by_contradiction h5,
  exact (and.elim_right h3) (and.elim_right h5),   
  exact (or.inr (and.intro h4 h5)),
  -- ++++++++++++++++++++++++++++++
  -- +++ De dreta a esquerra ++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  cases h1,
  -- Cas x ∈ A ∩ B
  have h2: x ∈ A ∩ B, from and.elim_left h1,
  have h3: x ∉ A ∩ C, from and.elim_right h1,
  have h4: x ∈ A, from and.elim_left h2,
  have h5: x ∈ B, from and.elim_right h2,
  have h6: x ∉ C, by_contradiction h6,
  exact (h3 (and.intro h4 h6)), 
  exact (and.intro h4 (or.inl (and.intro h5 h6))),
  -- Cas x ∈ A ∩ C
  have h2: x ∈ A ∩ C, from and.elim_left h1,
  have h3: x ∉ A ∩ B, from and.elim_right h1,
  have h4: x ∈ A, from and.elim_left h2,
  have h5: x ∈ C, from and.elim_right h2,
  have h6: x ∉ B, by_contradiction h6,
  exact (h3 (and.intro h4 h6)), 
  exact (and.intro h4 (or.inr (and.intro h5 h6))),
end

-- Com a conseqüència dels teorems anteriors,
-- el conjunt de les parts d'un conjunt, 𝒫(X),
-- és un anell Booleà amb l'operació
-- diferència simètrica com a suma 
-- i l'operació intersecció com a producte
-- és a dir, (𝒫(X),Δ,∩,∅,X) és un anell Booleà.

-- TEOREMA 10
-- Unicitat de l'invers per a la diferència simètrica
theorem TDifSimInvIff : A Δ B = ∅ ↔ A = B :=
begin
  split,
  -- ++++++++++++++++++++++++++++++
  -- +++ D'esquerra a dreta +++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  ext x,
  split,
  -- x ∈ A
  assume h2,
  by_contradiction h3,
  have h4: x ∈ A Δ B, from or.inl (and.intro h2 h3),
  rw [set.ext_iff] at h1,
  have h5: x ∈ ∅, from iff.elim_left (h1 x) h4,
  exact eq.subst (mem_empty_eq x) h5,
  -- x ∈ B
  assume h2,
  by_contradiction h3,
  have h4: x ∈ A Δ B, from or.inr (and.intro h2 h3),
  rw [set.ext_iff] at h1,
  have h5: x ∈ ∅, from iff.elim_left (h1 x) h4,
  exact eq.subst (mem_empty_eq x) h5,
  -- ++++++++++++++++++++++++++++++
  -- +++ De dreta a esquerra ++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  rw [set.ext_iff] at h1,
  ext x,
  split,
  -- x ∈ A Δ B
  assume h2,
  cases h2,
  -- Cas 1
  have h3: x ∈ A, from and.elim_left h2,
  have h4: x ∉ B, from and.elim_right h2,
  have h5: x ∈ B, from iff.elim_left (h1 x) h3,
  exact false.elim (h4 h5),
  -- Cas 2
  have h3: x ∈ B, from and.elim_left h2,
  have h4: x ∉ A, from and.elim_right h2,
  have h5: x ∈ A, from iff.elim_right (h1 x) h3,
  exact false.elim (h4 h5),
  -- x ∈ ∅
  assume h2,
  have h3: false, from eq.subst (mem_empty_eq x) h2,
  exact false.elim h3, 
end

-- Teorema 11
-- Relació amb el complementari
-- ᶜ  compl
theorem TDifSimCmpl : A Δ B = Aᶜ Δ Bᶜ :=
begin
  ext x,
  split,
  -- ++++++++++++++++++++++++++++++
  -- +++ D'esquerra a dreta +++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  cases h1,
  -- x ∈ A \ B
  have h2: x ∈ A, from and.elim_left h1,
  have h3: x ∉ B, from and.elim_right h1,
  have h4: x ∈ Bᶜ, from h3,
  have h5: x ∉ Aᶜ, by_contradiction h5,
  have h6: x ∉ A, from h5,
  exact h6 h2,    
  exact or.inr (and.intro h4 h5), 
  -- x ∈ B \ A
  have h2: x ∈ B, from and.elim_left h1,
  have h3: x ∉ A, from and.elim_right h1,
  have h4: x ∈ Aᶜ, from h3,
  have h5: x ∉ Bᶜ, by_contradiction h5,
  have h6: x ∉ B, from h5,
  exact h6 h2,    
  exact or.inl (and.intro h4 h5), 
  -- ++++++++++++++++++++++++++++++
  -- +++ De dreta a esquerra ++++++
  -- ++++++++++++++++++++++++++++++
  assume h1,
  cases h1,
  -- x ∈ Aᶜ \ Bᶜ 
  have h2: x ∈ Aᶜ, from and.elim_left h1,
  have h3: x ∉ A, from h2,
  have h4: x ∉ Bᶜ , from and.elim_right h1,
  have h5: x ∈ B, 
  by_contradiction h5,
  have h6: x ∈ Bᶜ, from h5, 
  exact h4 h6,
  exact or.inr (and.intro h5 h3),
  -- x ∈ Bᶜ \ Aᶜ 
  have h2: x ∈ Bᶜ, from and.elim_left h1,
  have h3: x ∉ B, from h2,
  have h4: x ∉ Aᶜ , from and.elim_right h1,
  have h5: x ∈ A, 
  by_contradiction h5,
  have h6: x ∈ Aᶜ, from h5, 
  exact h4 h6,
  exact or.inl (and.intro h5 h3),
end
