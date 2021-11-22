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
  sorry,
end

-- TEOREMA Aux1
-- Negació de la diferència simètrica a esquerra
theorem TDifSimNegEsq (h1: x ∉ A Δ B) : x ∉ A \ B :=
begin
  sorry,
end

-- TEOREMA Aux2
-- Negació de la diferència simètrica a dreta
theorem TDifSimNegDre (h1: x ∉ A Δ B) : x ∉ B \ A :=
begin
  sorry,
end

-- TEOREMA 2
-- Definició alternativa de la diferència simètrica
theorem TDifSimDef2 : A Δ B = (A ∪ B) \ (A ∩ B) :=
begin
  sorry,
end

-- TEOREMA 3
-- La diferència simètrica és commutativa
theorem TDifSimCom : A Δ B = B Δ A :=
begin
  sorry,
end

-- TEOREMA 4
-- La diferència simètrica és associativa
theorem TDifSimAss : A Δ (B Δ C) = (A Δ B) Δ C :=
begin
  sorry,
end

-- TEOREMA 5
-- El conjunt buit és neutre per a la diferència simètrica 
-- per l'esquerra
-- Considera les següents funcions auxiliars
#check mem_empty_eq
#check eq.subst 
theorem TDifSimNeutEs : A Δ ∅ = A :=
begin
  sorry,
end

-- TEOREMA 6
-- El conjunt buit és neutre per a la diferència simètrica 
-- per la dreta
#check eq.trans
theorem TDifSimNeutDr : ∅ Δ A = A :=
begin
  sorry,
end

-- TEOREMA 7
-- Tot conjunt és el seu invers per 
-- a la diferència simètrica
theorem TDifSimInv : A Δ A = ∅ :=
begin
  sorry,
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
  sorry,
end

-- TEOREMA 9
-- La intersecció distribueix sobre la diferència simètrica
theorem TDifSimIntDist : A ∩ (B Δ C) = (A ∩ B) Δ (A ∩ C) :=
begin
  sorry,
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
  sorry,
end

-- Teorema 11
-- Relació amb el complementari
-- ᶜ  compl
theorem TDifSimCmpl : A Δ B = Aᶜ Δ Bᶜ :=
begin
  sorry,
end
