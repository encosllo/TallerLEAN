-- Obre els recursos per a treballar amb conjunts
-- https://leanprover-community.github.io/mathlib_docs/data/set/basic.html
import data.set.basic  
open set   

-- Assumirem en tot l'exercici que 
-- Ω és un tipus que farà de contenidor
variable (Ω : Type)
-- a b c x y z seran elements de tipus Ω 
variables a b c x y z : Ω          
-- A B C X Y Z són conjunts amb elements de tipus Ω 
variables A B C X Y Z : set Ω

/-
## Notació 
-/

-- #check A ⊆ B            -- sub               -- Subconjunt
-- #check a ∈ A            -- in                -- Pertany
-- #check a ∉ A            -- not in            -- No pertany
-- #check A ∩ B            -- cap               -- Intersecció
-- #check A ∪ B            -- cup               -- Unió
-- #check Aᶜ               -- compl             -- Complement 
-- #check A \ B            -- \                 -- Diferència
-- #check (∅ : set Ω)      -- emptyset          -- Conjunt buit de tipus Ω 
-- #check (univ : set Ω)   -- Conjunt de tots els elements de tipus Ω 
-- #check 𝒫               -- powerset           -- Conjunt de les parts 

/-
## Demostracions
-/

theorem T1 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin 
  sorry,
end

theorem T2 : A \ B = Bᶜ \ Aᶜ :=
begin
  sorry,
end

theorem T3 : A ⊆ B ↔ A ∩ B = A :=
begin
  sorry,
end

theorem T4 : A ⊆ B ↔ A ∪ B = B :=
begin
  sorry,
end

theorem T5 : A ⊆ B ↔ Bᶜ ⊆ Aᶜ :=
begin
  sorry,
end

theorem T6 : A ⊆ B ↔ A ∩ Bᶜ = ∅ :=
begin
  sorry,
end

theorem T7 (h1: A ∩ B = A ∩ C) (h2: A ∪ B = A ∪ C) : B = C :=
begin
  sorry,
end

theorem T8 : (A\B)∪(B\A)=(A∪B)\(A∩B) :=
begin
  sorry,
end 

theorem T9 : A ∩ (B \ C) = ( A ∩ B ) \ ( A ∩ C) :=
begin
  sorry,
end

theorem T10 : A \ (A \ B) = A ∩ B :=
begin
  sorry,
end

theorem T11 : (B ∪ C) \ A = (B \ A) ∪ (C \ A) :=
begin
  sorry,
end

theorem T12 : A ⊆ B ↔ 𝒫 A ⊆ 𝒫 B :=
begin
  sorry,
end

theorem T13 : 𝒫 A ∩ 𝒫 B = 𝒫 (A ∩ B) :=
begin 
  sorry,
end

theorem T14 : 𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B) :=
begin
  sorry,
end 

theorem T15 : X ≠ Y ↔ ∃ (x : Ω), (x ∈ X \ Y ∨ x ∈ Y \ X) :=
begin
  sorry,
end
