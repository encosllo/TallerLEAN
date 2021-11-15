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
  -- Els conjunts seran iguals si tenen els mateixos elements
  ext z, 
  -- Doble implicació
  split,
  -- Primera implicació
  assume h1,
  have h2: z ∈ A, from and.elim_left h1,
  have h3: z ∈ B ∪ C, from and.elim_right h1,
  cases h3 with h3 h3,
  -- Cas 1
  exact or.inl (and.intro h2 h3),
  -- Cas 2
  exact or.inr (and.intro h2 h3),
  -- Segona implicació
  assume h1,
  cases h1 with h1 h1,
  -- Cas 1
  have h2: z ∈ A, from and.elim_left h1,
  have h3: z ∈ B ∪ C, from or.inl (and.elim_right h1), 
  exact and.intro h2 h3,
  -- Cas 2
  have h2: z ∈ A, from and.elim_left h1,
  have h3: z ∈ B ∪ C, from or.inr (and.elim_right h1), 
  exact and.intro h2 h3,
end

theorem T2 : A \ B = Bᶜ \ Aᶜ :=
begin
  ext z,
  split,
  -- Primera implicació
  assume h1,
  have h2: z ∈ A, from and.elim_left h1,
  have h3: z ∉ B, from and.elim_right h1,
  have h4: z ∈ Bᶜ, exact h3,
  have h5: z ∉ Aᶜ,
  by_contradiction h6,
  exact h6 h2, 
  exact and.intro h4 h5,
  -- Segona implicació
  assume h1,
  have h2: z ∈ Bᶜ, from and.elim_left h1,
  have h3: z ∉ Aᶜ, from and.elim_right h1,
  have h4: z ∈ A,
  by_contradiction h5,
  exact h3 h5, 
  exact and.intro h4 h2, 
end

theorem T3 : A ⊆ B ↔ A ∩ B = A :=
begin
  split,
  assume h1,
  ext z,
  split,
  assume h2,
  exact and.elim_left h2,
  assume h2,
  have h3: z ∈ B, from h1 h2,
  exact and.intro h2 h3,
  assume h1,
  intro z,
  assume h2,
  rw [set.ext_iff] at h1,
  have h3: z ∈ A ∩ B, from (iff.elim_right (h1 z)) h2,
  exact and.elim_right h3,
end

theorem T4 : A ⊆ B ↔ A ∪ B = B :=
begin
  split,
  assume h1,
  ext z,
  split,
  assume h2,
  cases h2 with h3 h3,
  -- Cas 1 z ∈ A
  exact h1 h3,
  -- Cas 2 z ∈ B
  exact h3,
  assume h2,
  exact or.inr h2,
  assume h1,
  intro z,
  assume h2,
  have h3: z ∈ A ∪ B, from or.inl h2,
  rw [set.ext_iff] at h1,
  have h4: z ∈ A ∪ B ↔ z ∈ B, from h1 z,
  exact (iff.elim_left h4) h3,
end

theorem T5 : A ⊆ B ↔ Bᶜ ⊆ Aᶜ :=
begin
  split,
  assume h1,
  intro z,
  assume h2,
  have h3: z ∉ A, 
  by_contradiction h4,
  exact h2 (h1 h4),
  exact h3,
  assume h1,
  intro z,
  assume h2,
  by_contradiction h3,
  exact (h1 h3) h2,
end

theorem T6 : A ⊆ B ↔ A ∩ Bᶜ = ∅ :=
begin
  split,
  assume h1,
  ext z,
  split,
  intro h2,
  have h3: z ∈ B, from h1 (and.elim_left h2),
  have h4: z ∈ Bᶜ, from and.elim_right h2, 
  exact h4 h3,
  intro h2,
  exact false.elim h2,
  assume h1,
  rw [set.ext_iff] at h1,
  intro z,
  assume h2,
  have h3: z ∈ A ∩ Bᶜ ↔ z ∈ ∅, from h1 z,   
  have h4: z ∈ A ∩ Bᶜ → z ∈ ∅, from iff.elim_left h3,
  by_contradiction h5,
  have h6: z ∈ ∅, from h4 (and.intro h2 h5), 
  exact h6,
end

theorem T7 (h1: A ∩ B = A ∩ C) (h2: A ∪ B = A ∪ C) : B = C :=
begin
  rw [set.ext_iff] at h1,
  rw [set.ext_iff] at h2,
  ext z,
  split,
  assume h3,
  have h4: z ∈ A ∪ B, from or.inr h3,
  have h5: z ∈ A ∪ C, from (iff.elim_left (h2 z)) h4,
  cases h5 with h5 h5,
  -- Cas 1
  exact and.elim_right ((iff.elim_left (h1 z)) (and.intro h5 h3)),
  -- Cas 2
  exact h5,
  assume h3,
  have h4: z ∈ A ∪ B, from  (iff.elim_right (h2 z)) (or.inr h3),
  cases h4 with h4 h4,
  -- Cas 1
  exact and.elim_right ((iff.elim_right (h1 z)) (and.intro h4 h3)),
  -- Cas 2
  exact h4,
end

theorem T8 : (A\B)∪(B\A)=(A∪B)\(A∩B) :=
begin
  ext z,
  split,
  -- Primera implicació
  intro h1,
  cases h1 with h1 h1,
  have h2: z ∈ A, from and.elim_left h1,
  have h3: z ∉ B, from and.elim_right h1,
  have h4: z ∈ A ∪ B, from or.inl h2,
  have h5: z ∉ A ∩ B,
  by_contradiction h5,
  exact h3 (and.elim_right h5),
  exact and.intro h4 h5,
  have h2: z ∈ B, from and.elim_left h1,
  have h3: z ∉ A, from and.elim_right h1,
  have h4: z∈ A ∪ B, from or.inr h2,
  have h5: z ∉ A ∩ B,
  by_contradiction h5,
  exact h3 (and.elim_left h5),
  exact and.intro h4 h5,
  -- Segona implicació
  rintros ⟨h1,h2⟩, 
  cases h1 with h1 h1,
  -- Cas 1
  have h3: z ∉ B,
  by_contradiction h3,
  exact h2 (and.intro h1 h3),
  exact or.inl (and.intro h1 h3),
  -- Cas 2
  have h3: z ∉ A,
  by_contradiction h3,
  exact h2 (and.intro h3 h1),
  exact or.inr (and.intro h1 h3),
end 

theorem T9 : A ∩ (B \ C) = ( A ∩ B ) \ ( A ∩ C) :=
begin
  ext z,
  split,
  rintros ⟨h1 , ⟨h2 , h3⟩⟩, 
  have h4: z ∈ A ∩ B, from and.intro h1 h2,
  have h5: z ∉ A ∩ C,
  by_contradiction h5,
  exact h3 (and.elim_right h5),
  exact and.intro h4 h5,
  --
  rintros ⟨⟨h1, h2⟩, h3⟩,
  have h4: z ∉ C,
  by_contradiction h4,
  exact h3 (and.intro h1 h4),  
  exact and.intro h1 (and.intro h2 h4),
end

theorem T10 : A \ (A \ B) = A ∩ B :=
begin
  ext z, 
  split,
  rintros ⟨h1,h2⟩,
  have h3: z ∈ B,
  by_contradiction h3,
  exact h2 (and.intro h1 h3), 
  exact and.intro h1 h3,
  rintros ⟨h1,h2⟩, 
  have h3: z ∉ A\ B,
  by_contradiction h3,
  exact (and.elim_right h3) h2,
  exact and.intro h1 h3,
end

theorem T11 : (B ∪ C) \ A = (B \ A) ∪ (C \ A) :=
begin
  ext z,
  split,
  rintro ⟨h1, h2⟩,
  cases h1 with h1 h1,
  exact or.inl (and.intro h1 h2), 
  exact or.inr (and.intro h1 h2),
  assume h1,
  cases h1 with h1 h1, 
  have h2: z ∈ B, from and.elim_left h1,
  have h3: z ∉ A, from and.elim_right h1,
  have h4: z ∈ B ∪ C, from or.inl h2,
  exact and.intro h4 h3,
  have h2: z ∈ C, from and.elim_left h1,
  have h3: z ∉ A, from and.elim_right h1,
  have h4: z ∈ B ∪ C, from or.inr h2,
  exact and.intro h4 h3,
end

theorem T12 : A ⊆ B ↔ 𝒫 A ⊆ 𝒫 B :=
begin
  split,
  assume h1,
  intro X,
  assume h2,
  have h3: X ⊆ A, from h2,
  have h4: X ⊆ B, 
  intro x,
  assume h4,
  have h5: x ∈ A, from h3 h4,
  exact h1 h5,
  exact h4,
  assume h1,
  have h2: A ⊆ A,
  intro z,
  assume h2,
  exact h2,
  exact h1 h2,
end

theorem T13 : 𝒫 A ∩ 𝒫 B = 𝒫 (A ∩ B) :=
begin 
  ext Z,
  split,
  rintros ⟨h1, h2⟩, 
  have h3: Z ⊆ A, from h1,
  have h4: Z ⊆ B, from h2,
  have h5: Z ⊆ A ∩ B, 
  intro z,
  assume h5,
  exact and.intro (h3 h5) (h4 h5),
  exact h5,
  assume h1,
  have h2: Z ⊆ A ∩ B, from h1,
  have h3: Z ⊆ A, 
  intro z,
  assume h3,
  have h4: z ∈ A ∩ B, from h2 h3,
  exact and.elim_left h4, 
  have h4: Z ⊆ B, 
  intro z,
  assume h4,
  have h5: z ∈ A ∩ B, from h2 h4,
  exact and.elim_right h5,
  exact and.intro h3 h4, 
end

theorem T14 : 𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B) :=
begin
  intro Z,
  assume h1,
  cases h1 with h1 h1,
  -- Cas 1
  have h2: Z ⊆ A, from h1,
  have h3: Z ⊆ A ∪ B, 
  intro z,
  assume h3,
  exact or.inl (h2 h3),
  exact h3,
  -- Cas 2
  have h2: Z ⊆ B, from h1,
  have h3: Z ⊆ A ∪ B, 
  intro z,
  assume h3,
  exact or.inr (h2 h3),
  exact h3,
end 

theorem T15 : X ≠ Y ↔ ∃ (x : Ω), (x ∈ X \ Y ∨ x ∈ Y \ X) :=
begin
  split,
  -- D'esquerra a dreta
  assume h1,
  have h2: ∃ (x : Ω), x ∈ X ↔ x ∉ Y,
  by_contradiction h2,
  have h3: ∀ (x : Ω), x ∈ X ↔ x ∈ Y,
  intro x,
  split,
  --
  assume h3,
  by_contradiction h4,
  have h5: x ∈ X ↔ x ∉ Y,
  split,
  intro h5,
  exact h4,
  intro h5,
  exact h3,
  exact h2 (exists.intro x h5),
  --
  assume h3,
  by_contradiction h4,
  have h5: x ∈ X ↔ x ∉ Y,
  split,
  intro h5,
  exact (false.elim (h4 h5)),
  intro h5,
  exact (false.elim (h5 h3)),
  --
  exact h2 (exists.intro x h5),
  --
  have h4: X = Y,
  rw [set.ext_iff], exact h3,
  --
  exact h1 h4,
  --
  cases h2 with x h2,
  have h3: x ∈ X ∨ x ∉ X, from em (x ∈ X),
  cases h3,
  --
  have h4: x ∉ Y, from (iff.elim_left h2) h3,
  have h5: x ∈ X \ Y ∨ x ∈ Y \ X, from or.inl (and.intro h3 h4),  
  exact exists.intro x h5, 
  --
  have h4: x ∈ Y, by_contradiction h4,
  have h5: x ∈ X, from (iff.elim_right h2) h4,
  exact h3 h5,
  have h5: x ∈ X \ Y ∨ x ∈ Y \ X, from or.inr (and.intro h4 h3),
  exact exists.intro x h5, 
  -- De dreta a esquerra
  assume h1,
  cases h1 with x h1,
  cases h1,
  -- x ∈ X\Y
  have h2: ¬(X=Y), by_contradiction h2,
  rw [set.ext_iff] at h2, 
  have h3: x ∈ X ↔ x ∈ Y, from h2 x,
  have h4: x ∈ X, from and.elim_left h1,
  have h5: x ∉ Y, from and.elim_right h1,
  have h6: x ∈ Y, from (iff.elim_left h3) h4,
  exact h5 h6,
  exact h2,
  -- x ∈ Y\X
  have h2: ¬(X=Y), by_contradiction h2,
  rw [set.ext_iff] at h2, 
  have h3: x ∈ X ↔ x ∈ Y, from h2 x,
  have h4: x ∈ Y, from and.elim_left h1,
  have h5: x ∉ X, from and.elim_right h1,
  have h6: x ∈ X, from (iff.elim_right h3) h4,
  exact h5 h6,
  exact h2,
end
