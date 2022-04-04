import data.set.basic data.set.function
open set
open classical

-- Assumirem en tot l'exercici que 
-- Ω és un tipus que farà de contenidor
variables (Ω Δ: Type)
-- a b c x y z seran elements de tipus Ω 
variables a b c x y z : Ω          
-- A B C X Y Z són conjunts amb elements de tipus Ω 
variables A B C X Y Z : set Ω
variable 𝕏 : set (set Ω)

def Union (𝕏 : set (set Ω)) : set Ω := 
{ x | ∃ (X : set Ω), ((X ∈ 𝕏) ∧ (x ∈ X))}

def Disj (Ω : Type) (𝕏 : set (set Ω)) : Prop :=
∀ (X Y: set Ω), (X ∈ 𝕏 ∧ Y ∈ 𝕏 ∧ X ≠ Y → (X∩Y=∅))

#check Disj Ω 𝕏

def AOC2 (𝕏: set (set Ω)) 
(h1: (∅ : set Ω) ∉ 𝕏) 
(h2: Disj Ω 𝕏) : Prop :=
∃ (f: set Ω →  Ω), 
∀ (X: set Ω), 
(X ∈ 𝕏 → f X ∈ X)

def InDr (f: Ω → Δ) 
(h1: function.surjective f) : Prop :=
∃ (g : Δ → Ω), (f ∘ g = (id : Δ → Δ))

#check AOC2 Ω

theorem T1 (Ω Δ :Type) (𝕏: set (set Ω)) (h1: (∅ : set Ω) ∉ 𝕏) (h2: Disj Ω 𝕏) (f: Ω → Δ) (h3: function.surjective f) : ((AOC2 Ω 𝕏 h1 h2) ↔ (InDr Ω Δ f h3)) :=
begin
  split,
  ---
  assume h4,
  sorry,
  sorry,
end



