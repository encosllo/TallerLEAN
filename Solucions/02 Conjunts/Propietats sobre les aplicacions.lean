-- Obre els recursos per a treballar amb conjunts
-- https://leanprover-community.github.io/mathlib_docs/data/set/basic.html

import data.set.basic data.set.function
open set 
-- open classical

-- Assumirem en tot l'exercici que 
-- Ω és un tipus que farà de contenidor
variables {I Ω Γ Δ: Type}
-- a b c x y z seran elements de tipus Ω 
variables a b c x y z : Ω  
-- a b c x y z seran elements de tipus Ω 
variables A B C X Y Z : set Ω    
-- P és una proposició sobre elements de tipus Ω
variable P : Ω → Prop 
-- famílies de conjunts de tipus Ω
variable 𝔸 : I → set Ω
-- R S T relacions sobre Ω
variables R S T : Ω → Ω → Prop  
-- funcions sobre elements de tipus Ω
variables f g : Ω → Ω

-- En aquesta sessió treballarem amb aplicacions
-- https://leanprover-community.github.io/mathematics_in_lean/sets_functions_and_relations.html#functions

#print function.injective 
#check function.injective f

#print function.surjective
#check function.surjective f

#print function.bijective
#check function.bijective f

-- Negació de la injectivitat
theorem TNegInj (f: Ω → Γ) : ¬ function.injective f ↔ ∃ (x y: Ω), f x = f y ∧ x ≠ y :=
begin
  split,
  -- Primera implicació
  assume h1,
  by_contradiction h2,
  have h3: function.injective f,
  intros x y,
  intro h3,
  by_contradiction h4,
  have h5: x ≠ y, exact h4,
  have h6: f x = f y ∧ x ≠ y, exact and.intro h3 h5,
  have h7: ∃ (x y: Ω), f x = f y ∧ x ≠ y, exact exists.intro x (exists.intro y h6),
  exact h2 h7,
  exact h1 h3,
  -- Segona implicació
  assume h1,
  by_contradiction h2,
  cases h1 with x h1,
  cases h1 with y h1,
  have h3: f x = f y, exact and.elim_left h1,
  have h4: ¬ x = y, exact and.elim_right h1,
  have h5: x = y, exact h2 h3, 
  exact h4 h5,
end  

-- La composició d'injectives és injectiva
theorem TCompInj (f: Ω → Γ) (g: Γ → Δ) (h1: function.injective f) (h2: function.injective g) : function.injective (g ∘ f) :=
begin
  intros x y,
  assume h3,
  have h4: g (f x) = g (f y), exact h3,
  have h5: f x = f y, exact h2 h4,
  exact h1 h5, 
end

#check function.injective f 

-- Si la composició (g∘f) és injectiva, aleshores f és injectiva
theorem TCompDInj (f: Ω → Γ) (g: Γ → Δ) (h1: function.injective (g ∘ f)) : (function.injective f) :=
begin 
  intros x y,
  assume h2,
  have h3: (g ∘ f) x = (g ∘ f) y,
  exact (calc
    (g ∘ f) x = g (f x)     : by refl
    ...       = g (f y)     : by rw h2 
    ...       = (g ∘ f) y   : by refl
  ),
  exact h1 h3,
end

-- Negació de la sobrejectivitat
theorem TNegSob (f: Ω → Γ) : ¬ function.surjective f ↔ ∃ (z: Γ), ∀ (x : Ω), f x ≠ z :=
begin
  split,
  -- Primera implicació
  assume h1,
  by_contradiction h2,
  have h3: function.surjective f,
  intro z,
  by_contradiction h3,
  have h4: ∀ (x : Ω), f x ≠ z,
  intro x,
  have h4: ¬ f x = z,
  by_contradiction h5,
  have h6: ∃ (a : Ω), f a = z, exact exists.intro x h5,
  exact h3 h6,
  exact h4,
  have h5: ∃ (z : Γ), ∀ (x : Ω), f x ≠ z, exact exists.intro z h4,
  exact h2 h5,
  exact h1 h3,
  -- Segona implicació
  assume h1,
  by_contradiction h2,
  cases h1 with z h1,
  have h3: ∃ (x : Ω), f x = z, exact h2 z,
  cases h3 with x h3,
  have h4: f x ≠ z, exact h1 x,
  exact h4 h3,
end  

-- La composició de sobrejectives és sobrejectiva
theorem TCompSob (f: Ω → Γ) (g: Γ → Δ) (h1: function.surjective f) (h2: function.surjective g) : function.surjective (g ∘ f) :=
begin
  intro c,
  have h3: ∃ (b : Γ), g b = c, exact h2 c,
  cases h3 with b h3,
  have h4: ∃ (a : Ω), f a = b, exact h1 b,
  cases h4 with a h4,
  have h5: (g ∘ f) a = c,
  exact (calc
    (g ∘ f) a = g (f a)   : by refl
    ...       = g b       : by rw h4
    ...       = c         : h3
  ),
  exact exists.intro a h5,
end

-- Si la composició (g∘f) és sobrejectiva, aleshores g és sobrejectiva
theorem TCompDSob (f: Ω → Γ) (g: Γ → Δ) (h1: function.surjective (g ∘ f)) : (function.surjective g) :=
begin 
  intro z,
  have h2: ∃ (x : Ω), g (f x) = z,
  exact h1 z,
  cases h2 with x h2,
  exact exists.intro (f x) h2,
end

-- Monos (simplificable a esquerra)
-- Si f ∘ g = f ∘ h, aleshores g = h 
def function.mono : (Ω → Γ) → Prop := λ (f : Ω → Γ), ∀ (Δ : Type), ∀ (g h: Δ → Ω), (f ∘ g = f ∘ h) → (g = h)   

-- Definim l'aplicació constant a x
-- κ kappa
-- (κ x) y = x 
def κ : Ω → (Ω → Ω) := λ (x: Ω), λ (y:Ω), x 

-- Una aplicació és mono si, i només si, és injectiva
theorem TCarMonoInj (f : Ω → Γ) : function.mono f ↔ function.injective f :=
begin
  split,
  -- Primera implicació
  assume h1,
  intros x y,
  assume h2,
  have h3 : (f ∘ (κ x)) = (f ∘ (κ y)),
  funext z,
  exact (calc 
    (f ∘ (κ x)) z = f ( (κ x) z)  : by refl
    ...           = f x           : by refl
    ...           = f y           : h2
    ...           = f ( (κ y) z)  : by refl 
    ...           = (f ∘ (κ y)) z : by refl
  ),
  have h4: κ x = κ y, exact h1 Ω (κ x) (κ y) h3,
  exact (calc
    x       = (κ x) x    : by refl
    ...     = (κ y) x    : by rw h4
    ...     = y          : by refl
  ), 
  -- Segona implicació
  assume h1,
  intro Δ,
  intros g h,
  assume h2,
  funext,
  have h3 : f (g x) = f (h x),
  exact (calc
    f (g x) = (f ∘ g) x     : by refl
    ...     = (f ∘ h) x     : by rw h2
    ...     = f (h x)       : by refl
  ),
  exact h1 h3,
end

-- Epis (simplificable a dreta)
-- Si g ∘ f = h ∘ f, aleshores g = h 
def function.epi : (Ω → Γ) → Prop := λ (f : Ω → Γ), ∀ (Δ : Type), ∀ (g h: Γ → Δ), (g ∘ f = h ∘ f) → (g = h)   

-- Definim l'aplicació constant a true
def veritat : Γ → Prop := λ (x : Γ), true 
-- Definim l'aplicació noigual que depén d'una variable x
def noigual : Γ → (Γ → Prop) := λ (x y : Γ), ¬ y = x 

-- Una aplicació és epi si, i només si, és sobrejectiva
theorem TCarEpiSob (f : Ω → Γ) : function.epi f ↔ function.surjective f :=
begin
  split,
  -- Primera implicació
  assume h1,
  intro z,
  by_contradiction h2,
  have h3: veritat ∘ f = (noigual z) ∘ f, 
  funext,
  have h4: (veritat ∘ f) x = true, by refl,
  have h5: ((noigual z) ∘ f) x = (¬ f x = z), by refl, 
  have h6: ∀ (x:Ω), ¬ f x = z,
  intro y,
  by_contradiction h7,
  have h8: ∃ (a:Ω), f a = z, exact exists.intro y h7,
  exact h2 h8,
  have h7: ¬ f x = z, exact h6 x,
  have h8: ¬ f x = z ↔ true,
  split,
  intro h8,
  exact true.intro,
  intro h9,
  exact h7,
  exact (calc 
    (veritat ∘ f) x = true : h4
    ...             = (¬ f x = z) : by rw h8
    ...             = ((noigual z) ∘ f) x : h5
  ),
  have h4: veritat = noigual z, exact h1 Prop veritat (noigual z) h3,
  have h5: true = (¬ z = z),
  exact (calc
    true  = veritat z : by refl
    ...   = (noigual z) z: by rw h4
    ...   = (¬ z = z) : by refl
  ), 
  have h6: ¬ (z=z) ↔ false,
  split,
  assume h7,
  have h8: z=z, exact eq.refl z,
  exact h7 h8,
  assume h7,
  exact false.elim h7,
  have h7: true ↔ false,
  split,
  assume h7,
  have h8: ¬ z = z, exact eq.subst h5 h7,
  exact iff.elim_left h6 h8,
  assume h7,
  exact false.elim h7, 
  have h8: true, exact true.intro,
  exact iff.elim_left h7 h8,
-- Segona implicació
  assume h1,
  intro Δ,
  intros g h,
  assume h2,
  funext,
  have h3: ∃ (z:Ω), f z = x, exact h1 x,
  cases h3 with z h3,
  exact (calc 
    g x   = g (f z)   : by rw h3
    ...   = (g ∘ f) z : by refl
    ...   = (h ∘ f) z : by rw h2
    ...   = h (f z)   : by refl
    ...   = h x       : by rw h3
  ), 
end


