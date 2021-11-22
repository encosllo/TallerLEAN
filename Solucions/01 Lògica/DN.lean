/-Deducció Natural - Solucions-/
open classical

-- Exercicis de Daniel Clemente 
-- https://www.danielclemente.com/
-- CA https://www.danielclemente.com/logica/dn.ca.pdf
-- ES https://www.danielclemente.com/logica/dn.pdf
-- EN https://www.danielclemente.com/logica/dn.en.pdf
-- EO https://www.danielclemente.com/logica/dn.eo.pdf


/----------------------------------------------------
-----------------------------------------------------
4. Les regles
-----------------------------------------------------
----------------------------------------------------/

-- 4.1 Iteració
theorem T41 (A : Prop) (h1 : A) : A :=
begin
  exact h1,
end

-- 4.2 Introducció de la conjunció
theorem T42 (A B : Prop) (h1 : A) (h2 : B) : A ∧ B :=
begin
  exact and.intro h1 h2,
end

-- 4.3 Eliminació de la conjunció
theorem T41a (A B : Prop) (h1: A ∧ B) : A :=
begin
  exact and.elim_left h1,
end 

theorem T41b (A B : Prop) (h1: A ∧ B) : B :=
begin
  exact and.elim_right h1,
end 

-- 4.4 Introducció de la implicació
theorem T44 (A B : Prop) (h1 : B) : A → B :=
begin
  assume h2,
  exact h1,
end

-- 4.5 Eliminació de la implicació
theorem T45 (A B : Prop) (h1: A → B) (h2: A) : B :=
begin
  exact h1 h2,
end

-- 4.6 Introducció de la disjunció
theorem T46a (A B : Prop) (h1: A) : A ∨ B :=
begin
  exact or.inl h1,
end

theorem T46b (A B : Prop) (h1: A) : B ∨ A :=
begin
  exact or.inr h1,
end

-- 4.7 Eliminació de la disjunció
theorem T47 (A B C : Prop) (h1: A ∨ B) (h2: A → C) (h3: B → C) : C :=
begin
  cases h1 with h4 h4,
  -- Cas 1
  exact h2 h4,
  -- Cas 2
  exact h3 h4,
end

-- 4.8 Introducció de la negació
theorem T48 (A B : Prop) (h1: A → B) (h2: ¬B) : ¬ A :=
begin
  by_contradiction h3,
  exact h2 (h1 h3),
end

-- 4.9 Eliminació de la negació
theorem T49 (A : Prop) (h1: ¬¬A) : A :=
begin
  by_contradiction h2,
  exact h1 h2,
end

/----------------------------------------------------
-----------------------------------------------------
5. Exercicis explicats 
-----------------------------------------------------
----------------------------------------------------/

-- 5.1 Un molt senzill
theorem T51 (P Q : Prop) (h1: P) (h2: P → Q) : P ∧ Q :=
begin
  exact and.intro h1 (h2 h1),
end

-- 5.2 Una mica més complicat
theorem T52 (P Q R : Prop) (h1: P ∧ Q → R) (h2: Q → P) (h3: Q) : R :=
begin
  exact h1 (and.intro (h2 h3) h3),
end 

-- 5.3 Començant a suposar coses
theorem T53 (P Q R : Prop) (h1: P → Q) (h2: Q → R) : P → (Q ∧ R) :=
begin
  assume h3,
  have h4 : Q, from h1 h3,
  have h5 : R, from h2 h4,
  exact and.intro h4 h5,
end

-- 5.4 Usant la iteració
theorem T54 (P Q : Prop) (h1 : P) : Q → P :=
begin
  assume h2,
  exact h1,
end

-- 5.5 Reducció a l'absurd
theorem T55 (P Q : Prop) (h1 : P → Q) (h2: ¬Q) : ¬P :=
begin
  by_contradiction h3,
  exact h2 (h1 h3),
end 

-- 5.6 Amb subdemostracions
theorem T56 (P Q R : Prop) (h1: P → (Q → R)) : Q → (P → R) :=
begin
  assume h2,
  assume h3,
  exact (h1 h3) h2,
end

-- 5.7 Un de prova per casos
theorem T57 (P Q R : Prop) (h1: P ∨ (Q ∧ R)) : P ∨ Q :=
begin
  cases h1 with h2 h2,
  -- Cas 1
  exact or.inl h2,
  -- Cas 2
  exact or.inr (and.elim_left h2),
end

-- 5.8 Un per pensar-hi
theorem T58 (L M P I : Prop) (h1: (L ∧ M) → ¬P)  (h2: I → P) (h3: M) (h4: I) : ¬L :=
begin
  by_contradiction h5,
  have h6: L ∧ M, from and.intro h5 h3,
  have h7: ¬P, from h1 h6,
  have h8: P, from h2 h4,
  exact h7 h8,
end  

-- 5.9 La part esquerra buida
theorem T59 (P: Prop) : P → P :=
begin
  assume h1,
  exact h1,
end

-- 5.10 Suposar el contrari
theorem T510 (P: Prop) : ¬ (P ∧ ¬P) :=
begin
  by_contradiction h1,
  have h2: P, from and.elim_left h1,
  have h3: ¬P, from and.elim_right h1,
  exact h3 h2,
end

-- 5.11 Aquest sembla fàcil
theorem T511 (P: Prop) : P ∨ ¬P :=
begin
  by_contradiction h1,
  have h2: P,
  by_contradiction h2,
  have h3: P ∨ ¬P, from or.inr h2,
  exact h1 h3,
  have h3: P ∨ ¬P, from or.inl h2,
  exact h1 h3,
end

-- 5.12 Un d'interessant
theorem T512 (P Q : Prop) (h1: P ∨ Q) (h2: ¬P) : Q :=
begin
  have h3: P → Q,
  assume h4,
  exact false.elim (h2 h4),
  cases h1 with h4 h4,
  -- Cas 1
  exact false.elim (h2 h4),
  -- Cas 2
  exact h4,
end

-- 5.13 Aquest me'l van posar a un examen
theorem T513 (A B C D : Prop) (h1: A ∨ B) (h2: A → C) (h3: ¬D → ¬B) : C ∨ D :=
begin
  cases h1 with h4 h4,
  -- Cas 1
  have h5: C, from h2 h4, 
  exact or.inl h5,
  -- Cas 2
  have h5: D, 
  by_contradiction h6,
  have h7: ¬B, from h3 h6, 
  exact h7 h4,
  exact or.inr h5,
end

-- 5.14 Un "curt"
theorem T514 (A B: Prop) (h1: A ↔ B) : (A ∧ B) ∨ (¬A ∧ ¬B) :=
begin
  have h2: A → B, from iff.elim_left h1,
  have h3: B → A, from iff.elim_right h1,
  have h4: A ∨ ¬A, from em A,
  cases h4 with h5 h5,
  -- Cas 1
  have h6: B, from h2 h5,
  have h7: A ∧ B, from and.intro h5 h6,
  exact or.inl h7,
  -- Cas 2
  have h6: ¬B,
  by_contradiction h7,
  have h8: A, from h3 h7,
  exact h5 h8,
  have h7: ¬A ∧ ¬B, from and.intro h5 h6,
  exact or.inr h7,
end

/----------------------------------------------------
-----------------------------------------------------
7. Complicant-ho una mica més
-----------------------------------------------------
----------------------------------------------------/

-- 7.1 Regles de cert i fals
-- 7.1.1 Introducció de cert
theorem T711 : true :=
begin 
  exact true.intro,
end

-- 7.1.2. Eliminació de fals
theorem T712 (A : Prop) (h1: false) : A :=
begin
  exact false.elim h1,
end 

-- 7.2 Regles de quatificadors
-- 7.2.2. Introducció de l'existencial
-- U és un tipus arbitrari i A és una proposició amb variable de tipus U
#check exists.intro
theorem T722 {U: Type} {A : U → Prop} (t : U) (h1: ∀ x, A x) : ∃ x, A x :=
begin
  have h2: A t, from h1 t,
  exact exists.intro t h2,
end

-- 7.2.3. Eliminació de l'existencial
#check exists.elim
theorem T723 {U: Type} {A : U → Prop} (B : Prop) (h1: ∃ x, A x) (h2: (∀ (a : U), A a → B)) : B :=
begin
  have h3: (∀ (a : U), A a → B) → B, from exists.elim h1,
  exact h3 h2,
end

-- 7.2.4 Introducció de l'universal
theorem T724 {U: Type} {A : U → Prop} (h1: ∀ (x : U), A x) : ∀ (y : U), A y :=
begin
  intro y,
  exact h1 y,
end

-- 7.2.5 Eliminació de l'universal
theorem T725 {U: Type} {A : U → Prop} (h1: ∀ (x : U), A x) (t : U) : A t :=
begin
  exact h1 t,
end

-- 7.3 Regles derivades
-- Llei de doble negació
theorem DN (A : Prop) : A ↔ ¬¬A :=
begin
  have h1: A ∨ ¬A, from em A,
  cases h1 with h2 h2,
  -- Cas 1
  have h3: ¬¬A → A,
  assume h3,
  exact h2,
  have h4: A → ¬¬A,
  assume h4,
  by_contradiction h5,
  exact h5 h4,
  exact iff.intro h4 h3,
  -- Cas 2
  have h3: ¬¬A → A,
  assume h3,
  exact false.elim (h3 h2),
  have h4: A → ¬¬A,
  assume h4,
  exact false.elim (h2 h4),
  exact iff.intro h4 h3,
end

-- Modus Tollens
theorem MT (A B: Prop) (h1: A → B) (h2: ¬B) : ¬A :=
begin
  by_contradiction h3,
  exact h2 (h1 h3),
end

-- Sil·logisme disjuntiu (esquerra)
theorem SD1 (A B: Prop) (h1: A ∨ B) (h2: ¬A) : B :=
begin
  cases h1 with h3 h3,
  -- Cas 1
  exact false.elim (h2 h3),
  -- Cas 2
  exact h3,
end

-- Sil·logisme disjuntiu (dreta)
theorem SD2 (A B: Prop) (h1: A ∨ B) (h2: ¬B) : A :=
begin
  cases h1 with h3 h3,
  -- Cas 1
  exact h3,
  -- Cas 2
  exact false.elim (h2 h3),
end

-- Eliminació de ¬→ 
theorem ENI (A B: Prop) (h1: ¬ (A → B)) : A ∧ ¬B :=
begin
  have h2: ¬B,
  by_contradiction h3,
  have h4: A → B,
  assume h4,
  exact h3,
  exact h1 h4,
  have h3: A,
  by_contradiction h3,
  have h4: A → B,
  assume h4,
  exact false.elim (h3 h4),
  exact h1 h4,
  exact and.intro h3 h2,
end

-- Eliminació de ¬∨  
theorem ENO (A B: Prop) (h1: ¬ (A ∨ B)) : ¬A ∧ ¬B :=
begin
  have h2: ¬A,
  by_contradiction h2,
  have h3: A ∨ B, from or.inl h2,
  exact h1 h3,
  have h3: ¬B,
  by_contradiction h3,
  have h4: A ∨ B, from or.inr h3,
  exact h1 h4,
  exact and.intro h2 h3,
end

-- Eliminació de ¬∧   
theorem ENC (A B: Prop) (h1: ¬ (A ∧ B)) : ¬A ∨ ¬B :=
begin
  have h2: A ∨ ¬A, from em A,
  cases h2 with h3 h3,
  -- Cas 1
  have h4: B ∨ ¬B, from em B,
  cases h4 with h5 h5,
  -- Cas 1.1
  have h6: A ∧ B, from and.intro h3 h5,
  exact false.elim (h1 h6),
  -- Cas 1.2
  exact or.inr h5,
  -- Cas 2
  exact or.inl h3,
end

-- Teoremes que pots incorporar quan vulguis
theorem TQIQV1 (A: Prop) : A → A :=
begin
  assume h1,
  exact h1,
end

theorem TQIQV2 (A: Prop) : A ∨ ¬ A :=
begin
  exact em A,
end

theorem TQIQV3 (A: Prop) : ¬ (A ∧ ¬ A) :=
begin
  by_contradiction h1,
  exact (and.elim_right h1) (and.elim_left h1),
end

/----------------------------------------------------
-----------------------------------------------------
9. Exemples, molts exemples
-----------------------------------------------------
----------------------------------------------------/

theorem T91 (P Q : Prop) (h1: P) (h2: P → Q) : P ∧ Q :=
begin 
  exact and.intro h1 (h2 h1),
end

theorem T92 (P Q R: Prop) (h1: P ∧ Q → R) (h2: Q → P) (h3: Q) : R :=
begin
  have h4: P ∧ Q, from and.intro (h2 h3) h3,
  exact (h1 h4),
end 

theorem T93 (P Q R: Prop) (h1: P → Q) (h2: Q → R) : P → Q ∧ R :=
begin
  assume h3,
  have h4: Q, from h1 h3,
  have h5: R, from h2 h4,
  exact and.intro h4 h5,
end 

theorem T94 (P Q: Prop) (h1: P) : Q → P :=
begin
  assume h2,
  exact h1,
end 

theorem T95 (P Q : Prop) (h1: P → Q) (h2: ¬Q) : ¬P :=
begin
  by_contradiction h3,
  have h4: Q, from h1 h3,
  exact h2 h4,
end

theorem T96 (P Q R: Prop) (h1: P→ (Q → R)) : Q → (P → R) :=
begin
  assume h2,
  assume h3,
  exact (h1 h3) h2,
end

theorem T97 (P Q R: Prop) (h1: P ∨ (Q ∧ R)) : P ∨ Q :=
begin
  cases h1 with h2 h2,
  -- Cas 1
  exact or.inl h2,
  -- Cas 2
  exact or.inr (and.elim_left h2),
end

theorem T98 (L M P I: Prop) (h1: L ∧ M → ¬P) (h2: I → P) (h3: M) (h4: I) : ¬L :=
begin
  by_contradiction h5,
  have h6: L ∧ M, from and.intro h5 h3,
  have h7: P, from h2 h4, 
  have h8: ¬P, from h1 h6,
  exact h8 h7,
end

theorem T99 (P : Prop) : P → P :=
begin
  assume h1,
  exact h1,
end

theorem T910 (P: Prop) : ¬(P ∧ ¬P) :=
begin
  by_contradiction h1,
  exact (and.elim_right h1) (and.elim_left h1),
end

theorem T911 (P : Prop) : P ∨ ¬P :=
begin
   exact em P,
end 

theorem T912 (P Q : Prop) (h1: P ∨ Q) (h2: ¬P) : Q :=
begin
  cases h1 with h3 h3,
  -- Cas 1
  exact false.elim (h2 h3),
  -- Cas 2
  exact h3,
end

theorem T913 (A B C D : Prop) (h1: A ∨ B) (h2: A → C) (h3: ¬D → ¬B) : C ∨ D :=
begin
  cases h1 with h4 h4,
  -- Cas 1
  have h5: C, from h2 h4,
  exact or.inl h5,
  -- Cas 2
  have h5: D,
  by_contradiction h6,
  have h7: ¬B, from h3 h6,
  exact h7 h4,
  exact or.inr h5,
end

theorem T914 (A B : Prop) (h1: A ↔ B) : (A ∧ B) ∨ (¬A ∧ ¬B) :=
begin
  have h2: A → B, from iff.elim_left h1,
  have h3: B → A, from iff.elim_right h1,
  have h4: A ∨ ¬A, from em A,
  cases h4 with h5 h5,
  -- Cas 1
  have h6: B, from h2 h5,
  have h7: A ∧ B, from and.intro h5 h6,
  exact or.inl h7,
  -- Cas 2
  have h6: ¬B, 
  by_contradiction h7,
  have h8: A, from h3 h7,
  exact h5 h8,
  have h7: ¬A ∧ ¬B, from and.intro h5 h6,
  exact or.inr h7,
end

theorem T915 (P Q : Prop) (h1: P) : (P → Q) → Q :=
begin
  assume h2,
  exact h2 h1,
end

theorem T916 (P Q R : Prop) (h1: P → Q) : (Q → R) → (P → R) :=
begin
  assume h2,
  assume h3,
  exact h2 (h1 h3),
end

theorem T917 (P Q R : Prop) (h1: P → Q) (h2: P → (Q → R)) : P → R :=
begin
  assume h3,
  exact (h2 h3) (h1 h3),
end

theorem T918 (P Q R : Prop) (h1: P ∧ Q → R) : P → (Q → R) :=
begin
  assume h2,
  assume h3,
  have h4: P ∧ Q, from and.intro h2 h3,
  exact h1 h4,
end

theorem T919 (P Q : Prop) (h1: ¬P) : P → Q :=
begin
  assume h2,
  exact false.elim (h1 h2),
end

theorem T920 (A B C : Prop) (h1: A ∧ (B ∨ C)) : (A ∧ B) ∨ (A ∧ C) :=
begin
  have h2: A, from and.elim_left h1,
  have h3: B ∨ C, from and.elim_right h1,
  cases h3 with h4 h4,
  -- Cas 1
  have h5: A ∧ B, from and.intro h2 h4,
  exact or.inl h5,
  -- Cas 2
  have h5: A ∧ C, from and.intro h2 h4,
  exact or.inr h5,
end

theorem T921 (A B : Prop) (h1: ¬A ∨ B) : A → B :=
begin
  assume h2,
  cases h1 with h3 h3,
  -- Cas 1
  exact false.elim (h3 h2),
  -- Cas 2
  exact h3,
end

theorem T922 (P Q : Prop) : ((P → Q) → P) → P :=
begin
  assume h1,
  by_contradiction h2,
  have h3: ¬(P → Q),
  by_contradiction h3,
  exact h2 (h1 h3),
  have h4 : ¬Q,
  by_contradiction h4,
  have h5: P → Q,
  assume h5,
  exact h4,
  exact h2 (h1 h5), 
  have h5: P,
  have h6: P → Q,
  assume h5,
  exact false.elim (h2 h5),
  exact h1 h6,
  exact h2 h5,
end

theorem T923 {U: Type} {P Q : U → Prop} (a : U) (h1: P a) (h2: Q a) : ∃ x, (P x ∧ Q x) :=
begin
  have h3: P a ∧ Q a, from and.intro h1 h2,
  exact exists.intro a h3,
end

theorem T924 {U: Type} {P Q : U → Prop} (h1: ∀ (x : U), (P x → Q x)) (a : U): P a → Q a :=
begin
  exact h1 a,
end

theorem T925 {U: Type} {P Q R : U → Prop} (h1: ∀ (x : U), (P x → Q x)) (h2 : ∀ (x : U), (Q x → R x)): ∀ (x : U), P x → R x :=
begin
  assume x,
  assume h3,
  have h4: Q x, from (h1 x) h3,
  have h5: R x, from (h2 x) h4,
  exact h5,
end

#check exists.elim
#check exists.intro
theorem T926 {U: Type} {P : U → U → Prop} (h1: ∃ (x : U), ∀ (y : U), P x y) : ∀ (y : U), ∃ (x : U),  P x y :=
begin
  assume y,
  apply exists.elim h1, 
  assume x,
  assume h3,
  have h4: P x y, from h3 y,
  exact exists.intro x h4,
end





