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
  sorry,
end

-- 4.2 Introducció de la conjunció
theorem T42 (A B : Prop) (h1 : A) (h2 : B) : A ∧ B :=
begin
  sorry,
end

-- 4.3 Eliminació de la conjunció
theorem T41a (A B : Prop) (h1: A ∧ B) : A :=
begin
  sorry,
end 

theorem T41b (A B : Prop) (h1: A ∧ B) : B :=
begin
  sorry,
end 

-- 4.4 Introducció de la implicació
theorem T44 (A B : Prop) (h1 : B) : A → B :=
begin
  sorry,
end

-- 4.5 Eliminació de la implicació
theorem T45 (A B : Prop) (h1: A → B) (h2: A) : B :=
begin
  sorry,
end

-- 4.6 Introducció de la disjunció
theorem T46a (A B : Prop) (h1: A) : A ∨ B :=
begin
  sorry,
end

theorem T46b (A B : Prop) (h1: A) : B ∨ A :=
begin
  sorry,
end

-- 4.7 Eliminació de la disjunció
theorem T47 (A B C : Prop) (h1: A ∨ B) (h2: A → C) (h3: B → C) : C :=
begin
  sorry,
end

-- 4.8 Introducció de la negació
theorem T48 (A B : Prop) (h1: A → B) (h2: ¬B) : ¬ A :=
begin
  sorry,
end

-- 4.9 Eliminació de la negació
theorem T49 (A : Prop) (h1: ¬¬A) : A :=
begin
  sorry,
end

/----------------------------------------------------
-----------------------------------------------------
5. Exercicis explicats 
-----------------------------------------------------
----------------------------------------------------/

-- 5.1 Un molt senzill
theorem T51 (P Q : Prop) (h1: P) (h2: P → Q) : P ∧ Q :=
begin
  sorry,
end

-- 5.2 Una mica més complicat
theorem T52 (P Q R : Prop) (h1: P ∧ Q → R) (h2: Q → P) (h3: Q) : R :=
begin
  sorry,
end 

-- 5.3 Començant a suposar coses
theorem T53 (P Q R : Prop) (h1: P → Q) (h2: Q → R) : P → (Q ∧ R) :=
begin
  sorry,
end

-- 5.4 Usant la iteració
theorem T54 (P Q : Prop) (h1 : P) : Q → P :=
begin
  sorry,
end

-- 5.5 Reducció a l'absurd
theorem T55 (P Q : Prop) (h1 : P → Q) (h2: ¬Q) : ¬P :=
begin
  sorry,
end 

-- 5.6 Amb subdemostracions
theorem T56 (P Q R : Prop) (h1: P → (Q → R)) : Q → (P → R) :=
begin
  sorry,
end

-- 5.7 Un de prova per casos
theorem T57 (P Q R : Prop) (h1: P ∨ (Q ∧ R)) : P ∨ Q :=
begin
  sorry,
end

-- 5.8 Un per pensar-hi
theorem T58 (L M P I : Prop) (h1: (L ∧ M) → ¬P)  (h2: I → P) (h3: M) (h4: I) : ¬L :=
begin
  sorry,
end  

-- 5.9 La part esquerra buida
theorem T59 (P: Prop) : P → P :=
begin
  sorry,
end

-- 5.10 Suposar el contrari
theorem T510 (P: Prop) : ¬ (P ∧ ¬P) :=
begin
  sorry,
end

-- 5.11 Aquest sembla fàcil
theorem T511 (P: Prop) : P ∨ ¬P :=
begin
  sorry,
end

-- 5.12 Un d'interessant
theorem T512 (P Q : Prop) (h1: P ∨ Q) (h2: ¬P) : Q :=
begin
  sorry,
end

-- 5.13 Aquest me'l van posar a un examen
theorem T513 (A B C D : Prop) (h1: A ∨ B) (h2: A → C) (h3: ¬D → ¬B) : C ∨ D :=
begin
  sorry,
end

-- 5.14 Un "curt"
theorem T514 (A B: Prop) (h1: A ↔ B) : (A ∧ B) ∨ (¬A ∧ ¬B) :=
begin
  sorry,
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
  sorry,
end

-- 7.1.2. Eliminació de fals
theorem T712 (A : Prop) (h1: false) : A :=
begin
  sorry,
end 

-- 7.2 Regles de quatificadors
-- 7.2.2. Introducció de l'existencial
-- U és un tipus arbitrari i A és una proposició amb variable de tipus U
#check exists.intro
theorem T722 {U: Type} {A : U → Prop} (t : U) (h1: ∀ x, A x) : ∃ x, A x :=
begin
  sorry,
end

-- 7.2.3. Eliminació de l'existencial
#check exists.elim
theorem T723 {U: Type} {A : U → Prop} (B : Prop) (h1: ∃ x, A x) (h2: (∀ (a : U), A a → B)) : B :=
begin
  sorry,
end

-- 7.2.4 Introducció de l'universal
theorem T724 {U: Type} {A : U → Prop} (h1: ∀ (x : U), A x) : ∀ (y : U), A y :=
begin
  sorry,
end

-- 7.2.5 Eliminació de l'universal
theorem T725 {U: Type} {A : U → Prop} (h1: ∀ (x : U), A x) (t : U) : A t :=
begin
  sorry,
end

-- 7.3 Regles derivades
-- Llei de doble negació
theorem DN (A : Prop) : A ↔ ¬¬A :=
begin
  sorry,
end

-- Modus Tollens
theorem MT (A B: Prop) (h1: A → B) (h2: ¬B) : ¬A :=
begin
  sorry,
end

-- Sil·logisme disjuntiu (esquerra)
theorem SD1 (A B: Prop) (h1: A ∨ B) (h2: ¬A) : B :=
begin
  sorry,
end

-- Sil·logisme disjuntiu (dreta)
theorem SD2 (A B: Prop) (h1: A ∨ B) (h2: ¬B) : A :=
begin
  sorry,
end

-- Eliminació de ¬→ 
theorem ENI (A B: Prop) (h1: ¬ (A → B)) : A ∧ ¬B :=
begin
  sorry,
end

-- Eliminació de ¬∨  
theorem ENO (A B: Prop) (h1: ¬ (A ∨ B)) : ¬A ∧ ¬B :=
begin
  sorry,
end

-- Eliminació de ¬∧   
theorem ENC (A B: Prop) (h1: ¬ (A ∧ B)) : ¬A ∨ ¬B :=
begin
  sorry,
end

-- Teoremes que pots incorporar quan vulguis
theorem TQIQV1 (A: Prop) : A → A :=
begin
  sorry,
end

theorem TQIQV2 (A: Prop) : A ∨ ¬ A :=
begin
  sorry,
end

theorem TQIQV3 (A: Prop) : ¬ (A ∧ ¬ A) :=
begin
  sorry,
end

/----------------------------------------------------
-----------------------------------------------------
9. Exemples, molts exemples
-----------------------------------------------------
----------------------------------------------------/

theorem T91 (P Q : Prop) (h1: P) (h2: P → Q) : P ∧ Q :=
begin 
  sorry,
end

theorem T92 (P Q R: Prop) (h1: P ∧ Q → R) (h2: Q → P) (h3: Q) : R :=
begin
  sorry,
end 

theorem T93 (P Q R: Prop) (h1: P → Q) (h2: Q → R) : P → Q ∧ R :=
begin
  sorry,
end 

theorem T94 (P Q: Prop) (h1: P) : Q → P :=
begin
  sorry,
end 

theorem T95 (P Q : Prop) (h1: P → Q) (h2: ¬Q) : ¬P :=
begin
  sorry,
end

theorem T96 (P Q R: Prop) (h1: P→ (Q → R)) : Q → (P → R) :=
begin
  sorry,
end

theorem T97 (P Q R: Prop) (h1: P ∨ (Q ∧ R)) : P ∨ Q :=
begin
  sorry,
end

theorem T98 (L M P I: Prop) (h1: L ∧ M → ¬P) (h2: I → P) (h3: M) (h4: I) : ¬L :=
begin
  sorry,
end

theorem T99 (P : Prop) : P → P :=
begin
  sorry,
end

theorem T910 (P: Prop) : ¬(P ∧ ¬P) :=
begin
  sorry,
end

theorem T911 (P : Prop) : P ∨ ¬P :=
begin
   sorry,
end 

theorem T912 (P Q : Prop) (h1: P ∨ Q) (h2: ¬P) : Q :=
begin
  sorry,
end

theorem T913 (A B C D : Prop) (h1: A ∨ B) (h2: A → C) (h3: ¬D → ¬B) : C ∨ D :=
begin
  sorry,
end

theorem T914 (A B : Prop) (h1: A ↔ B) : (A ∧ B) ∨ (¬A ∧ ¬B) :=
begin
  sorry,
end

theorem T915 (P Q : Prop) (h1: P) : (P → Q) → Q :=
begin
  sorry,
end

theorem T916 (P Q R : Prop) (h1: P → Q) : (Q → R) → (P → R) :=
begin
  sorry,
end

theorem T917 (P Q R : Prop) (h1: P → Q) (h2: P → (Q → R)) : P → R :=
begin
  sorry,
end

theorem T918 (P Q R : Prop) (h1: P ∧ Q → R) : P → (Q → R) :=
begin
  sorry,
end

theorem T919 (P Q : Prop) (h1: ¬P) : P → Q :=
begin
  sorry,
end

theorem T920 (A B C : Prop) (h1: A ∧ (B ∨ C)) : (A ∧ B) ∨ (A ∧ C) :=
begin
  sorry,
end

theorem T921 (A B : Prop) (h1: ¬A ∨ B) : A → B :=
begin
  sorry,
end

theorem T922 (P Q : Prop) : ((P → Q) → P) → P :=
begin
  sorry,
end

theorem T923 {U: Type} {P Q : U → Prop} (a : U) (h1: P a) (h2: Q a) : ∃ x, (P x ∧ Q x) :=
begin
  have h3: P a ∧ Q a, from and.intro h1 h2,
  sorry,
end

theorem T924 {U: Type} {P Q : U → Prop} (h1: ∀ (x : U), (P x → Q x)) (a : U): P a → Q a :=
begin
  sorry,
end

theorem T925 {U: Type} {P Q R : U → Prop} (h1: ∀ (x : U), (P x → Q x)) (h2 : ∀ (x : U), (Q x → R x)): ∀ (x : U), P x → R x :=
begin
  sorry,
end

#check exists.elim
#check exists.intro
theorem T926 {U: Type} {P : U → U → Prop} (h1: ∃ (x : U), ∀ (y : U), P x y) : ∀ (y : U), ∃ (x : U),  P x y :=
begin
  sorry,
end





