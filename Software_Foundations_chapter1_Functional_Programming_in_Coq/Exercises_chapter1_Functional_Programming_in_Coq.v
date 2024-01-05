Require Export Course_chapter1_Functional_Programming_in_Coq.

(*==================================================*)
(*========Exercise: 1 star, standard (nandb)========*)
(*==================================================*)

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => negb(b2)
  | false => true
  end.

Example test_nanb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nanb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nanb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nanb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.



(*===================================================*)
(*========Exercise: 1 star, standard (andb3)=========*)
(*===================================================*)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => andb b2 b3
  | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.



(*===================================================*)
(*=======Exercise: 1 star, standard (factorial)======*)
(*===================================================*)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.



(*===================================================*)
(*=========Exercise: 1 star, standard (ltb)==========*)
(*===================================================*)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Definition ltb (n m : nat) : bool := 
  negb (leb m n).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.



(*=======================================================*)
(*=====Exercise: 1 star, standard (plus_id_exercise)=====*)
(*=======================================================*)

Theorem plus_id_exercise : forall n m p : nat,
n = m -> m = p -> n + m = n + p.

Proof.
intros n m p.
intros H1.
intros H2.
rewrite -> H1.
rewrite -> H2.
reflexivity.
Qed.



(*=======================================================*)
(*=========Exercise: 1 star, standard (mult_n_1)=========*)
(*=======================================================*)

Theorem plus_1_n : forall n : nat, 1 + n = S n.
Proof. intros n. reflexivity. Qed.

Theorem mult_n_O : forall n : nat, 0 = 0 * n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem commutativite : forall n m : nat, n * m = m * n.
Admitted.

Theorem mult_n_Sm : forall n m : nat, n * m + n = n * S m.
Admitted.

Theorem mult_n_1 : forall p : nat, p * 1 = p.
Proof. 
intros p. 
rewrite <- mult_n_Sm. 
rewrite -> commutativite. 
rewrite <- mult_n_O.
rewrite -> plus_O_n.
reflexivity.
Qed.



(*=========================================================*)
(*======Exercise: 2 stars, standard (andb_true_elim2)======*)
(*=========================================================*)

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.


Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
Proof.
intros b c.
rewrite <- andb_commutative.
destruct c eqn:Ec.
-destruct b eqn:Eb.
  +reflexivity.
  +reflexivity.
-destruct b eqn:Eb.
  +intros H. rewrite <- H. reflexivity.
  +intros H. rewrite <- H. reflexivity.
Qed.



(*==========================================================*)
(*======Exercise: 1 star, standard (zero_nbeq_plus_1)=======*)
(*==========================================================*)

Theorem zero_nbeq_plus_1 : forall n : nat, (eqb 0  (n + 1)) = false.
Proof. intros [|n].
-reflexivity.
-reflexivity.
Qed.



(*____________________________________________________________________________*)
(*_____________________________More exersises_________________________________*)
(*____________________________________________________________________________*)



(*==========================================================*)
(*==Exercise: 1 star, standard (identity_fn_applied_twice)==*)
(*==========================================================*)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof. intros f. intros H. intros b. rewrite -> H. rewrite <- H. reflexivity. Qed.



(*==========================================================*)
(*==Exercise: 1 star, standard (negation_fn_applied_twice)==*)
(*==========================================================*)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.

Proof. intros f. intros H. intros b. rewrite -> H. rewrite -> H.
rewrite -> negb_involutive. reflexivity. Qed.

Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.



(*==========================================================*)
(*===Exercise: 3 stars, standard, optional (andb_eq_orb)====*)
(*==========================================================*)

Lemma orb_commutative : forall b c : bool, b || c = c || b.
Proof. intros b c. destruct b eqn:B.
  -destruct c.
    +simpl. reflexivity.
    +simpl. reflexivity.
  -destruct c.
    +simpl. reflexivity.
    +simpl. reflexivity.
Qed.

Lemma or_false : forall b : bool, b || false = b.
Proof. intros b. destruct b.
  -reflexivity.
  -reflexivity.
Qed.

Lemma and_true : forall b : bool, b && true = b.
Proof. intros b. destruct b eqn:B.
-simpl. reflexivity.
-simpl. reflexivity.
Qed.

Theorem andb_eq_orb : forall b c : bool, (andb b c = orb b c) -> b = c.
Proof. intros b c. intros H. destruct b eqn:B.
-rewrite <- and_true. rewrite andb_commutative. rewrite H.
simpl. reflexivity.
-rewrite <- or_false. rewrite -> orb_commutative. rewrite <- H. simpl.
reflexivity.
Qed.




(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*+++++++++++++++++++Course Late Policies, Formalized+++++++++++++++++++++++++*)
(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)

Module LateDays.

Inductive letter : Type := 
| A | B | C | D | F.

Inductive modifier : Type :=
| Plus | Natural | Minus.

Inductive grade : Type := 
Grade (l:letter) (m:modifier).

Inductive comparison : Type :=
  | Eq
  | Lt
  | Gt.

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F
  end.

Theorem lower_letter_F_is_F: lower_letter F = F.
Proof. simpl. reflexivity. Qed.



(*==================================================*)
(*==Exercise: 1 star, standard (letter_comparison)==*)
(*==================================================*)

Theorem letter_comparison_Eq : forall l : letter, letter_comparison l l = Eq.
Proof. intros l. destruct l.
-reflexivity.
-reflexivity.
-reflexivity.
-reflexivity.
-reflexivity. Qed.




(*==================================================*)
(*==Exercise: 2 stars, standard (grade_comparison)==*)
(*==================================================*)

Definition grade_comparison (g1 g2 : grade) : comparison :=
  match (g1, g2) with
  | (Grade l1 m1, Grade l2 m2) => 
    match letter_comparison l1 l2 with
    | Eq => modifier_comparison m1 m2
    | _ => letter_comparison l1 l2 
    end
  end.

Example test_grade_comparison1 : (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. simpl. reflexivity. Qed.

Example test_grade_comparison2 : (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. simpl. reflexivity. Qed.

Example test_grade_comparison3 : (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. simpl. reflexivity. Qed.

Example test_grade_comparison4 :(grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. simpl. reflexivity. Qed.



(*=====================================================*)
(*==Exercise: 2 stars, standard (lower_letter_lowers)==*)
(*=====================================================*)

Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.

Proof. intros l. intros H. destruct l.
-reflexivity.
-reflexivity.
-reflexivity.
-reflexivity.
-simpl. rewrite <- H. reflexivity.
Qed.



(*=====================================================*)
(*======Exercise: 2 stars, standard (lower_grade)======*)
(*=====================================================*)

Definition lower_grade (g : grade) : grade :=
  match g with
  | Grade l m =>
    match m with
    | Plus => Grade l Natural
    | Natural => Grade l Minus
    | Minus => match l with
               | F => g 
               | _ => Grade (lower_letter l) Plus
               end
    end
  end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof. simpl. reflexivity. Qed.

Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof. reflexivity. Qed.

Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof. reflexivity. Qed.

Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof. reflexivity. Qed.

Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof. reflexivity. Qed.

Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof. reflexivity. Qed.

Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof. reflexivity. Qed.

Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof. reflexivity. Qed.



(*====================================================*)
(*==Exercise: 3 stars, standard (lower_grade_lowers)==*)
(*====================================================*)

Theorem lower_grade_lowers : forall (g : grade),
grade_comparison (Grade F Minus) g = Lt ->
grade_comparison (lower_grade g) g = Lt.

Proof. intros g. intros H. destruct g. destruct m.
-simpl. destruct l.
  +reflexivity.
  +reflexivity.
  +reflexivity.
  +reflexivity.
  +reflexivity.
-simpl. destruct l.
  +reflexivity.
  +reflexivity.
  +reflexivity.
  +reflexivity.
  +reflexivity.
-simpl. destruct l.
  +reflexivity.
  +reflexivity.
  +reflexivity.
  +reflexivity.
  +rewrite -> H. reflexivity.
Qed.


Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).


Theorem apply_late_policy_unfold :
  forall (late_days : nat) (g : grade),
    (apply_late_policy late_days g)
    =
    (if late_days <? 9 then g else
       if late_days <? 17 then lower_grade g
       else if late_days <? 21 then lower_grade (lower_grade g)
            else lower_grade (lower_grade (lower_grade g))).

Proof. intros n g. reflexivity. Qed.



(*===============================================================*)
(*==Exercise: 2 stars, standard (no_penalty_for_mostly_on_time)==*)
(*===============================================================*)

Theorem no_penalty_for_mostly_on_time :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = true) ->
    apply_late_policy late_days g = g.

Proof. intros n g. intros H. rewrite -> apply_late_policy_unfold. rewrite -> H.
reflexivity. Qed.



(*===============================================================*)
(*=======Exercise: 2 stars, standard (graded_lowered_once)=======*)
(*===============================================================*)

Theorem grade_lowered_once :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (grade_comparison (Grade F Minus) g = Lt) ->
    (apply_late_policy late_days g) = (lower_grade g).

Proof. intros n g. intros H1. intros H2. intros H3.
rewrite apply_late_policy_unfold. rewrite H1. rewrite H2. reflexivity. Qed.

End LateDays.




(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*+++++++++++++++++++++++++++++++Binary Numerals+++++++++++++++++++++++++++++++*)
(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).


Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => 0
  | B0 Z => 0
  | B1 Z => 1
  | B0 m' => 2*(bin_to_nat m')
  | B1 m' => 1 + 2*(bin_to_nat m')
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. reflexivity. Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr6 : bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.

