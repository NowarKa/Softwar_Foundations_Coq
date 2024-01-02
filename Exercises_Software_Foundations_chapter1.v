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




