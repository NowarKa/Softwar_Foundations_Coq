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


