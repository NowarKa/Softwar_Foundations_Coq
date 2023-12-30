From Coq Require Export String.

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday tuesday).

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Compute (negb true).

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

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

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => andb b2 b3
  | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | white
  | black
  | primary (p : rgb).

Module TuplePlayground.

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

End TuplePlayground.



Module Natplayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n1 => n1
  end.

End Natplayground.

Fixpoint even (n : nat) : bool :=
  match n with
  | O  => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n : nat) : bool :=
  negb (even n).

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => plus n' (S m)
  end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _=> O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S O => m
  | S n' => plus m (mult n' m)
  end.

End Playground2.

Fixpoint exp (n m : nat) : nat :=
  match n with
  | O => 1
  | S n' => mult m (exp n' m)
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Fixpoint eqb (n m : nat): bool :=
  match n, m with
  | O, O => true
  | _, O => false
  | O, _ => false
  | S n', S m' => eqb n' m'
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
