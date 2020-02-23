(* Inductive day : Type :=
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
  
Compute (next_weekday saturday).

Example test_next:
  (next_weekday(next_weekday(saturday))) = tuesday.
  
Proof. simpl. reflexivity. Qed. *)

(*
Inductive bool : Type :=
  | true
  | false.
  
Definition negb (b: bool) :=
  match b with
  | true => false
  | false => true
  end.
  
Definition andb (b1: bool) (b2: bool) :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
*)

(*Level 1 -- nandb*)

Definition nandb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => (negb b2)
  | false => true
  end.
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.


(*Level 1 -- nandb3*)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
(andb b1 (andb b2 b3)).

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.


(* Check negb.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p: rgb).

Definition monochrome (c: color) := 
  match c with
  | black => true
  | white => true
  | primary p => false
  end.



Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0).

Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.
  
Compute (all_zero (bits B1 B0 B1 B0)).
Compute (all_zero (bits B1 B1 B1 B1)).
Compute (all_zero (bits B0 B0 B0 B0)).

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat) .

Definition pred (n : nat) : nat := 
  match n with 
    | O => O
    | S n' => n'
  end.

End NatPlayground.

Check (S (S (S 2))). *)

(*Level 1 -- factorial*)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
  
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.
  
Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => (mult (factorial n') n)
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.







