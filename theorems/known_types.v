(*Require Import a.*)

Inductive bit : Type :=
  | bit_zero
  | bit_one
.

Check (0, true).

Require Import Bool.

Definition is_zero b :=
	match b with
  | bit_zero => true
  | bit_one => false
  end
.
Definition is_one b := negb (is_zero b).

Example test_is_zero_zero: is_zero bit_zero = true.
Proof. simpl. reflexivity. Qed.
Example test_is_zero_one: is_zero bit_one = false.
Proof. simpl. reflexivity. Qed.
Example test_is_one_zero: is_one bit_zero = false.
Proof. simpl. reflexivity. Qed.
Example test_is_one_one: is_one bit_one = true.
Proof. simpl. reflexivity. Qed.
