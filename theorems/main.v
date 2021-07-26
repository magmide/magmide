Require Import List String.
Import ListNotations.

From stdpp Require Import base fin vector options.

Definition Register := nat.
Definition RegisterBank n := vec Register n.

Example t1: ([# 4; 2] !!! 0%fin) = 4.
Proof. reflexivity. Qed.

Definition label := option string.


Inductive Operand :=
	| Literal (n: nat)
	| Register (r: register)
.

Notation RegisterBank := list nat (only parsing).

Inductive Instruction :=
	| InstMov (l: label) (src: Operand) (dest: register)
	| InstAdd (l: label) (a: Operand) (dest: register)
	(*| InstBranchEq (l: label) (a: Operand) (b: Operand) (to: label)*)
	| InstBranchNeq (l: label) (a: Operand) (b: Operand) (to: label)
	| InstExit (l: label) (return_val: Operand)
.


(*
I want to create a fixpoint
execute_program_unsafe

that can run a program to completion but can fail and requires fuel
then prove that a particular linear program can be run with a *safe* variant since it decreases on a well-founded order
then prove that any purely dag-like program can be run safely
then figure out how to prove that any labeled program that proof justifies cyclic jumps can be run safely

*)


Notation val := Operand (only parsing).
Notation expr := Instruction (only parsing).

Notation of_val := InstExit (only parsing).

Definition to_val (e: expr): option val :=
  match e with
  | InstExit _ v => Some v
  | _ => None
  end.

(*
	So the first program I'm interested in verifying is this one.
	I want to obviously verify it's safe and such, but also I want to be

main: (this label is implicit)
	{{ True }}
	Mov 0 $r1
	{{ $r1 = 0 }}
loop:
	{{ exists n < 10. $r1 = n }}
	Add 1 $r1
	{{ exists n <= 10. $r1 = n + 1}}
	BranchNeq $r1 10 loop
done:
	{{ $r1 = 10 }}
	Exit $r1

*)


Inductive Bit: Type := B0 | B1.
