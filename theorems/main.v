Require Import List String.
Import ListNotations.

From stdpp Require Import base fin vector options.

Example t1: ([# 4; 2] !!! 0%fin) = 4.
Proof. reflexivity. Qed.


Section Sized.
	Variable size: nat.
	Notation RegisterBank := (vec nat size).
	Notation register := (fin size).

	Inductive Operand: Type :=
		| Literal (n: nat)
		| Register (r: register)
	.

	Definition eval_operand
		(bank: RegisterBank) (operand: Operand)
	: nat :=
		match operand with
		| Literal n => n
		| Register r => (bank !!! r)
		end
	.

	(*Definition label := option string.*)
	Inductive Instruction :=
		| InstMov (src: Operand) (dest: register)
		| InstAdd (val: Operand) (dest: register)
		(*| InstBranchEq (a: Operand) (b: Operand) (to: label)*)
		(*| InstBranchNeq (a: Operand) (b: Operand) (to: label)*)
		| InstExit
	.

	(*Record State := state { counter: nat; bank: RegisterBank }.*)

	Inductive step
		{program: list Instruction} {counter} {bank}
	: nat -> RegisterBank -> Prop :=
		| step_Mov: forall src dest,
			(lookup counter program) = Some (InstMov src dest)
			-> step
				(S counter)
				(vinsert dest (eval_operand bank src) bank)
		| step_Add: forall val dest,
			(lookup counter program) = Some (InstAdd val dest)
			-> step
				(S counter)
				(vinsert dest ((eval_operand bank val) + (bank !!! dest)) bank)
	.
	Hint Constructors step: core.

	Theorem step_pointing_not_stuck: forall (program: list Instruction) counter bank i,
		(lookup counter program) = Some i
		-> (i = InstExit) \/ exists counter' bank', @step program counter bank counter' bank'.
	Proof.
		intros ??? [] ?; try solve [auto]; right; eauto.
	Qed.

	Fixpoint execute_program_unsafe
		(fuel: nat) (program: list Instruction)
		(counter: nat) (bank: RegisterBank)
	: option RegisterBank :=
		match (lookup counter program) with
		| None => None
		| Some i => match fuel, i with
			| _, InstExit => Some bank
			| 0, _ => None
			| S f, InstMov src dest => execute_program_unsafe
				f program (S counter)
				(vinsert dest (eval_operand bank src) bank)
			| S f, InstAdd val dest => execute_program_unsafe
				f program (S counter)
				(vinsert dest ((eval_operand bank val) + (bank !!! dest)) bank)
			end
		end
	.
End Sized.

Arguments Literal {size} _.
Arguments Register {size} _.

Arguments execute_program_unsafe {size} _ _ _ _.

Arguments InstMov {size} _ _.
Arguments InstAdd {size} _ _.
(*Arguments InstBranchEq {size} _ _ _.*)
(*Arguments InstBranchNeq {size} _ _ _.*)
Arguments InstExit {size}.


Definition redundant_additions: list (Instruction 1) := [
	InstMov (Literal 0) (0%fin);
	InstAdd (Literal 1) (0%fin);
	InstAdd (Literal 1) (0%fin);
	InstAdd (Literal 1) (0%fin);
	InstAdd (Literal 1) (0%fin);
	InstAdd (Literal 1) (0%fin);
	InstExit
].
Example test__redundant_additions:
	execute_program_unsafe
		(length redundant_additions) redundant_additions 0 [#0] = Some [#5].
Proof. reflexivity. Qed.


Definition redundant_doubling: list (Instruction 1) := [
	InstMov (Literal 1) (0%fin);
	InstAdd (Register 0%fin) (0%fin);
	InstAdd (Register 0%fin) (0%fin);
	InstAdd (Register 0%fin) (0%fin);
	InstExit
].
Example test__redundant_doubling:
	execute_program_unsafe
		(length redundant_doubling) redundant_doubling 0 [#0] = Some [#8].
Proof. reflexivity. Qed.

(*
that can run a program to completion but can fail and requires fuel
then prove that a particular linear program can be run with a *safe* variant since it decreases on a well-founded order
then prove that any purely dag-like program can be run safely
then figure out how to prove that any labeled program that proof justifies cyclic jumps can be run safely
*)

(*
Definition mergeSort: list A -> list A.
refine (Fix lengthOrder wf (fun => list A)
	(fun
		(ls: list A)
		(mergeSort: forall ls': list A, lengthOrder ls' ls -> list A)
	=>
			if le_lt_dec 2 (length ls)
			then let lss := split ls in
			merge (mergeSort (fst lss)) (mergeSort (snd lss))
			else ls)
); subst lss; eauto.
Defined.
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




Inductive Result (T: Type) (E: Type): Type :=
	| Ok (value: T)
	| Err (error: E).

Arguments Ok {T} {E} _.
Arguments Err {T} {E} _.
