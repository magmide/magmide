Add LoadPath "/home/blaine/personal/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List String Cpdt.CpdtTactics.
From stdpp Require Import base fin vector options.
Import ListNotations.

Ltac solve_crush := try solve [crush].
Ltac solve_assumption := try solve [assumption].
Ltac subst_injection H := injection H; intros; subst; clear H.

Theorem valid_index_not_None {T}: forall (l: list T) index,
	index < (length l) -> (lookup index l) <> None.
Proof.
	intros ????%lookup_ge_None; lia.
Qed.
Theorem valid_index_Some {T}: forall (l: list T) index,
	index < (length l) -> exists t, (lookup index l) = Some t.
Proof.
	intros ???%(lookup_lt_is_Some_2 l index);
	unfold is_Some in *; assumption.
Qed.

Definition closer_to target: nat -> nat -> Prop :=
	fun next cur => (target - next) < (target - cur).
(*Hint Unfold closer_to: core.*)

Theorem closer_to_well_founded target: well_founded (closer_to target).
Proof.
	apply (well_founded_lt_compat nat (fun a => target - a)); intros; assumption.
Defined.

Theorem closer_to_reverse: forall target cur next,
	(target - next) < (target - cur) -> cur < next.
Proof. lia. Qed.

Theorem closer_to_bounded_reverse: forall target cur next,
	cur < next -> cur < target -> (target - next) < (target - cur).
Proof. lia. Qed.

Definition closer_to_end {T} (arr: list T) := closer_to (length arr).

Theorem closer_to_end_well_founded {T} (arr: list T): well_founded (closer_to_end arr).
Proof. apply closer_to_well_founded. Qed.


Section well_founded_compatibility.
	Variable A B: Type.
	Variable RA: A -> A -> Prop.
	Variable RB: B -> B -> Prop.

	Variable RB_well_founded: well_founded RB.
	Variable f: A -> B.
	Hypothesis H_compat: forall a1 a2: A, RA a1 a2 <-> RB (f a1) (f a2).

	Theorem well_founded_compat: well_founded RA.
	Proof.
constructor.

unfold well_founded in *.
constructor.
intros.
rename y into a1; rename a into a2.

specialize (H_compat a1 a2).
remember (f a1) as b1; remember (f a2) as b2.
destruct H_compat as [H_compat_A H_compat_B].
specialize (H_compat_A H) as ?.


specialize (RB_well_founded b1) as Hb1.
specialize (RB_well_founded b2) as Hb2.
inversion Hb1.


specialize (Acc_inv RB_well_founded).

	Qed.

Check RB_well_founded.

EndSection well_founded_compatibility.

(*
forall (?A ?B: Type) (?RA: ?A -> ?A -> Prop) (?RW: ?B -> ?B -> Prop) -> _
*)


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
		| InstExit
		| InstMov (src: Operand) (dest: register)
		| InstAdd (val: Operand) (dest: register)

		(*| InstJump (to: string)*)
		(*| InstBranchEq (a: Operand) (b: Operand) (to: string)*)
		(*| InstBranchNeq (a: Operand) (b: Operand) (to: string)*)

		(*| InstStore (src: Operand) (dest: Operand)*)
		(*| InstLoad (src: Operand) (dest: register)*)
	.
	Hint Constructors Instruction: core.

	Inductive branching: Instruction -> Prop :=
		(*| branch_BranchEq: forall a b to, branching (InstBranchEq a b to)*)
		(*| branch_BranchNeq: forall a b to, branching (InstBranchNeq a b to)*)
		(*| branch_Jump: forall to, branching (InstJump to)*)
	.
	Hint Constructors branching: core.

	Inductive terminating: Instruction -> Prop :=
		| terminating_Exit: terminating InstExit
	.
	Hint Constructors terminating: core.

	(*Notation "'appear' instr program cur" :=
		((lookup cur program) = Some instr) (at level 70).*)

	Record MachineState := state {
		counter: nat;
		registers: RegisterBank
	}.

	Inductive step
		{program: list Instruction} {cur} {bank}
	: nat -> RegisterBank -> Prop :=
		| step_Mov: forall src dest,
			(lookup cur program) = Some (InstMov src dest)
			-> step
				(S cur)
				(vinsert dest (eval_operand bank src) bank)

		| step_Add: forall val dest,
			(lookup cur program) = Some (InstAdd val dest)
			-> step
				(S cur)
				(vinsert dest ((eval_operand bank val) + (bank !!! dest)) bank)

		(*| step_Jump: forall to,
			(lookup cur program) = Some (InstJump to)
			-> exists next, find_label program to = Some next
			-> step next bank*)

		(*| step_BranchEq_Eq: forall a b to,
			(lookup cur program) = Some (InstBranchEq a b to)
			-> a = b
			-> exists next, find_label program to = Some next
			-> step next bank
		| step_BranchEq_Neq: forall a b to,
			(lookup cur program) = Some (InstBranchEq a b to)
			-> a <> b
			-> step (S cur) bank*)

		(*| step_BranchNeq_Neq: forall a b to,
			(lookup cur program) = Some (InstBranchNeq Ne b to)
			-> a <> b
			-> exists next, find_label program to = Some next
			-> step next bank
		| step_BranchNeq_Eq: forall a b to,
			(lookup cur program) = Some (InstBranchNeq Ne b to)
			-> a = b
			-> step (S cur) bank*)
	.
	Hint Constructors step: core.

	Theorem terminating_stuck instr:
		terminating instr
		-> (
			forall program cur next b1 b2, (lookup cur program) = Some instr
			-> ~(@step program cur b1 next b2)
		).
	Proof.
		intros Hterminating ?????? Hstep;
		inversion Hterminating; inversion Hstep; crush.
	Qed.

	(*
	Inductive Acc (R: A -> A -> Prop) x: Prop :=
		Acc_intro: (forall y, R y x -> Acc R y) -> Acc R x
	*)

	Definition program_counter_well_founded program :=
		(*well_founded (fun next cur => exists b1 b2, @step program cur b1 next b2).*)
		forall b1 b2, well_founded (fun next cur => @step program cur b1 next b2).

	Inductive terminated: list Instruction -> Prop :=
		| terminated_End: forall instr,
			terminating instr
			-> terminated [instr]

		| terminated_Cons: forall instr rest,
			~(branching instr)
			-> ~(terminating instr)
			-> terminated rest
			-> terminated (instr :: rest)
	.
	Hint Constructors terminated: core.

	Theorem terminated_step_increments program:
		terminated program
		-> forall cur next b1 b2, @step program cur b1 next b2
		-> next = S cur.
	Proof.
		intros Hterminated ???? Hstep;
		inversion Hterminated; inversion Hstep; crush.
	Qed.

	(*
	*)


	Theorem terminated_always_terminates: forall program,
		terminated program
		-> program_counter_well_founded program.
	Proof.
unfold program_counter_well_founded.
intros.
induction H.
-
specialize (terminating_stuck H).
intros.
constructor.

+
crush.
constructor.
intros.
unfold not in H.
specialize (H0 H).
apply H0 in H.

apply H0 in H.


intros.


-

constructor.

(*
either terminated shows that we only have one terminating instruction left, in which case no step can be produced and so this is the root
or
*)

apply (well_founded_lt_compat nat (fun a => target - a)).

intros ?. induction 1.

-



	Qed.


	Theorem existent_not_stuck: forall program cur bank instr,
		(lookup cur program) = Some instr
		->
			terminating instr
			\/ exists cur' bank', @step program cur bank cur' bank'.
	Proof. intros ??? [] ?; eauto. Qed.

	Theorem terminated_wf: forall program,
		terminated program
		->
		-> well_founded (remaining)

	Theorem terminated_not_stuck: forall program,
		terminated program
		->

		(lookup cur program) = Some instr
		->
			terminating instr
			\/ exists next bank', @step program cur bank next bank'.
	Proof. intros ??? [] ?; eauto. Qed.


	Fixpoint execute_program_unsafe
		(fuel: nat) (program: list Instruction)
		(cur: nat) (bank: RegisterBank)
	: option RegisterBank :=
		match (lookup cur program) with
		| None => None
		| Some i => match fuel, i with
			| _, InstExit => Some bank
			| 0, _ => None
			| S f, InstMov src dest => execute_program_unsafe
				f program (S cur)
				(vinsert dest (eval_operand bank src) bank)
			| S f, InstAdd val dest => execute_program_unsafe
				f program (S cur)
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
