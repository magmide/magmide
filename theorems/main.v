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
(*lookup_lt_Some*)

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

	Record MachineState := state {
		counter: nat;
		registers: RegisterBank
	}.
	Notation "'within' program cur" :=
		(cur.(counter) < (length program))
		(at level 10, program at next level, cur at next level, only parsing).

	Notation "'cur_instr' cur program" := (lookup cur.(counter) program)
		(at level 10, cur at next level, program at next level, only parsing).

	Notation "'eval' cur val" :=
		(eval_operand cur.(registers) val)
		(at level 10, cur at next level, val at next level, only parsing).

	Notation "'get' cur reg" :=
		(cur.(registers) !!! reg)
		(at level 10, cur at next level, reg at next level, only parsing).

	Notation "'update' cur dest val" :=
		(vinsert dest val cur.(registers))
		(at level 10, cur at next level, dest at next level, val at next level, only parsing).

	Notation "'incr' cur" :=
		(S cur.(counter))
		(at level 10, cur at next level, only parsing).

	Inductive step
		{program: list Instruction}
	: MachineState -> MachineState -> Prop :=
		| step_Mov: forall cur src dest,
			(cur_instr cur program) = Some (InstMov src dest)
			-> step cur (state
				(incr cur)
				(update cur dest (eval cur src))
			)

		| step_Add: forall cur val dest,
			(cur_instr cur program) = Some (InstAdd val dest)
			-> step cur (state
				(incr cur)
				(update cur dest ((eval cur val) + (get cur dest)))
			)

		(*| step_Jump: forall cur to,
			(cur_instr cur program) = Some (InstJump to)
			-> exists next, find_label program to = Some next
			-> step next bank*)

		(*| step_BranchEq_Eq: forall cur a b to,
			(cur_instr cur program) = Some (InstBranchEq a b to)
			-> a = b
			-> exists next, find_label program to = Some next
			-> step next bank
		| step_BranchEq_Neq: forall cur a b to,
			(cur_instr cur program) = Some (InstBranchEq a b to)
			-> a <> b
			-> step (S cur) bank*)

		(*| step_BranchNeq_Neq: forall cur a b to,
			(cur_instr cur program) = Some (InstBranchNeq Ne b to)
			-> a <> b
			-> exists next, find_label program to = Some next
			-> step next bank
		| step_BranchNeq_Eq: forall cur a b to,
			(cur_instr cur program) = Some (InstBranchNeq Ne b to)
			-> a = b
			-> step (S cur) bank*)
	.
	Hint Constructors step: core.

	Theorem step_always_within: forall program cur next,
		@step program cur next
		-> within program cur.
	Proof.
		intros ???; inversion 1;
		match goal with
		| [ H : _ !! counter _ = Some _ |- _ ] =>
			apply lookup_lt_Some in H; assumption
		end.
	Qed.


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

	Theorem terminating_stuck instr program cur next:
		terminating instr
		-> (cur_instr cur program) = Some instr
		-> ~(@step program cur next).
	Proof.
		intros Hterminating ? Hstep;
		inversion Hterminating; inversion Hstep; crush.
	Qed.

	(*
	Inductive Acc (R: A -> A -> Prop) x: Prop :=
		Acc_intro: (forall y, R y x -> Acc R y) -> Acc R x
	*)

	Inductive sequential: list Instruction -> Prop :=
		| sequential_End: forall instr,
			terminating instr
			-> sequential [instr]

		| sequential_Cons: forall instr rest,
			(*~(branching instr)*)
			sequential rest
			-> sequential (instr :: rest)
	.
	Hint Constructors sequential: core.

	Theorem sequential_not_empty program:
		sequential program -> 0 < length program.
	Proof. inversion 1; crush. Qed.

	Theorem sequential_step_increments program cur next:
		sequential program
		-> @step program cur next
		-> next.(counter) = (incr cur).
	Proof.
		intros Hsequential Hstep;
		inversion Hsequential; inversion Hstep; crush.
	Qed.

	Theorem sequential_step_safe program cur next:
		sequential program
		-> @step program cur next
		-> within program next.
	Proof.
intros Hsequential Hstep;
specialize (step_always_within Hstep) as Hwithin;
specialize (sequential_step_increments Hsequential Hstep) as Hincr;
rewrite -> Hincr.
induction Hsequential.
-
admit.

(*
inversion Hstep
subst; simpl in *; inversion H.
rewrite <- H0  in H1.
rewrite lookup_cons in H1.
assert (Hc: counter cur = 0) by lia.
rewrite Hc in *.
discriminate.*)
-
specialize (sequential_not_empty Hsequential) as Hrest.

simpl in *.
rewrite <- Hincr in *.
apply lt_n_S.



clear Hstep Hincr H H0; subst cur0.

assert (Hlenprogram: 1 < length program).
{
subst program.
simpl in *.
destruct (length rest); crush.

}

intros.


assert (Hmorerest: 1 < length rest).


simpl length in Hwithin.

crush.
specialize (Hs0 rest).

idtac.

crush.



unfold lookup in H1; unfold list_lookup in H1.

specialize (terminating_stuck H H1) as Hdumb.


+

subst.

rewrite <- H0 in *; simpl in *.


		Qed.

	Theorem sequential_always_terminates program:
		sequential program
		-> program_well_founded program.
	Proof.
unfold program_well_founded.
induction 1.

-
inversion H.
specialize (terminating_stuck H).
constructor; intros.
apply H1 in H2; try exfalso; solve_assumption.
+apply (absurd H2).

intros Hsequential.
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
		(cur_instr cur program) = Some instr
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

		(cur_instr cur program) = Some instr
		->
			terminating instr
			\/ exists next bank', @step program cur bank next bank'.
	Proof. intros ??? [] ?; eauto. Qed.


	Fixpoint execute_program_unsafe
		(fuel: nat) (program: list Instruction)
		(cur: nat) (bank: RegisterBank)
	: option RegisterBank :=
		match (cur_instr cur program) with
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
