Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List String Cpdt.CpdtTactics Coq.Program.Wf.
From stdpp Require Import base fin vector options natmap.
Import ListNotations.
Require Import theorems.utils.

(*From stdpp Require Import natmap.
Definition test__natmap_lookup_m: natmap nat := {[ 3 := 2; 0 := 2 ]}.
Example test__natmap_lookup: test__natmap_lookup_m !! 3 = Some 2.
Proof. reflexivity. Qed.

Example test__vec_total_lookup: ([# 4; 2] !!! 0%fin) = 4.
Proof. reflexivity. Qed.*)

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
	Notation Within program cur :=
		(cur.(counter) < (length program)) (only parsing).

	Notation cur_instr cur program :=
		(lookup cur.(counter) program) (only parsing).

	Notation get_instr cur program :=
		(@safe_lookup _ cur.(counter) program _) (only parsing).

	Notation eval cur val :=
		(eval_operand cur.(registers) val) (only parsing).

	Notation get cur reg :=
		(cur.(registers) !!! reg) (only parsing).

	Notation update cur dest val :=
		(vinsert dest val cur.(registers)) (only parsing).

	Notation incr cur :=
		(S cur.(counter)) (only parsing).

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

	(*Inductive step_trace program: forall cur next, (list @step program cur next) -> Prop :=
		| trace_Exit: forall cur next,
			@step program cur next
			-> (cur_instr next program) = Some InstExit
			-> trace program cur next [@step program cur next]
		| trace_Step
	.*)

	Theorem step_always_Within program cur next:
		@step program cur next -> Within program cur.
	Proof.
		inversion 1;
		match goal with
		| H: _ !! counter _ = Some _ |- _ =>
			apply lookup_lt_Some in H; assumption
		end.
	Qed.

	Inductive sequential: Instruction -> Prop :=
		| sequential_Mov: forall src dest, sequential (InstMov src dest)
		| sequential_Add: forall val dest, sequential (InstAdd val dest)
	.
	Hint Constructors sequential: core.
	(*Definition is_sequential*)

	Theorem sequential_always_next instr:
		sequential instr
		-> forall (program: list Instruction) cur next,
		(cur_instr cur program) = Some instr
		-> @step program cur next
		-> counter next = S (counter cur).
	Proof.
		intros ????? Hstep; destruct instr; inversion Hstep; auto.
	Qed.

	Inductive branching: Instruction -> Prop :=
		(*| branch_BranchEq: forall a b to, branching (InstBranchEq a b to)*)
		(*| branch_BranchNeq: forall a b to, branching (InstBranchNeq a b to)*)
		(*| branch_Jump: forall to, branching (InstJump to)*)
	.
	Hint Constructors branching: core.

	Inductive stopping: Instruction -> Prop :=
		| stopping_Exit: stopping InstExit
	.
	Hint Constructors stopping: core.
	Definition is_stopping: forall instr, {stopping instr} + {~(stopping instr)}.
		refine (fun instr =>
			match instr with | InstExit => Yes | _ => No end
		); try constructor; inversion 1.
	Defined.

	Theorem stopping_stuck instr:
		stopping instr
		-> forall program cur next,
		(cur_instr cur program) = Some instr
		-> ~(@step program cur next).
	Proof.
		intros Hstopping ???? Hstep;
		inversion Hstopping; inversion Hstep; crush.
	Qed.

	Theorem not_stopping_not_stuck instr:
		~(stopping instr)
		-> forall program cur,
		(cur_instr cur program) = Some instr
		-> exists next, @step program cur next.
	Proof.
		destruct instr; try contradiction; eauto.
	Qed.

	Notation NextStep program instr cur next :=
		((cur_instr cur (program%list)) = Some instr -> @step (program%list) cur next)
		(only parsing).

	Definition execute_instruction:
		forall instr (cur: MachineState), ~stopping instr
		-> {next: MachineState | forall program, NextStep program instr cur next}
	.
		refine (fun instr cur =>
			match instr with
			| InstMov src dest => fun _ => this (state
				(incr cur)
				(update cur dest (eval cur src))
			)
			| InstAdd val dest => fun _ => this (state
				(incr cur)
				(update cur dest ((eval cur val) + (get cur dest)))
			)
			| _ => fun _ => impossible
			end
		); destruct instr; try contradiction; auto.
	Defined.

	Definition execute_program_unsafe
		(program: list Instruction)
	:
		nat -> MachineState -> option MachineState
	.
		refine (fix go steps cur :=
			match (cur_instr cur program) with
			| None => None
			| Some instr =>
				if (is_stopping instr) then Some cur
				else match steps with
				| 0 => None
				| S steps' =>
					let (next, _) := (@execute_instruction instr cur _) in
					go steps' next
				end
			end
		); assumption.
	Defined.

	Notation WellFormed program :=
		(forall cur next, @step program cur next -> Within program next)
		(only parsing).

	Notation InstWellFormed len_program := (fun index instr =>
		forall program cur next,
		len_program <= (length program)
		-> lookup (index%nat) program = Some instr
		-> cur.(counter) = (index%nat)
		-> @step program cur next
		-> Within program next
	) (only parsing).

	Theorem step_implies_instr program cur next:
		@step program cur next -> exists instr, (cur_instr cur program) = Some instr.
	Proof. intros []; eauto. Qed.

	Notation IndexPairsWellFormed program :=
		(fun index_instr => InstWellFormed (length program) index_instr.1 index_instr.2)
		(only parsing).

	Theorem index_pairs_InstWellFormed_implies_WellFormed program:
		Forall (IndexPairsWellFormed program) (imap pair program)
		-> WellFormed program.
	Proof.
		intros H ?? Hstep; rewrite Forall_lookup in H;
		specialize (step_implies_instr Hstep) as [instr];
		specialize (H cur.(counter) (cur.(counter), instr));
		eapply H; eauto; apply index_pairs_lookup_forward; assumption.
	Qed.

	Definition check_instruction_well_formed len_program:
		forall index_instr, partial (InstWellFormed len_program index_instr.1 index_instr.2)
	.
		refine (fun index_instr =>
			if (is_stopping index_instr.2) then proven
			else if (lt_dec (S index_instr.1) len_program) then proven else unknown
			(*if (is_sequential instr)*)
		);
		destruct index_instr as [index instr]; simpl in *;
		intros ???? Hsome Hcounter Hstep; subst;
		try apply (stopping_stuck s Hsome) in Hstep;
		destruct instr; inversion Hstep; try contradiction; simpl in *; subst; lia.
	Defined.

	Definition execute_program_unknown_termination
		(program: list Instruction)
		(well_formed: WellFormed program)
	:
		nat -> forall cur, Within program cur -> option MachineState
	.
		refine (fix go steps cur _ :=
			let (instr, _) := (get_instr cur program) in
			if (is_stopping instr) then Some cur
			else match steps with
			| 0 => None
			| S steps' =>
				let (next, _) := (@execute_instruction instr cur _) in
				go steps' next _
			end
		); eauto.
	Defined.

	Section execute_program.
		Variable program: list Instruction.
		Variable well_formed: WellFormed program.
		Variable progress: MachineState -> MachineState -> Prop.
		Variable progress_wf: well_founded progress.
		Variable program_progress:
			forall cur next, @step program cur next -> progress next cur.

		Program Fixpoint execute_program
			cur (H: Within program cur) {wf progress cur}
		: MachineState :=
			let (instr, _) := (get_instr cur program) in
			if (is_stopping instr) then cur
			else
				let (next, _) := (@execute_instruction instr cur _) in
				execute_program next _
		.
		Solve All Obligations with eauto.
	End execute_program.

End Sized.

Arguments Literal {size} _.
Arguments Register {size} _.

Arguments execute_program_unsafe {size} _ _ _.

Arguments InstMov {size} _ _.
Arguments InstAdd {size} _ _.
(*Arguments InstBranchEq {size} _ _ _.*)
(*Arguments InstBranchNeq {size} _ _ _.*)
Arguments InstExit {size}.

Notation Within program cur :=
	(cur.(counter) < (length program)) (only parsing).

Notation WellFormed program :=
	(forall cur next, @step _ program cur next -> Within program next)
	(only parsing).

Notation InstWellFormed len_program := (fun index instr =>
	forall program cur next,
	len_program <= (length program)
	-> lookup (index%nat) program = Some instr
	-> cur.(counter) = (index%nat)
	-> @step _ program cur next
	-> Within program next
) (only parsing).

Notation IndexPairsWellFormed program :=
	(fun index_instr => InstWellFormed (length program) index_instr.1 index_instr.2)
	(only parsing).

Ltac program_well_formed :=
	match goal with
	| |- WellFormed ?program =>
		let program_type := type of program in
		match program_type with | list (Instruction ?size) =>
			apply index_pairs_InstWellFormed_implies_WellFormed;
			find_obligations__helper
				(IndexPairsWellFormed program)
				(@check_instruction_well_formed size (length program))
				(imap pair program)
		end
	end.


Module redundant_additions.
	Definition program: list (Instruction 1) := [
		InstMov (Literal 0) (0%fin);
		InstAdd (Literal 1) (0%fin);
		InstAdd (Literal 1) (0%fin);
		InstAdd (Literal 1) (0%fin);
		InstAdd (Literal 1) (0%fin);
		InstAdd (Literal 1) (0%fin);
		InstExit
	].
	Theorem well_formed: WellFormed program. Proof. program_well_formed. Qed.
	Theorem within: Within program (state 0 [#0]). Proof. simpl; lia. Qed.

	Example test:
		execute_program_unknown_termination
			well_formed (length program) (state 0 [#0]) within
		= Some (state 6 [#5]).
	Proof. reflexivity. Qed.
End redundant_additions.

Module redundant_doubling.
	Definition program: list (Instruction 1) := [
		InstMov (Literal 1) (0%fin);
		InstAdd (Register 0%fin) (0%fin);
		InstAdd (Register 0%fin) (0%fin);
		InstAdd (Register 0%fin) (0%fin);
		InstExit
	].
	Theorem well_formed: WellFormed program. Proof. program_well_formed. Qed.
	Theorem within: Within program (state 0 [#0]). Proof. simpl; lia. Qed.

	Example test:
		execute_program_unknown_termination
			well_formed (length program) (state 0 [#0]) within
		= Some (state 4 [#8]).
	Proof. reflexivity. Qed.
End redundant_doubling.


(*Notation val := Operand (only parsing).
Notation expr := Instruction (only parsing).

Notation of_val := InstExit (only parsing).

Definition to_val (e: expr): option val :=
	match e with
	| InstExit _ v => Some v
	| _ => None
	end.
*)
(*
	So the first program I'm interested in verifying is this one.
	I want to obviously verify it's safe and such, but also I want to be

main: (this label is implicit)
	{{ True }}
	Mov 0 $r1
	{{ $r1 = 0 }}
loop:
	{{ exists n < 10, $r1 = n }}
	Add 1 $r1
	{{ exists n <= 10, $r1 = n + 1}}
	BranchNeq $r1 10 loop
done:
	{{ $r1 = 10 }}
	Exit
*)

(*Inductive Bit: Type := B0 | B1.*)
