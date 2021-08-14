Add LoadPath "/home/blaine/personal/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List String Cpdt.CpdtTactics.
From stdpp Require Import base fin vector options.
Import ListNotations.

Ltac solve_crush := try solve [crush].
Ltac solve_assumption := try solve [assumption].
Ltac subst_injection H := injection H; intros; subst; clear H.

Notation "'impossible'" := (False_rec _ _).
Notation "'here' item" := (exist _ item _) (at level 10, item at next level).

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

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

Theorem numeric_capped_incr_safe total begin cap index:
	total = begin + cap
	-> 0 < cap
	-> index < begin
	-> S index < total.
Proof. lia. Qed.

Theorem capped_incr_safe {T} (total begin cap: list T) index:
	total = begin ++ cap
	-> 0 < length cap
	-> index < length begin
	-> S index < length total.
Proof.
	intros Htotal Hcap Hindex;
	assert (Hlen: length total = (length begin) + (length cap))
		by solve [rewrite Htotal; apply app_length];
	apply (numeric_capped_incr_safe Hlen Hcap Hindex).
Qed.

(*
app_length: ∀ (A: Type) (l l': list A), length (l ++ l') = length l + length l'
last_length: ∀ (A: Type) (l: list A) (a: A), length (l ++ [a]) = S (length l)
*)

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
	Notation "'Within' program cur" :=
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

	Theorem step_always_Within program cur next:
		@step program cur next
		-> Within program cur.
	Proof.
		inversion 1;
		match goal with
		| [ H: _ !! counter _ = Some _ |- _ ] =>
			apply lookup_lt_Some in H; assumption
		end.
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

	Definition execute_instruction: forall instr (cur: MachineState), ~stopping instr -> MachineState.
		refine (fun instr cur =>
			match instr with
			| InstMov src dest => fun _ => (state
				(incr cur)
				(update cur dest (eval cur src))
			)
			| InstAdd val dest => fun _ => (state
				(incr cur)
				(update cur dest ((eval cur val) + (get cur dest)))
			)
			| _ => fun _ => impossible
			end
		); contradiction.
	Defined.

	Theorem execute_instruction_implements_step program instr cur (H: ~(stopping instr)):
		(cur_instr cur program) = Some instr
		-> @step program cur (@execute_instruction instr cur H).
	Proof.
		destruct instr; try contradiction; crush.
	Qed.
	Hint Resolve execute_instruction_implements_step: core.

	(*
	Fix:
		forall (A: Type) (R: A -> A -> Prop),
		well_founded R
		->
			forall P: A -> Type,
			(forall x: A, (forall y: A, R y x -> P y) -> P x) ->
			forall x: A, P x
	*)

	Definition program_step_alignment program (progress: MachineState -> MachineState -> Prop) :=
		forall cur next, @step program cur next -> progress next cur.

	Theorem program_safe_always_Some:
		forall program initial,
			Within program initial
			-> (forall cur next, @step program cur next -> Within program next)
			-> forall cur,
					cur = (execute_instruction instr cur H)
					-> cur_instr cur program <> None.
	Proof.
intros ????[bad].
unfold not.


	Qed.

	Inductive step_trace program: forall cur next, (list @step program cur next) -> Prop :=
		| trace_Exit: forall cur next,
			@step program cur next
			-> (cur_instr next program) = Some InstExit
			-> trace program cur next [@step program cur next]
		| trace_Step
	.


	Definition execute_program:
		forall
			(program: list Instruction) (initial: MachineState)
			(safe: Within program initial)
			(program_safe: forall cur next, @step program cur next -> Within program next)
			(progress: MachineState -> MachineState -> Prop)
			(progress_wf: well_founded progress)
			(program_progress: program_step_alignment program progress),
		MachineState
	.
		refine (fun program initial safe program_safe progress progress_wf program_progress => (
			Fix progress_wf (fun _ => MachineState) (
				fun cur (execute_program: forall next, (progress next cur) -> MachineState) =>
					match (cur_instr cur program) with
					| None => impossible
					| Some instr =>
						if (is_stopping instr) then cur
						else (execute_program (@execute_instruction instr cur _) _)
					end
		)) initial).
(*rename l0 into v;*)
(*rename l into safe;*)

-
apply p.
admit.
-


apply execute_instruction_implements_step.

destruct instr; try contradiction; constructor.
+
apply

crush.

apply (not_stopping_not_stuck n) in n.



	Defined.

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


	(*
	Inductive Acc (R: A -> A -> Prop) x: Prop :=
		Acc_intro: (forall y, R y x -> Acc R y) -> Acc R x
	*)

	(*
	The really important thing is the sequential list of instructions can have anything appended to it, but as long as it's something non empty the sequential block is safe to execute
	It's probably a good idea to create a prop as the opposite of branching for all the instructions that have a step but don't merely increment the counter

	basically I want to rethink this concept of sequential to be more in line with a basic block
	essentially that the purely sequential *portion* of a basic block is both safe and the step relation is well founded
	more work is required later in order to prove what happens *after* the sequential segment

	so I'm going to create a sequential prop that cateogorizes *instructions*, and then a "basic block" definitional prop that just says an entire list of instructions are sequential

	later we can add constructors to the sequential prop that apply to conditional branches, but only given that their branch condition is false
	*)

	Inductive sequential: list Instruction -> Prop :=
		| sequential_End: forall instr,
			stopping instr
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
		-> Within program next.
	Proof.

		Qed.

	Theorem sequential_step_well_founded program:
		sequential program
		-> program_well_founded program.
	Proof.
	Qed.


	Theorem existent_not_stuck: forall program cur bank instr,
		(cur_instr cur program) = Some instr
		->
			stopping instr
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
			stopping instr
			\/ exists next bank', @step program cur bank next bank'.
	Proof. intros ??? [] ?; eauto. Qed.

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
