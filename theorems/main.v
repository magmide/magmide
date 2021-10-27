Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List String Cpdt.CpdtTactics Coq.Program.Wf.
From stdpp Require Import base fin vector options.
Import ListNotations.
Require Import theorems.utils.


Section Sized.
	Context {size: nat}.

	Notation register := (fin size).
	Record MachineState := machine_state {
		counter: nat;
		registers: (vec nat size);
		program_memory: list Instruction
	}.

	Inductive Operand: Type :=
		| Literal (n: nat)
		| Register (r: register)
	.

	Definition eval_operand
		(cur: MachineState) (operand: Operand)
	: nat :=
		match operand with
		| Literal n => n
		| Register r => (cur.(registers) !!! r)
		end
	.

	Inductive Instruction :=
		| InstExit
		| InstMov (src: Operand) (dest: register)
		| InstAdd (val: Operand) (dest: register)

		(*| InstJump (to: nat)*)
		(*| InstBranchEq (a: Operand) (b: Operand) (to: nat)*)
		(*| InstBranchNeq (a: Operand) (b: Operand) (to: nat)*)

		(*| InstStore (src: Operand) (dest: Operand)*)
		(*| InstLoad (src: Operand) (dest: register)*)
	.
	Hint Constructors Instruction: core.

	Notation Within cur :=
		(cur.(counter) < (length cur.(program_memory))) (only parsing).

	Notation cur_instr cur :=
		(lookup cur.(counter) cur.(program_memory)) (only parsing).

	Notation get_instr cur :=
		(@safe_lookup _ cur.(counter) cur.(program_memory) _) (only parsing).

	Notation get cur reg :=
		(cur.(registers) !!! reg) (only parsing).

	Notation update cur dest val :=
		(vinsert dest val cur.(registers)) (only parsing).

	Notation incr cur :=
		(S cur.(counter)) (only parsing).

	Inductive Step: MachineState -> MachineState -> Prop :=
		| Step_Mov: forall cur src dest,
			(cur_instr cur) = Some (InstMov src dest)
			-> Step program cur (machine_state
				(incr cur)
				(update cur dest (eval_operand cur src))
			)

		| Step_Add: forall cur val dest,
			(cur_instr cur) = Some (InstAdd val dest)
			-> Step program cur (machine_state
				(incr cur)
				(update cur dest ((eval_operand cur val) + (get cur dest)))
			)

		(*| Step_Jump: forall cur to,
			(cur_instr cur program) = Some (InstJump to)
			-> Step program cur (machine_state to cur.(registers))*)

		(*| Step_BranchEq: forall cur a b to,
			(cur_instr cur program) = Some (InstBranchEq a b to)
			-> IF (a = b)
				then Step program cur (machine_state to cur.(registers))
				else Step program cur (machine_state (incr cur) cur.(registers))*)

		(*| Step_BranchNeq: forall cur a b to,
			(cur_instr cur program) = Some (InstBranchNeq a b to)
			-> IF (a = b)
				then Step program cur (machine_state (incr cur) cur.(registers))
				else Step program cur (machine_state to cur.(registers))*)
	.
	Hint Constructors Step: core.

	Theorem Step_always_Within program cur next:
		Step program cur next -> Within program cur.
	Proof. inversion 1; eauto using lookup_lt_Some. Qed.


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
		-> ~(Step program cur next).
	Proof.
		intros Hstopping ???? HStep;
		inversion Hstopping; inversion HStep; naive_solver.
	Qed.

	Theorem not_stopping_not_stuck instr:
		~(stopping instr)
		-> forall program cur,
		(cur_instr cur program) = Some instr
		-> exists next, Step program cur next.
	Proof.
		destruct instr; try contradiction; eauto.
	Qed.

	Inductive branching: Instruction -> Prop :=
		(*| branch_BranchEq: forall a b to, branching (InstBranchEq a b to)*)
		(*| branch_BranchNeq: forall a b to, branching (InstBranchNeq a b to)*)
		(*| branch_Jump: forall to, branching (InstJump to)*)
	.
	Hint Constructors branching: core.
	Definition is_branching: forall instr, {branching instr} + {~(branching instr)}.
		refine (fun instr =>
			match instr with
				(*| InstBranchEq _ _ _ => Yes*)
				(*| InstBranchNeq _ _ _ => Yes*)
				(*| InstJump _ => Yes*)
				| _ => No
			end
		); inversion 1.
	Defined.

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
		-> Step program cur next
		-> counter next = S (counter cur).
	Proof.
		intros ????? HStep; destruct instr; inversion HStep; auto.
	Qed.

	Notation segment_sequential segment := (Forall sequential segment).


	Notation NextStep program instr cur next :=
		((cur_instr cur (program%list)) = Some instr -> Step (program%list) cur next)
		(only parsing).

	Definition execute_instruction:
		forall instr (cur: MachineState), ~stopping instr
		-> {next: MachineState | forall program, NextStep program instr cur next}
	.
		refine (fun instr cur =>
			match instr with
			| InstMov src dest => fun _ => this (machine_state
				(incr cur)
				(update cur dest (eval_operand cur src))
			)
			| InstAdd val dest => fun _ => this (machine_state
				(incr cur)
				(update cur dest ((eval_operand cur val) + (get cur dest)))
			)
			| _ => fun _ => impossible
			end
		); destruct instr; try contradiction; auto.
	Defined.

	Inductive Steps
	 (program: list Instruction)
	: list MachineState -> MachineState -> Prop :=
		| Steps_start: forall start,
			Steps program cur []

		| Steps_Step: forall start steps prev cur,
			Steps program start steps prev
			-> Step program prev cur
			-> Steps program start (steps ++ [prev]) cur
	.

	Theorem Steps_start_inversion program cur next:
		Steps program cur [] next -> Step program cur next.
	Proof.
		inversion 1; subst; trivial;
		apply app_eq_nil in H0 as [_ Hfalse]; discriminate Hfalse.
	Qed.

	Theorem Steps_connect_tail_last program first steps tail last:
		Steps program first (steps ++ [tail]) last -> Step program tail last.
	Proof.
		inversion 1; subst.
		- apply app_cons_not_nil in H0; contradiction.
		- apply app_inj_tail in H0 as []; subst; assumption.
	Qed.

	Theorem Steps_connect_first_head program first head steps last:
		Steps program first ([head] ++ steps) last -> Step program first head.
	Proof.
inversion 1; subst.


subst.


intros H; induction H.
-
admit.
-
assumption.


generalize dependent steps.
induction steps.
-
inversion 1.
subst.
apply app_singleton in H0 as [[]|[]]; subst.
+ subst_injection H2; inversion H1; subst; auto; apply Steps_start_inversion; assumption.
+ discriminate H2.

-
intros.


	Qed.



	(*Theorem Steps_append program first steps1 meet steps2 last:
		Steps program first steps1 meet
		-> Steps program meet steps2 last
		-> Steps program first (steps1 ++ [meet] ++ steps2) last.
	Proof.
		intros.
	Qed.*)

	Theorem list_split_around_meet {T} items:
		forall n (Hlength: n < length items),
		exists meet, meet = safe_lookup steps Hlength
		/\ items = (take n items) ++ [use meet] ++ (drop (S n) items).

	Theorem Steps_split program first steps last:
		Steps program first steps last
		-> forall n (Hlength: n < length steps),
		exists meet,
			meet = safe_lookup steps Hlength
			/\ Steps program first (take n steps) (use meet)
			/\ Steps program (use meet) (drop (S n) steps) last.
	Proof.
		intros.
	Qed.


	Definition execute_eternal
		(program: list Instruction)
		(well_formed: WellFormed program)
		(start: MachineState)
	: forall previous cur, Within program cur -> .
		refine (cofix execute_eternal previous cur _ _ :=
			let (instr, _) := (get_instr cur program) in
			if (is_stopping instr) then (previous ++ cur)
			else
				let (next, _) := (@execute_instruction instr cur _) in
				execute_eternal next _
		)
	Defined.

	Theorem Steps_deterministic: forall program start between1 last1 between2 last2,
		Steps program start between1 last1
		-> Steps program start between2 last2
		-> length between1 = length between2
		-> last1 = last2 /\ between1 = between2.
	Proof.
	Qed.


	Definition stateprop := MachineState -> Prop.

	(* first the partial correctness version *)
	Definition triple (block: list Instruction) (H Q: stateprop) :=
		forall prefix postfix first last between,
			H first
			-> Steps (prefix ++ block ++ postfix) first between last
			-> Q last.

	Definition triple (block: list Instruction) (H Q: stateprop) :=
		forall prefix postfix first, H first -> Within program first
			-> exists between last,
				Steps (prefix ++ block ++ postfix) first between last
				/\ Q last.

	Definition exiting_triple (block: list Instruction).




	(*
		some concept I probably need is an idea of a Steps or Trace being "within" some program segment, as in all the machine states in that trace have program counters in the segment, so I can reason about "exiting" the segment,
		also theorems about concatenation of traces, so I can do things like "the beginning of this trace is all within this segment, but this concatened head state isn't, therefore we've exited the segment"
	*)


	(*Theorem Trace_to_Step:
		forall program start steps cur,
			Trace program (steps ++ [start]) (Some cur)
			-> Steps program start steps cur.
	Proof.
	Qed.

	Theorem Steps_to_Trace:
		forall program start steps cur,
			Steps program start steps cur
			-> Trace program (steps ++ [start]) (Some cur).
	Proof.
	Qed.*)


	(*
		things to prove using Trace:
		- if a trace is currently Trace_exit, then the program is stuck
		- `execute_unsafe_eternal` is approximated by the non-eternal version, and if it returns None the program isn't well-formed and there isn't a possible next step
		- `execute_eternal` is approximated by the non-eternal version, and if it returns None there doesn't exist a possible next step
		- a well_founded relation on the program step relation implies there exists a finite number of steps such that `n = (length states), Trace states None`. also execute_program perfectly defines execute_eternal in this situation
	*)



	(*
		I think what I want is this:
		- first just *local*, as in single instruction, versions of total state assertions (hoare triples) and framed state assertions (separation logic triples)
		- somehow tie those together with Trace?
	*)

	(*Notation stateprop := (MachineState -> Prop) (only parsing).*)

	(*hoare triples assert over total state, separation triples assert over the given state and all other states*)


	(*Definition execute_eternal
		program (well_formed: WellFormed program)
	: MachineState -> Step_stream program.
		refine (cofix execute_eternal cur =>
			let (instr, _) = safe_lookup cur program in
			if (is_stopping instr) then
			else
		)
	Defined.

	CoFixpoint execute_eternal
		program (H: WellFormed program): Step_stream program
	:=
		do_Start H
	.*)


	Definition execute_program_unsafe
		(program: list Instruction)
	:
		nat -> MachineState -> option MachineState
	.
		refine (fix go Steps cur :=
			match (cur_instr cur program) with
			| None => None
			| Some instr =>
				if (is_stopping instr) then Some cur
				else match Steps with
				| 0 => None
				| S Steps' =>
					let (next, _) := (@execute_instruction instr cur _) in
					go Steps' next
				end
			end
		); assumption.
	Defined.

	Notation WellFormed program :=
		(forall cur next, Step program cur next -> Within program next)
		(only parsing).

	Notation InstWellFormed len_program := (fun index instr =>
		forall program cur next,
		len_program <= (length program)
		-> lookup (index%nat) program = Some instr
		-> cur.(counter) = (index%nat)
		-> Step program cur next
		-> Within program next
	) (only parsing).

	Theorem Step_implies_instr program cur next:
		Step program cur next -> exists instr, (cur_instr cur program) = Some instr.
	Proof. intros []; eauto. Qed.

	Notation IndexPairsWellFormed program :=
		(fun index_instr => InstWellFormed (length program) index_instr.1 index_instr.2)
		(only parsing).

	Theorem index_pairs_InstWellFormed_implies_WellFormed program:
		Forall (IndexPairsWellFormed program) (imap pair program)
		-> WellFormed program.
	Proof.
		intros H ?? HStep; rewrite Forall_lookup in H;
		specialize (Step_implies_instr HStep) as [instr];
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
		intros ???? Hsome Hcounter HStep; subst;
		try apply (stopping_stuck s Hsome) in HStep;
		destruct instr; inversion HStep; try contradiction; simpl in *; subst; lia.
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

		Variable progression: MachineState -> MachineState -> Prop.
		Variable progression_wf: well_founded progression.
		Variable progress: forall cur next, Step program cur next -> progression next cur.

		Program Fixpoint execute_program
			cur (H: Within program cur) {wf progression cur}
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

(*Arguments Literal {size} _.
Arguments Register {size} _.

Arguments execute_program_unsafe {size} _ _ _.

Arguments InstMov {size} _ _.
Arguments InstAdd {size} _ _.
Arguments InstBranchEq {size} _ _ _.
Arguments InstBranchNeq {size} _ _ _.
Arguments InstExit {size}.*)

Notation Within program cur :=
	(cur.(counter) < (length program)) (only parsing).

Notation WellFormed program :=
	(forall cur next, Step program cur next -> Within program next)
	(only parsing).

Notation InstWellFormed len_program := (fun index instr =>
	forall program cur next,
	len_program <= (length program)
	-> lookup (index%nat) program = Some instr
	-> cur.(counter) = (index%nat)
	-> Step program cur next
	-> Within program next
) (only parsing).

Notation IndexPairsWellFormed program :=
	(fun index_instr => InstWellFormed (length program) index_instr.1 index_instr.2)
	(only parsing).

Ltac program_well_formed :=
	match goal with
	| |- WellFormed ?program =>
		let program_type := type of program in
		match program_type with | list (@Instruction ?size) =>
			apply index_pairs_InstWellFormed_implies_WellFormed;
			find_obligations__helper
				(IndexPairsWellFormed program)
				(@check_instruction_well_formed size (length program))
				(imap pair program)
		end
	end.


Module redundant_additions.
	Definition program: list (@Instruction 1) := [
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
	Definition program: list (@Instruction 1) := [
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


(*
(*CoInductive Trace
	(program: list Instruction)
: list MachineState -> option MachineState -> Prop :=
	| Trace_start: forall start,
		Within program start
		-> Trace program [] (Some start)

	| Trace_step: forall prev cur next,
		Trace program prev (Some cur)
		-> Step program cur next
		-> Trace program (cur :: prev) (Some next)

	| Trace_exit: forall prev cur,
		Trace program prev (Some cur)
		-> (cur_instr cur program) = Some InstExit
		-> Trace program (cur :: prev) None
.*)
*)




Definition program_fizzbuzz := [
	(* we accept the input n in register 1 *)
	(* we then increment register 2 *)
	"begin"
		(InstMov 0 "$2")

	"main"
		(InstAdd 1 "$2")

		(* prepare for test_3 by moving our increment into register 3 *)
		(InstMov "$2" "$3")
	"test_3"
		(* TODO if the number is already less than 3, what's the semantics here? *)
		(InstSub 3 "$3")
		(* if the current remainder is greater than or equal to 3, we have to keep iterating *)
		(InstBranchLt 3 "$3" "test_3")
		(* otherwise we continue *)
		(* if the remainder isn't 0, then we skip printing "Fizz" *)
		(InstBranchNeq "$2" "$3" "after_fizz")
		(InstPrint "fizz")

	"after_fizz"
		(* prepare for test_5 by moving our increment into register 3 *)
		(InstMov "$2" "$3")
	"test_5"
		(InstSub 5 "$3")
		(* if the current remainder is greater than or equal to 5, we have to keep iterating *)
		(InstBranchLt 5 "$3" "test_5")
		(* if the remainder isn't 0, then we skip printing "Buzz" *)
		(InstBranchNeq "$2" "$3" "after_buzz")
		(InstPrint "buzz")

	"after_buzz"
		(* if our increment is less than the input, rerun the loop *)
		(InstBranchLt "$2" "$1" "main")
		(* otherwise fall through to exit *)
		(* should we actually literally exit? *)
		(InstExit)
].
