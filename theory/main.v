Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.

From stdpp Require Import base options fin vector.
Import ListNotations.
(*Require Import theory.utils.*)

Notation Mask := coPset.

Section Sized.
	Context {size: nat}.

	Notation register := (fin size).

	Inductive Operand: Type :=
		| Literal (n: nat)
		| Register (r: register)
	.


	(*
		It seems pretty obvious I need to break instructions into "sequential" and "terminator" versions (kinda like llvm), and then have two layers of assertions, each with their own "later" concept:
			- a layer for reasoning purely about sequential "segments" of instructions (the body of a basic block)
			- a layer for reasoning about graphs of labeled blocks. this layer is basically where we can encode some concept of recursion, and where we use the lob induction iris provides to make it possible to reason about loops and such

		we have one layer of weakest preconditions (or just preconditions like in the low level code papers?) that moves sequential statements along
		then we have a "block" structure that contains a list of sequential instructions and a single terminator instruction
		then we have an "execute block" function that takes a machine state (that doesn't include an instruction pointer for now?) and transforms it according to the sequential segment and then returns the transformed state and an optional next label, with None meaning execution is finished
	*)

	Inductive Instruction :=
		| Instruction_Exit
		| Instruction_Move (src: Operand) (dest: register)
		| Instruction_Add (val: Operand) (dest: register)

		| Instruction_Jump (to: nat)
		| Instruction_BranchEq (a: Operand) (b: Operand) (to: nat)
		| Instruction_BranchNeq (a: Operand) (b: Operand) (to: nat)

		(*| Instruction_Store (src: Operand) (dest: Operand)*)
		(*| Instruction_Load (src: Operand) (dest: register)*)
	.
	Hint Constructors Instruction: core.


	Record MachineState := machine_state {
		instruction_pointer: nat;
		(*registers: (vec nat size);*)
		registers: (gmap nat nat);
		program: list Instruction
	}.

	Notation current_instruction s :=
		(lookup s.(instruction_pointer) s.(program)) (only parsing).

	Notation incr s :=
		(S s.(instruction_pointer)) (only parsing).

	Notation get cur reg :=
		(cur.(registers) !!! reg) (only parsing).

	Notation update s dest val :=
		(vinsert dest val s.(registers)) (only parsing).

	Notation make_next cur next_instruction_pointer next_registers :=
		(machine_state next_instruction_pointer next_registers cur.(program))
		(only parsing).

	Definition eval_operand
		(cur: MachineState) (operand: Operand)
	: nat :=
		match operand with
		| Literal n => n
		| Register r => (cur.(registers) !!! r)
		end
	.

	Inductive Step: MachineState -> MachineState -> Prop :=
		| Step_Move: forall cur src dest,
			(current_instruction cur) = Some (Instruction_Move src dest)
			-> Step cur (make_next cur
				(incr cur)
				(update cur dest (eval_operand cur src))
			)
		(*$s==v ∗ $d==? ∗ <later>($s==v ∗ $d==? -∗ Q d v) <entails> wp Move $r $d {Q d v}*)

		| Step_Add: forall cur val dest,
			(current_instruction cur) = Some (Instruction_Add val dest)
			-> Step cur (make_next cur
				(incr cur)
				(update cur dest ((eval_operand cur val) + (get cur dest)))
			)

		| Step_Jump: forall cur to,
			(current_instruction cur) = Some (Instruction_Jump to)
			-> Step cur (make_next cur to cur.(registers))

		| Step_BranchEq_Yes: forall cur a b to,
			(current_instruction cur) = Some (Instruction_BranchEq a b to)
			-> a = b
			-> Step cur (make_next cur to cur.(registers))

		| Step_BranchEq_No: forall cur a b to,
			(current_instruction cur) = Some (Instruction_BranchEq a b to)
			-> ~(a = b)
			-> Step cur (make_next cur (incr cur) cur.(registers))

		| Step_BranchNeq_Yes: forall cur a b to,
			(current_instruction cur) = Some (Instruction_BranchNeq a b to)
			-> ~(a = b)
			-> Step cur (make_next cur to cur.(registers))

		| Step_BranchNeq_No: forall cur a b to,
			(current_instruction cur) = Some (Instruction_BranchNeq a b to)
			-> a = b
			-> Step cur (make_next cur (incr cur) cur.(registers))
	.
	Hint Constructors Step: core.

	(*theorems about individual instructions, such as that exit never takes a step*)

	(*use the Chain prop to think about traces*)

	(*theorem that any trace with Exit at the top never continues*)

	(*theorems lifting list operators for Trace*)

	Class magmideGS (Σ: gFunctors) := MagmideG {
		(*magmideGS_invGS :> invGS_gen HasNoLc Σ;*)
	  (*magmideGS_gen_heapG :> gen_heapGS nat nat Σ;*)
	  magmideGS_ghost_mapG :> ghost_mapGS nat nat Σ;
	}.
	Global Opaque magmide_invGS.
	Global Arguments MagmideG {Σ}.

	(*gen_heap_interp state.(heap)*)
	(*leads to*)
	(*ghost_map_auth (gen_heap_name hG) 1 state.(heap)*)
	(*leads to*)
	(*Record state : Type := {
	  heap: gmap loc (option val);
	}.*)

	Definition state_interpretation state := gen_heap_interp state.(heap) (*∗ steps_auth step_cnt*).




	Definition wp_pre
		`{!magmideGS Σ}
		(wp: Mask -d> MachineState -d> (MachineState -d> iPropO Σ) -d> iPropO Σ)
	: Mask -d> MachineState -d> (MachineState -d> iPropO Σ) -d> iPropO Σ := fun mask cur Post =>
		match current_instruction cur with
		| None => |={mask}=> Post cur
		| Some Instruction_Exit => |={mask}=> Post cur
		| Some instruction => state_interpretation cur
			-∗ |={mask,∅}=> (
				CanStep cur
				∗ (forall next, Step cur next -∗ |={∅,mask}=> ▷ (
					state_interpretation next
					∗ wp mask next Post
				))
			)
		end%I.

	Local Instance wp_pre_contractive `{!magmideGS Σ}: Contractive wp_pre.
	Proof.
		rewrite /wp_pre /= ⇒ n wp wp' Hwp E e1 Φ.
		do 25 (f_contractive || f_equiv).
		induction num_laters_per_step as [|k IH]; simpl.
		- repeat (f_contractive || f_equiv); apply Hwp.
		- by rewrite -IH.
	Qed.

	(*probably have to define our own Wp typeclass :( *)
	Class Wp :=
		wp: Mask -> MachineState -> (MachineState -> iPropO Σ) -> iPropO Σ.
	Global Arguments wp {_ _ _ _ _} _ _ _%E _%I.
	Global Instance: Params (@wp) 8 := {}.

	Local Definition wp_def `{!magmideGS Σ}: Wp := fixpoint wp_pre.
	Local Definition wp_aux: seal (@wp_def). Proof. by eexists. Qed.
	Definition wp' := wp_aux.(unseal).
	Global Arguments wp' {hlc Λ Σ _}.
	Global Existing Instance wp'.
	Local Lemma wp_unseal `{!magmideGS Σ}: wp = @wp_def hlc Λ Σ _.
	Proof. rewrite -wp_aux.(seal_eq) //. Qed.

End Sized.


(*

define the wp recursively, referring to a state interpretation (that includes a reference to Step?) and using later and update modalities to link step indexing to steps in the program

then prove a bunch of consequences of the wp, such as a wp for each individual instruction or specialized versions of operators like * and -*

then do things like prove the wp is non expansive?
	TCEq (to_val e) None ->
	Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).

that it preserves equivalences?
	Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).





then higher level concepts, such as being able to form wps for blocks of code instead of individual instructions





I want to get to the point where I can:

- verify a simple straight line program that does something like adding four numbers

- verify a program with a branch implemented loop

- add input and output signals similar to the kinds of simple signals in a chip like a 6502, and use them to verify something like a hello world program


then is it time to start figuring out and building systems for trackable effects?

*)
