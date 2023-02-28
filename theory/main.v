Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.

From stdpp Require Import base options fin vector.
Import ListNotations.
Require Import theory.utils.

Section Sized.
	Context {size: nat}.

	Notation register := (fin size).

	Inductive Operand: Type :=
		| Literal (n: nat)
		| Register (r: register)
	.

	Inductive Instruction :=
		| Instruction_Exit
		| Instruction_Move (src: Operand) (dest: register)
		| Instruction_Add (val: Operand) (dest: register)

		(*| Instruction_Jump (to: nat)*)
		(*| Instruction_BranchEq (a: Operand) (b: Operand) (to: nat)*)
		(*| Instruction_BranchNeq (a: Operand) (b: Operand) (to: nat)*)

		(*| Instruction_Store (src: Operand) (dest: Operand)*)
		(*| Instruction_Load (src: Operand) (dest: register)*)
	.
	Hint Constructors Instruction: core.


	Record MachineState := machine_state {
		instruction_pointer: nat;
		registers: (vec nat size);
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

		| Step_Add: forall cur val dest,
			(current_instruction cur) = Some (Instruction_Add val dest)
			-> Step cur (make_next cur
				(incr cur)
				(update cur dest ((eval_operand cur val) + (get cur dest)))
			)

		(*| Step_Jump: forall cur to,
			(current_instruction cur) = Some (InstJump to)
			-> Step cur (machine_state to cur.(registers))*)

		(*| Step_BranchEq: forall cur a b to,
			(current_instruction cur) = Some (InstBranchEq a b to)
			-> IF (a = b)
				then Step cur (machine_state to cur.(registers))
				else Step cur (machine_state (incr cur) cur.(registers))*)

		(*| Step_BranchNeq: forall cur a b to,
			(current_instruction cur) = Some (InstBranchNeq a b to)
			-> IF (a = b)
				then Step cur (machine_state (incr cur) cur.(registers))
				else Step cur (machine_state to cur.(registers))*)
	.
	Hint Constructors Step: core.

	(*theorem that exit never takes a step*)

	Inductive Trace: list MachineState -> Prop :=
		| Trace_start: forall start,
			Trace [start]

		| Trace_step: forall past cur next,
			Trace (cur :: past)
			-> Step cur next
			-> Trace (next :: (cur :: past))
	.
	Hint Constructors Trace: core.

	(*theorem that any trace with Exit at the top never continues*)

	(*theorems lifting list operators for Trace*)

End Sized.
