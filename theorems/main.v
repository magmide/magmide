Require Import List.
Import ListNotations.

Inductive Bit: Type := B0 | B1.

(*Inductive Instruction: Type :=
	| IAdd ()
.*)

Definition mem := list nat.

Fixpoint mem_access addr mem: option nat :=
	match addr, mem with
	| O, value :: _ => Some value
	| (S addr'), _ :: mem' => mem_access addr' mem'
	| _, nil => None
	end.
