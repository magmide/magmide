Declare ML Module "magmide.plugin".
Require Import String.
Open Scope string_scope.

Inductive Instruction :=
	| InstExit
	| InstMov (src: nat) (dest: nat)
	| InstAdd (val: nat) (dest: nat)
.

Magmide "something.mg" use yo.
Theorem yo_true: yo = true.
Proof. reflexivity. Qed.

MagmideInspectExpr (true).
MagmideInspectExpr (0).
MagmideInspectExpr ("yo").
MagmideInspectExpr (InstMov 0 1).
