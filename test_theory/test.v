Declare ML Module "magmide_plugin".
Require Import String.
Open Scope string_scope.

Inductive Value :=
	| Const (n: nat)
	| Ref (r: nat)
.

Inductive Instruction :=
	| Return (v: Value)
	| Add (r: nat) (op1: Value) (op2: Value)
.

Magmide "test_code/something.mg" as four.
Check four.
Print four.

MagmideInspectExpr (true).
MagmideInspectExpr (0).
MagmideInspectExpr ("yo").
MagmideInspectExpr (cons true nil).
