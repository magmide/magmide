Declare ML Module "magmide_plugin".

Definition definition := 5.

Inductive Instruction :=
	| InstExit
	| InstMov (src: nat) (dest: nat)
	| InstAdd (val: nat) (dest: nat)
.

MyDefine (InstMov 0 0).

(*App(
	MutConstruct((theory.test.Instruction,0),,2),
	[
		MutConstruct((Coq.Init.Datatypes.nat,0),,1);
		MutConstruct((Coq.Init.Datatypes.nat,0),,1)
	]
)*)


(*MyDefine 5.*)
(*MyDefine definition.*)
(*MyDefine Instruction.*)

(*Intern 3.
Intern definition.
Intern (fun (x : Prop) => x).
Intern (fun (x : Type) => x).
Intern (forall (T : Type), T).
Intern (fun (T : Type) (t : T) => t).
Intern _.
Intern (Type : Type).


MyDefine n := 1.
Check n.

MyDefine f := (fun (x : Type) => x).
Check f.
*)
