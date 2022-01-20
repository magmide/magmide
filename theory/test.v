Declare ML Module "magmide_plugin".

Definition definition := 5.

Intern 3.
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
