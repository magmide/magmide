(*
	it seems possible to define a function that given an AST representing an inductive type is able to produce a pair of functions that can serialize/deserialize values of that inductive type to/from binary arrays

	the cases that are especially interesting are:
	- any flat union (which should just be a single tag representing which variant the value is)
	- any type with exactly one unit variant and exactly one variant with only one recursive argument (which should basically have a tag/number at the beginning representing how many wrapped recursive constructors there are, and the rest of the array is any non-recursive wrapped data values) (the cases I have in mind here are natural numbers and lists)
*)

Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List String Cpdt.CpdtTactics.
Import ListNotations.
From stdpp Require Import base options stringmap.

(*Definition yo: stringmap nat := {[ "hey" := 1; "dude" := 2 ]}.
Example test_yo: (yo !!! "hey") = 1. Proof. reflexivity. Qed.
Example test_yo': (yo !! "hey") = Some 1. Proof. reflexivity. Qed.
Example test_yo'': (yo !!! "nope") = 0. Proof. reflexivity. Qed.*)

Inductive bit: Type := b0 | b1.
Notation bit_array := (list bit).

Inductive TypeReference: Type := self_ref | other_ref (name: string).

Inductive ConstructorNode := constructor_node { constructor_args: list TypeReference }.

(* TODO polymorphic args *)
Inductive InductiveType := inductive_node { constructors: stringmap ConstructorNode }.

Inductive InductiveValue := inductive_value {
	value_type: string;
	value_constructor: string;
	value_args: list InductiveValue
}.

Notation InductiveContext := (stringmap InductiveType).


(* do we have to modify/reduce ctx as we go down? *)
Fixpoint
ValueOfType
	(ctx: InductiveContext) (value: InductiveValue) (type: InductiveType)
	{struct value}
: Prop :=
	ctx !! value.(value_type) = Some type
	/\ exists constructor, type.(constructors) !! value.(value_constructor) = Some constructor
	/\ ValuesOfTypes ctx value.(value_args) constructor.(constructor_args)
with
ValuesOfTypes
	(ctx: InductiveContext) (values: list InductiveValue) (type_refs: list TypeReference)
	{struct values}
: Prop :=
	match values, type_refs with
	| [], [] => True
	| value :: values', type_ref :: type_refs' =>
		let remainder_well_typed := (ValuesOfTypes ctx values' type_refs') in
		match type_ref with
		| self_ref => remainder_well_typed
		| other_ref other_name =>
			exists other_type, ctx !! other_name = Some other_type /\ ValueOfType ctx value other_type
			/\ remainder_well_typed
		end
	| _, _ => False
	end
.



Inductive Result (T: Type) (E: Type): Type :=
	| Ok (value: T)
	| Err (error: E).

Arguments Ok {T} {E} _.
Arguments Err {T} {E} _.

Notation serializer T := (T -> bit_array).
Notation deserializer T := (bit_array -> Result T string).

Fixpoint produce_serde_functions
	(node: InductiveType)
: Result (serializer, deserializer) string :=
	.
