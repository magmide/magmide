(*
	okay I feel like I want to have a `compile` function that takes terms and just reduces the knowns, typechecks them, and outputs a string representing the "compiled" program
	then a `run` function that reduces the knowns and typechecks the program, but then reduces all the terms and outputs the "stdout" of the program
	this is presupposing that you'll have some kind of effectful commands that append some string to the "stdout". that seems like the more natural way I would prefer to structure a language that I'll eventually be using to learn while making a real imperative language
*)

Require Import Coq.Strings.String.
Require Import theorems.Maps.

Inductive typ: Type :=
	(*| Generic*)
	| Bool
	| Nat
	| Arrow (input output: typ)
	| UnionNil
	| UnionCons (arm_name: string) (arm_type: typ) (rest: typ)
	| TupleNil
	| TupleCons (left right: typ)
	(*| KnownType (type_value: trm)*)
	(*| KnownValue (value: trm)*)
.

Inductive Arm: Type :=
  | arm (arm_name: string).

Inductive trm: Type :=
	| tru | fls
	| debug_bool
	(*| nat_const (n: nat)*)
	(*| nat_plus (left right: trm)*)
	(*| debug_nat*)
	| binding (decl_name: string) (after: trm)
	| usage (var_name: string)
	| test (conditional iftru iffls: trm)
	| fn (args_name: string) (output_type: typ) (body: trm)
	| call (target_fn args: trm)
	| union_nil
	| union_cons (arm_name: string) (arm_value: trm) (rest_type: typ)
	| union_match (tr: trm) (arms: list (string * trm))
	| tuple_nil
	| tuple_cons (left right: trm)
	| tuple_access (tup: trm) (index: nat)
.


Fixpoint tuple_lookup (n: nat) (tr: trm): option trm :=
	match tr with
	| tuple_cons t tr' => match n with
		| 0 => Some t
		| S n' => tuple_lookup n' tr'
		end
	| _ => None
	end
.

Fixpoint union_lookup (tr: trm) (arms: list (string, (string * trm))): option trm :=
	match tr with
	| union_cons tr_arm_name tr_arm_value _ => match arms with
		| (arm_name, (arm_var, arm_body)) :: arms' => if eqb_string tr_arm_name arm_name
			then Some (substitute arm_var tr_arm_value arm_body)
			else union_lookup tr arms'
		| [] => None
		end
  | _ => None
	end
.
