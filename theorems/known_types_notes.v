(*Require Import Coq.Strings.String.
Require Import theorems.Maps.

(*Notation memarr := (@list string).*)


Inductive typ: Type :=
	| Base: string -> typ
	| Arrow: typ -> typ -> typ
	| TupleNil: typ
	| TupleCons: typ -> typ -> typ.


Inductive trm: Type :=
	| var: string -> trm
	| call: trm -> trm -> trm
	| fn: string -> typ -> trm -> trm
	(* tuples *)
	| tuple_proj: trm -> nat -> trm
	| tuple_nil: trm
	| tuple_cons: trm -> trm -> trm.


Inductive tuple_typ: typ -> Prop :=
	| TTnil:
		tuple_typ TupleNil
	| TTcons: forall T1 T2,
		tuple_typ (TupleCons T1 T2).

Inductive well_formed_typ: typ -> Prop :=
	| wfBase: forall i,
		well_formed_typ (Base i)
	| wfArrow: forall T1 T2,
		well_formed_typ T1 ->
		well_formed_typ T2 ->
		well_formed_typ (Arrow T1 T2)
	| wfTupleNil:
		well_formed_typ TupleNil
	| wfTupleCons: forall T1 T2,
		well_formed_typ T1 ->
		well_formed_typ T2 ->
		tuple_typ T2 ->
		well_formed_typ (TupleCons T1 T2).

Hint Constructors tuple_typ well_formed_typ.

Inductive tuple_trm: trm -> Prop :=
	| tuple_tuple_nil:
		tuple_trm tuple_nil
	| tuple_trm_tuple_cons: forall t1 t2,
		tuple_trm (tuple_cons t1 t2).

Hint Constructors tuple_trm.

(*Notation "x :: l" := (cons x l)
										 (at level 60, right associativity).*)
Notation "{ }" := tuple_nil.
Notation "{ x ; .. ; y }" := (tuple_cons x .. (tuple_cons y tuple_nil) ..).


Fixpoint subst (prev: string) (next: trm) (target: trm) : trm :=
	match target with
	| var y => if eqb_string prev y then next else target
	| fn y T t1 => fn y T (if eqb_string prev y then t1 else (subst prev next t1))
	| call t1 t2 => call (subst prev next t1) (subst prev next t2)
	| tuple_proj t1 i => tuple_proj (subst prev next t1) i
	| tuple_nil => tuple_nil
	| tuple_cons t1 tup => tuple_cons (subst prev next t1) (subst prev next tup)
	end.

Notation "'[' prev ':=' next ']' target" := (subst prev next target) (at level 20).


Inductive value: trm -> Prop :=
	| v_fn: forall x T11 t12,
		value (fn x T11 t12)
	| v_tuple_nil: value tuple_nil
	| v_tuple_cons: forall v1 vtup,
		value v1 ->
		value vtup ->
		value (tuple_cons v1 vtup).

Hint Constructors value.

Fixpoint tuple_lookup (n: nat) (tr: trm): option trm :=
	match tr with
	| tuple_cons t tr' => match n with
		| 0 => Some t
		| S n' => tuple_lookup n' tr'
		end
	| _ => None
	end.


Open Scope string_scope.

Notation a := (var "a").
Notation b := (var "b").
Notation c := (var "c").
Notation d := (var "d").
Notation e := (var "e").
Notation f := (var "f").
Notation g := (var "g").
Notation l := (var "l").
Notation A := (Base "A").
Notation B := (Base "B").
Notation k := (var "k").
Notation i1 := (var "i1").
Notation i2 := (var "i2").


Example test_tuple_lookup_nil_0:
	(tuple_lookup 0 {}) = None.
Proof. reflexivity. Qed.

Example test_tuple_lookup_nil_1:
	(tuple_lookup 1 {}) = None.
Proof. reflexivity. Qed.

Example test_tuple_lookup_cons_valid_0_a:
	(tuple_lookup 0 { a }) = Some a.
Proof. reflexivity. Qed.

Example test_tuple_lookup_cons_valid_0_a_b:
	(tuple_lookup 0 { a; b }) = Some a.
Proof. reflexivity. Qed.

Example test_tuple_lookup_cons_invalid:
	(tuple_lookup 3 { a; b; c }) = None.
Proof. reflexivity. Qed.
*)
