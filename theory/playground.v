Inductive Trivial: Prop :=
	| TrivialCreate.

Definition Trivial_manual: Trivial := TrivialCreate.

Definition Trivial_inductive_manual (P: Prop) (p: P) (evidence: Trivial): P :=
	match evidence with
	| TrivialCreate => p
	end.


Inductive Eq {T: Type}: T -> T -> Prop :=
	| EqCreate: forall t, Eq t t.

Definition Eq_inductive_manual
	(T: Type) (P: T -> T -> Prop)
	(f: forall t: T, P t t) (l r: T)
	(evidence: Eq l r)
: P l r :=
	match evidence in (Eq l r) return (P l r) with
	| EqCreate t => f t
	end.


Inductive And (P Q: Prop): Prop :=
	| AndCreate (Ph: P) (Pq: Q): And P Q.

Definition And_inductive_manual
	(P Q R: Prop) (f: P -> Q -> R) (evidence: And P Q)
: R :=
	match evidence with
	| AndCreate _ _ p q => f p q
	end.


Definition And_left_manual (P Q: Prop) (evidence: And P Q): P :=
	match evidence with
	| AndCreate _ _ p q => p
	end.

Definition And_right_manual (P Q: Prop) (evidence: And P Q): Q :=
	match evidence with
	| AndCreate _ _ p q => q
	end.

Inductive Or (P Q: Prop): Prop :=
	| OrLeft: P -> Or P Q
	| OrRight: Q -> Or P Q.

Definition Or_inductive_manual
(P Q R: Prop) (f_left: P -> R) (f_right: Q -> R) (evidence: Or P Q)
: R :=
	match evidence with
	| OrLeft _ _ l => f_left l
	| OrRight _ _ r => f_right r
	end.


Inductive Bool: Type :=
	| BoolTrue
	| BoolFalse.

Definition Bool_inductive_manual
	(P: Bool -> Prop) (P_BoolTrue: P BoolTrue) (P_BoolFalse: P BoolFalse)
: forall (b: Bool), P b :=
	fun b =>
		match b with
		| BoolTrue => P_BoolTrue
		| BoolFalse => P_BoolFalse
		end.

Definition Eq_manual: Eq BoolTrue BoolTrue := EqCreate BoolTrue.

Fail Definition Eq_manual_bad: Eq BoolTrue BoolFalse := EqCreate BoolTrue.
Fail Definition Eq_manual_bad: Eq BoolTrue BoolFalse := EqCreate BoolFalse.
Fail Definition Eq_manual_bad: Eq BoolFalse BoolTrue := EqCreate BoolTrue.
Fail Definition Eq_manual_bad: Eq BoolFalse BoolTrue := EqCreate BoolFalse.

Inductive Impossible: Prop := .

Definition BoolTrue_not_BoolFalse_manual: (Eq BoolTrue BoolFalse) -> Impossible :=
	fun wrong_eq =>
		match wrong_eq with
		| EqCreate t => match t with
			| BoolTrue => TrivialCreate
			| BoolFalse => TrivialCreate
			end
		end.

Definition Not (P: Prop) := P -> Impossible.

Definition not_impossible_manual: Not Impossible :=
	fun impossible => match impossible with end.

Definition ex_falso_quodlibet: forall (P: Prop), Impossible -> P :=
	fun (P: Prop) (impossible: Impossible) => match impossible return P with end.

Definition BoolTrue_not_BoolFalse_manual_full: Not (Eq BoolTrue BoolFalse) :=
	fun wrong_eq =>
		match wrong_eq in (Eq l r)
		return
			match l, r with
			| BoolTrue, BoolTrue => Trivial
			| BoolFalse, BoolFalse => Trivial
			| _, _ => Impossible
			end
		with
		| EqCreate t => match t with
			| BoolTrue => TrivialCreate
			| BoolFalse => TrivialCreate
			end
		end.

Print BoolTrue_not_BoolFalse_manual_full.
