Inductive MyEq {T: Type}: T -> T -> Prop :=
	| EqSelf: forall t, MyEq t t.

Definition MyEq_inductive_manual
	(T: Type) (P: T -> T -> Prop)
	(f: forall t: T, P t t) (l r: T)
	(m: MyEq l r)
: P l r :=
	match m in (MyEq l r) return (P l r) with
	| EqSelf t => f t
	end.


Inductive MyAnd (P Q: Prop): Prop :=
	| my_and (Ph: P) (Pq: Q): MyAnd P Q.

Check my_and.

Print and.
Print MyAnd.

Definition MyAnd_inductive_manual
	(P Q R: Prop) (f: P -> Q -> R) (evidence: MyAnd P Q)
: R :=
	match evidence with
	| my_and _ _ p q => f p q
	end.


Definition MyAnd_left_manual (P Q: Prop) (evidence: MyAnd P Q): P :=
	match evidence with
	| my_and _ _ p q => p
	end.

Definition MyAnd_right_manual (P Q: Prop) (evidence: MyAnd P Q): P :=
	match evidence with
	| my_and _ _ p q => q
	end.

Inductive MyOr (P Q: Prop): Prop :=
	| my_or_left: P -> MyOr P Q
	| my_or_right: Q -> MyOr P Q.

Definition MyOr_inductive_manual
(P Q R: Prop) (f_left: P -> R) (f_right: Q -> R) (evidence: MyOr P Q)
: R :=
	match evidence with
	| my_or_left _ _ l => f_left l
	| my_or_right _ _ r => f_right r
	end.


Inductive MyBool: Type :=
	| my_true
	| my_false.

Definition MyBool_inductive_manual
	(P: MyBool -> Prop) (P_my_true: P my_true) (P_my_false: P my_false)
: forall (b: MyBool), P b :=
	fun b =>
		match b with
		| my_true => P_my_true
		| my_false => P_my_false
		end.

Definition my_eq_manual: MyEq my_true my_true := EqSelf my_true.

Fail Definition my_eq_manual_bad: MyEq my_true my_false := EqSelf my_true.
Fail Definition my_eq_manual_bad: MyEq my_true my_false := EqSelf my_false.
Fail Definition my_eq_manual_bad: MyEq my_false my_true := EqSelf my_true.
Fail Definition my_eq_manual_bad: MyEq my_false my_true := EqSelf my_false.

Inductive MyFalse: Prop := .

Definition my_true_not_false_manual: (MyEq my_true my_false) -> MyFalse :=
	fun wrong_eq => match wrong_eq with
	| EqSelf t =>
	end

Definition MyNot (P: Prop) := P -> MyFalse.

Definition my_not_false_manual: MyNot MyFalse :=
	fun my_false => match my_false with end.

Definition my_ex_falso_quodlibet: forall (P: Prop), MyFalse -> P :=
	fun (P: Prop) (my_false: MyFalse) => match my_false return P with end.

Definition my_true_not_false_manual: MyNot (MyEq my_true my_false) :=
	fun wrong_eq =>
		match wrong_eq in (MyEq l r)
		return
			match l with
			| my_true =>
				match r with
				| my_true => True
				| my_false => MyFalse
				end
			| my_false => True
			end
		with
		| EqSelf t => match t as t with
			| my_true => I
			| my_false => I
			end
		end.

Print my_true_not_false_manual.
