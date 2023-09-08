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


Inductive day: Type :=
	| monday
	| tuesday
	| wednesday
	| thursday
	| friday
	| saturday
	| sunday.

Definition next_weekday (d: day): day :=
	match d with
	| monday => tuesday
	| tuesday => wednesday
	| wednesday => thursday
	| thursday => friday
	| friday => monday
	| saturday => monday
	| sunday => monday
	end.

Compute (next_weekday friday).
(* ==> monday : day *)
Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

Definition test_next_weekday_manual: Eq (next_weekday saturday) monday :=
	EqCreate monday.
















































(* Counterexample by Thierry Coquand and Christine Paulin
	 Translated into Coq by Vilhelm Sjöberg *)

(* NotPos represents any positive, but not strictly positive, operator. *)
(*Definition NotPos (a: Type) := (a -> Prop) -> Prop.*)

(* If we were allowed to form the inductive type
		 Inductive A: Type :=
			 createA: NotPos A -> A.
	 then among other things, we would get the following. *)
Axiom A: Type.
(*Axiom createA: NotPos A -> A.*)
Axiom createA: ((A -> Prop) -> Prop) -> A.
(*Axiom matchA: A -> NotPos A.*)
Axiom matchA: A -> ((A -> Prop) -> Prop).
(*Axiom roundtrip_same: forall (a: NotPos A), matchA (createA a) = a.*)
Axiom roundtrip_same: forall (a: ((A -> Prop) -> Prop)), matchA (createA a) = a.

(* In particular, createA is an injection. *)
Lemma createA_injective: forall p p', createA p = createA p' -> p = p'.
Proof.
	intros.
	assert (matchA (createA p) = (matchA (createA p'))) as H1 by congruence.
	rewrite roundtrip_same in H1.
	rewrite roundtrip_same in H1.
	assumption.
	(*now repeat rewrite roundtrip_same in H1.*)
Qed.

(* However, ... *)

(* Proposition: For any type A, there cannot be an injection
	 from NotPos(A) to A. *)

(* For any type T, there is an injection from T to (T->Prop),
	 which is λt1.(λt2.t1=t2) . *)
Definition type_to_prop {T:Type}: T -> (T -> Prop) :=
	fun t1 t2 => t1 = t2.

Lemma type_to_prop_injective: forall T (t t': T), type_to_prop t = type_to_prop t' -> t = t'.
Proof.
	intros.
	assert (type_to_prop t t = type_to_prop t' t) as H1 by congruence.
	compute in H1.
	symmetry.
	rewrite <- H1.
	reflexivity.
Qed.

(* Hence, by composition, we get an injection prop_to_type from A->Prop to A. *)
Definition prop_to_type: (A -> Prop) -> A
	:= fun p => createA (type_to_prop p).

Lemma prop_to_type_injective: forall p p', prop_to_type p = prop_to_type p' -> p = p'.
Proof.
	unfold prop_to_type. intros.
	apply createA_injective in H. apply type_to_prop_injective in H. assumption.
Qed.

(* We are now back to the usual Cantor-Russel paradox. *)
(* We can define *)
Definition AProp: A -> Prop
	(*the user gives us some `a: A`*)
	:= fun a =>
		(*and then we ask them to prove that some prop exists which:*)
		(*- **is the same as the object `a` they just gave us** *)
		(*- doesn't hold true for `a` *)
		(*these things together ask them to give us a prop that isn't true of itself!*)
		exists (P: A -> Prop), prop_to_type P = a /\ ~P a.
		(*this shouldn't be possible!*)


Definition a0: A := prop_to_type AProp.

(* We have (AProp a0) iff ~(AProp a0) *)
Lemma bad: (AProp a0) <-> ~(AProp a0).
Proof.
split.
	*
		unfold not.
		(*in this first case we've assumed aprop, but that's a problem because aprop *carries inside itself* a proof that there's some prop that isn't true of the thing we passed in, but also a proof that the thing we passed in is the same as the prop that isn't true!*)
		(*this is the core problem of non-strict positivity, that it allows an assumption we've made, an argument to our function, to already contain a proof of its own falsity*)
		(*this is definitely a kind of recursion, but it's *constructor* recursion rather than computational recursion *)
		intros [P [H1 H2]] H.
		unfold not in H2.
		unfold a0 in H1.
		apply prop_to_type_injective in H1. rewrite H1 in H2.
		auto.
	*
		(*this second case is the more straightforward one that assumes falsity already, so we just have to show that the proof of falsity actually applies to itself*)
		intros.
		exists AProp.
		split; try assumption.
		unfold a0. reflexivity.
Qed.

(* Hence a contradiction. *)
Theorem worse: False.
	pose bad. tauto.
Qed.

Print worse.

(*to construct yes, all you have to do is construct no*)
(*and to construct no, you only have to construct a *function* that accepts (assumes) yes *)
(*and you've done this in an environment where its possible to use the contradictory theorem to prove False once you've hit that level*)

(*is that the core idea of non-strict positivity? that it allows you to create situations where in order to create a *thing* you merely have to create a function that accepts the thing? with a side trip to creating ~thing?*)


Definition worse_manual: False :=
	and_ind (fun (forward: AProp a0 -> ~AProp a0) (backward: ~AProp a0 -> AProp a0) =>
		let aprop: AProp a0 := (
			let not_aprop: ~AProp a0 := (
				fun aprop: AProp a0 =>
					let not_aprop: ~AProp a0 := forward aprop in
					let ohno: False := not_aprop aprop in
					False_ind False ohno
			): ~AProp a0 in
			backward not_aprop
		) in
		(fun aprop: AProp a0 =>
			let not_aprop: ~AProp a0 := forward aprop in
			let ohno: False := not_aprop aprop in
			False_ind False ohno
		) aprop
	) bad.

Theorem worse_full: False.
	pose bad. destruct bad as [forward backward]. clear i.
	assert (AProp a0) by (apply backward; unfold not; intros; apply forward; assumption).
	apply forward. assumption.
	assumption.
Qed.
