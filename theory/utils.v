Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List Cpdt.CpdtTactics.
From stdpp Require Import base fin vector options.
Import ListNotations.

Ltac solve_crush := try solve [crush].
Ltac solve_assumption := try solve [assumption].
Ltac subst_injection H := injection H; intros; subst; clear H.

Notation impossible := (False_rect _ _).
Notation this item := (exist _ item _).
Notation use item := (proj1_sig item).

From Coq.Wellfounded Require Import Inclusion Inverse_Image.

Section wf_transfer.
	Variable A B: Type.
	Variable RA: A -> A -> Prop.
	Variable RB: B -> B -> Prop.
	Variable f: A -> B.

	Theorem wf_transfer:
		(forall a1 a2, (RA a1 a2) -> (RB (f a1) (f a2)))
		-> well_founded RB
		-> well_founded RA.
	Proof.
		intros H?;
		apply (wf_incl _ _ (fun a1 a2 => (RB (f a1) (f a2))) H);
		apply wf_inverse_image; assumption.
	Qed.

End wf_transfer.


Section VectorIndexAssertions.
	Context {T: Type}.
	Context {size: nat}.
	Notation IndexPair := (prod (fin size) T) (only parsing).

	Definition index_disjoint (index: fin size) :=
		fun (index_pair: IndexPair) => ((index_pair.1) <> index).

	Inductive UnionAssertion (vector: vec T size): list IndexPair -> Prop :=
		| union_nil: UnionAssertion vector []
		| union_cons: forall pairs index value,
			UnionAssertion vector pairs
			-> (vector !!! index) = value
			-> Forall (index_disjoint index) pairs
			-> UnionAssertion vector ((index, value) :: pairs)
	.

	(*Theorem UnionAssertion_no_duplicate_indices: forall vector index_pairs,
		UnionAssertion vector index_pairs
		-> NoDup (map (fun index_pair => index_pair.1) index_pairs).
	Proof. Qed.*)
	(*
		while this is fancy and everything, we almost certainly don't need it, since we really want a higher level opaque theorem stating that if two assertions point to the same location in the same vector then we can derive False
	*)

End VectorIndexAssertions.


Section convert_subset.
	Variable T: Type.
	Variable P Q: T -> Prop.
	Theorem convert_subset: {t | P t} -> (forall t: T, P t -> Q t) -> {t | Q t}.
	Proof. intros []; eauto. Qed.
End convert_subset.
Arguments convert_subset {T} {P} {Q} _ _.

Notation convert item := (convert_subset item _).

Notation Yes := (left _ _).
Notation No := (right _ _).
Notation Reduce x := (if x then Yes else No).

Theorem append_single_cons {T: Type}: forall (t: T) l, t :: l = [t] ++ l.
Proof. induction l; auto. Qed.


Inductive All: list Prop -> Prop :=
	| All_nil: All []
	| All_cons: forall (P: Prop) (l: list Prop), P -> All l -> All (P :: l)
.
Hint Constructors All: core.

Theorem All_undo_cons (P: Prop) (l: list Prop): All (P :: l) -> P.
Proof. inversion 1; auto. Qed.

Theorem All_permutation (A B: list Prop):
	Permutation A B -> All A -> All B.
Proof.
	intros Hpermutation HA; induction Hpermutation as []; try inversion HA; auto.
	inversion HA as [|??? Hl]; inversion Hl; auto.
Qed.

Global Instance Proper_Permutation_All: Proper (Permutation ==> flip impl) All.
Proof.
	intros ??[]?; eauto using All_permutation, Permutation_sym.
	inversion H as [| ??? Hl']; inversion Hl'; auto.
Qed.

Theorem All_permutation_cleaner (A B: list Prop):
	Permutation A B -> All A -> All B.
Proof. intros ?H; rewrite <-H; auto. Qed.

Theorem All_In_middle (P: Prop) (before after: list Prop):
	All (before ++ [P] ++ after) -> P.
Proof.
	intros H;
	assert (Hpermutation: Permutation (before ++ [P] ++ after) ([P] ++ (before ++ after)))
		by eauto using Permutation_app_swap_app;
	rewrite Hpermutation in H;
	assert (Hswap: ([P] ++ before ++ after) = (P :: (before ++ after))) by eauto;
	rewrite Hswap in H;
	eapply All_undo_cons; eauto.
Qed.

Theorem All_In (P: Prop) (l: list Prop):
	In P l -> All l -> P.
Proof.
	intros Hin Hall;
	apply in_split in Hin as [before [after]]; subst;
	rewrite cons_middle in Hall;
	eapply All_In_middle; eauto.
Qed.




Theorem valid_index_not_None {T} (l: list T) index:
	index < (length l) -> (lookup index l) <> None.
Proof.
	intros ??%lookup_ge_None; lia.
Qed.
Theorem valid_index_Some {T} (l: list T) index:
	index < (length l) -> exists t, (lookup index l) = Some t.
Proof.
	intros ?%(lookup_lt_is_Some_2 l index);
	unfold is_Some in *; assumption.
Qed.
(*lookup_lt_Some*)
Definition safe_lookup {T} index (l: list T):
	index < (length l) -> {t | (lookup index l) = Some t}
.
	intros ?%valid_index_not_None;
	destruct (lookup index l) eqn:Hlook; try contradiction;
	rewrite <- Hlook; apply (exist _ t Hlook).
Defined.

Theorem safe_lookup_In {T} index (l: list T) (H: index < length l):
	In (use (safe_lookup l H)) l.
Proof.
	apply elem_of_list_In; destruct (safe_lookup l H); simpl;
	apply elem_of_list_lookup; exists index; assumption.
Qed.

Theorem Forall_safe_lookup {T} (P: T -> Prop) l:
	Forall P l <-> forall index (H: index < length l), P (use (safe_lookup l H)).
Proof.
	split.
	-
		intros; destruct (safe_lookup l _); simpl;
		apply (Forall_lookup_1 P l index); assumption.
	-
		intros ?Hfunc; apply Forall_lookup; intros index item Hlookup;
		specialize (lookup_lt_Some l index item Hlookup) as Hindex;
		specialize (Hfunc index Hindex);
		destruct (safe_lookup l _) as [item' Hitem'] in Hfunc; simpl in Hfunc;
		rewrite Hlookup in Hitem'; subst_injection Hitem'; assumption.
Qed.

Definition closer_to target: nat -> nat -> Prop :=
	fun next cur => (target - next) < (target - cur).
(*Hint Unfold closer_to: core.*)

Theorem closer_to_well_founded target: well_founded (closer_to target).
Proof.
	apply (well_founded_lt_compat nat (fun a => target - a)); intros; assumption.
Defined.

Theorem closer_to_reverse: forall target cur next,
	(target - next) < (target - cur) -> cur < next.
Proof. lia. Qed.

Theorem closer_to_bounded_reverse: forall target cur next,
	cur < next -> cur < target -> (target - next) < (target - cur).
Proof. lia. Qed.

Definition closer_to_end {T} (arr: list T) := closer_to (length arr).

Theorem closer_to_end_well_founded {T} (arr: list T): well_founded (closer_to_end arr).
Proof. apply closer_to_well_founded. Qed.

Theorem numeric_capped_incr_safe total begin cap index:
	total = begin + cap
	-> 0 < cap
	-> index < begin
	-> S index < total.
Proof. lia. Qed.

Theorem capped_incr_safe {T} (total begin cap: list T) index:
	total = begin ++ cap
	-> 0 < length cap
	-> index < length begin
	-> S index < length total.
Proof.
	intros Htotal Hcap Hindex;
	assert (Hlen: length total = (length begin) + (length cap))
		by solve [rewrite Htotal; apply app_length];
	apply (numeric_capped_incr_safe Hlen Hcap Hindex).
Qed.

Theorem index_pairs_lookup_forward {A B}:
	forall (items: list A) (f: nat -> A -> B) item index,
	lookup index items = Some item -> lookup index (imap f items) = Some (f index item).
Proof.
	induction items; intros ??[]?;
	try solve [apply (IHitems (compose f S)); assumption];
	naive_solver.
Qed.

Theorem index_pairs_lookup_back {A B}:
	forall (items: list A) (f: nat -> A -> B) item index,
	(forall index i1 i2, f index i1 = f index i2 -> i1 = i2)
	-> lookup index (imap f items) = Some (f index item)
	-> lookup index items = Some item.
Proof.
	induction items; intros ??[]Hf?;
	try solve [injection H; intros ?%Hf; naive_solver];
	try solve [apply (IHitems (compose f S)); eauto];
	naive_solver.
Qed.

Theorem index_pair_equality {A B} (a: A) (b1 b2: B): (a, b1) = (a, b2) -> b1 = b2.
Proof. naive_solver. Qed.

Inductive partial (P: Prop): Type :=
	| Proven: P -> partial P
	(*| Falsified: ~P -> partial P*)
	| Unknown: partial P
.
Notation proven := (Proven _).
Notation unknown := (Unknown _).
Notation provenif test := (if test then proven else unknown).

Section find_obligations.
	Context {T: Type}.
	Variable P: T -> Prop.

	Theorem forall_done_undone items done undone:
		Permutation items (done ++ undone)
		-> Forall P done -> Forall P undone
		-> Forall P items.
	Proof.
		intros Hpermutation??; assert (Happ: Forall P (done ++ undone))
			by solve [apply Forall_app_2; assumption];
		setoid_rewrite Hpermutation; assumption.
	Qed.

	Variable compute_partial: forall t: T, partial (P t).

	Definition split_by_maybe: forall items: list T, {
		pair | Permutation items (pair.1 ++ pair.2) /\ Forall P pair.1
	}.
		refine (fix split_by_maybe items :=
			match items with
			| [] => this ([], [])
			| item :: items' =>
				let (pair, H) := split_by_maybe items' in
				match (compute_partial item) with
				| Proven _ => this ((item :: pair.1), pair.2)
				| Unknown => this (pair.1, (item :: pair.2))
				end
			end
		);
		intros; split; simpl in *; try destruct H;
		try solve [setoid_rewrite H; apply Permutation_middle]; auto.
	Defined.

	Definition find_obligations_function: forall items, {
		obligations | Forall P obligations -> Forall P items
	}.
		refine (fun items =>
			let (pair, H) := split_by_maybe items in
			this pair.2
		);
		destruct H; apply (forall_done_undone H); assumption.
	Defined.

	Theorem verify__find_obligations_function:
		forall items found, found = find_obligations_function items
		-> Forall P (use found) -> Forall P items.
	Proof. intros ?[]; auto. Qed.

End find_obligations.

Ltac find_obligations__helper P compute_partial items :=
	let found := eval compute in (find_obligations_function P compute_partial items) in
	let pf := eval compute in (proj2_sig found) in
	apply pf; apply Forall_fold_right; simpl; repeat split
.

Ltac find_obligations P compute_partial items :=
	match goal with
	| |- Forall P items =>
		find_obligations__helper P compute_partial items

	| |- forall item, In item items -> P item =>
		apply Coq.Lists.List.Forall_forall;
		find_obligations__helper P compute_partial items

	| |- forall item, elem_of item items -> P item =>
		apply Forall_forall;
		find_obligations__helper P compute_partial items

	| |- forall index def, index < length items -> P (nth index items def) =>
		apply Coq.Lists.List.Forall_nth;
		find_obligations__helper P compute_partial items

	| |- forall index item, (lookup index items) = Some item -> P item =>
		apply Forall_lookup;
		find_obligations__helper P compute_partial items

	| |- forall index, index < length items -> P (items !!! index) =>
		apply Forall_lookup_total;
		find_obligations__helper P compute_partial items

	| |- forall index (H: index < length items), P (use (safe_lookup items H)) =>
		apply Forall_safe_lookup;
		find_obligations__helper P compute_partial items
	end
.

Module test__find_obligations.
	Definition P n := (n < 4 \/ n < 6).
	Definition compute_partial: forall n, partial (P n).
		refine (fun n => if (lt_dec n 4) then proven else unknown); unfold P; lia.
	Defined.

	Definition items := [0; 1; 2; 4; 3; 2; 5].
	Theorem find_obligations__Forall: Forall P items.
	Proof. find_obligations P compute_partial items; lia. Qed.
	Theorem find_obligations__forall_In: forall item, In item items -> P item.
	Proof. find_obligations P compute_partial items; lia. Qed.
	Theorem find_obligations__forall_elem_of: forall item, elem_of item items -> P item.
	Proof. find_obligations P compute_partial items; lia. Qed.
	Theorem find_obligations__forall_nth: forall index def, index < length items -> P (nth index items def).
	Proof. find_obligations P compute_partial items; lia. Qed.
	Theorem find_obligations__forall_lookup: forall index item, (lookup index items) = Some item -> P item.
	Proof. find_obligations P compute_partial items; lia. Qed.
	Theorem find_obligations__forall_lookup_total: forall index, index < length items -> P (items !!! index).
	Proof. find_obligations P compute_partial items; lia. Qed.
	Theorem find_obligations__forall_safe_lookup:
		forall index (H: index < length items), P (use (safe_lookup items H)).
	Proof. find_obligations P compute_partial items; lia. Qed.
End test__find_obligations.


(*
Inductive Result (T: Type) (E: Type): Type :=
	| Ok (value: T)
	| Err (error: E).

Arguments Ok {T} {E} _.
Arguments Err {T} {E} _.
*)
