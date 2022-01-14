Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
(*Require Import List String Cpdt.CpdtTactics Coq.Program.Wf.*)
From Coq Require Import Morphisms RelationClasses Setoid.
Require Import Cpdt.CpdtTactics.
From stdpp Require Import base options fin gmap.
(*Import ListNotations.*)
Require Import theorems.utils.

(*Inductive Bit: Type := B0 | B1.*)
(*Notation BitWord word_size := (vec Bit word_size).*)

(*https://coq.inria.fr/library/Coq.Bool.Bvector.html*)
(*https://github.com/coq-community/bits*)
(*https://github.com/mit-plv/bbv*)
(*https://github.com/jasmin-lang/coqword*)
(*https://coq.inria.fr/library/Coq.PArith.BinPosDef.html*)


(*Notation MemoryBank word_size := (gmap (BitWord word_size) (BitWord word_size)).*)
(*Notation MemoryBank size := (gmap (fin size) nat).*)

(*Definition bank: RegisterBank 3 := {[ 2%fin := 1 ]}.
Example test_bank: (bank !!! 2%fin) = 1. Proof. reflexivity. Qed.
Definition empty_bank: RegisterBank 3 := empty.
Example test_empty: (empty_bank !!! 2%fin) = 0. Proof. reflexivity. Qed.*)

(*Notation RegisterBank word_size register_count := (gmap (fin register_count) (BitWord word_size)).*)
Notation RegisterBank size := (gmap (fin size) nat).


(*From stdpp Require Import natmap.
Definition test__natmap_lookup_m: natmap nat := {[ 3 := 2; 0 := 2 ]}.
Example test__natmap_lookup: test__natmap_lookup_m !! 3 = Some 2.
Proof. reflexivity. Qed.

Example test__vec_total_lookup: ([# 4; 2] !!! 0%fin) = 4.
Proof. reflexivity. Qed.*)

Module AbstractMachine.
	Parameter size: nat.

	Record MachineState := machine_state {
		program_counter: RegisterBank 1;
		registers: RegisterBank size
	}.
	(*Notation pc state := (state.(program_counter) !!! 0).*)
	Global Instance state_empty: Empty MachineState := machine_state empty empty.
	Global Instance state_union: Union MachineState := fun s1 s2 => (machine_state
		(union s1.(program_counter) s2.(program_counter))
		(union s1.(registers) s2.(registers))
	).
	Theorem state_equality c1 c2 r1 r2:
		c1 = c2 /\ r1 = r2 <-> (machine_state c1 r1) = (machine_state c2 r2).
	Proof. naive_solver. Qed.

	Definition state_disjoint s1 s2 :=
		map_disjoint s1.(program_counter) s2.(program_counter)
		/\ map_disjoint s1.(registers) s2.(registers).

	Global Instance state_disjoint_symmetric: Symmetric state_disjoint.
	Proof.
		intros ??; unfold state_disjoint;
		rewrite !map_disjoint_spec; naive_solver.
	Qed.

	Theorem state_union_commutative s1 s2:
		state_disjoint s1 s2 -> union s1 s2 = union s2 s1.
	Proof.
		intros [C R]; unfold union, state_union;
		rewrite (map_union_comm _ _ C); rewrite (map_union_comm _ _ R);
		reflexivity.
	Qed.

	Theorem state_disjoint_union_distributive s1 s2 s3:
		state_disjoint s1 (union s2 s3)
		<-> state_disjoint s1 s2 /\ state_disjoint s1 s3.
	Proof.
		split; unfold state_disjoint.
		- intros [?%map_disjoint_union_r ?%map_disjoint_union_r]; naive_solver.
		- intros [[] []]; split; apply map_disjoint_union_r_2; assumption.
	Qed.

	Theorem state_union_associative (s1 s2 s3: MachineState):
		union s1 (union s2 s3) = union (union s1 s2) s3.
	Proof.
		unfold union, state_union; simpl;
		apply state_equality; apply map_union_assoc.
	Qed.

	Theorem state_union_empty_l: forall state: MachineState, union empty state = state.
	Proof.
		unfold union, state_union; intros []; simpl; do 2 rewrite map_empty_union; reflexivity.
	Qed.
	Theorem state_union_empty_r: forall state: MachineState, union state empty = state.
	Proof.
		unfold union, state_union; intros []; simpl; do 2 rewrite map_union_empty; reflexivity.
	Qed.

	Theorem state_separate_counter_registers_disjoint: forall registers program_counter,
		state_disjoint (machine_state empty registers) (machine_state program_counter empty).
	Proof. intros; hnf; simpl; auto with map_disjoint. Qed.

	Theorem state_empty_disjoint: forall state, state_disjoint empty state.
	Proof. intros; hnf; simpl; auto with map_disjoint. Qed.

	Global Hint Extern 0 (state_disjoint _ _) => (split; assumption): core.

	Notation Assertion := (MachineState -> Prop) (only parsing).
	Declare Scope assertion_scope.
	Open Scope assertion_scope.


	Definition state_implies (H1 H2: Assertion): Prop :=
		forall state, H1 state -> H2 state.
	Notation "H1 **> H2" := (state_implies H1 H2) (at level 55).
	Definition state_equivalent (H1 H2: Assertion): Prop :=
		forall state, H1 state <-> H2 state.
	Notation "H1 <*> H2" := (state_equivalent H1 H2) (at level 60).

	Theorem state_implies_reflexive: forall H, H **> H.
	Proof. intros; hnf; trivial. Qed.
	Hint Resolve state_implies_reflexive: core.

	Theorem state_implies_transitive: forall H2 H1 H3,
		(H1 **> H2) -> (H2 **> H3) -> (H1 **> H3).
	Proof. intros ??? M1 M2 state H1state; auto. Qed.
	Hint Resolve state_implies_transitive: core.

	Theorem state_implies_antisymmetric: forall H1 H2,
		(H1 **> H2) -> (H2 **> H1) -> H1 <*> H2.
	Proof. intros ?? M1 M2; split; auto. Qed.
	Hint Resolve state_implies_antisymmetric: core.

	Theorem state_implies_transitive_r: forall H2 H1 H3,
		(H2 **> H3) -> (H1 **> H2) -> (H1 **> H3).
	Proof. intros ??? M1 M2; eapply state_implies_transitive; eauto. Qed.
	Hint Resolve state_implies_transitive_r: core.

	Theorem state_operation_commutative:
		forall (operation: Assertion -> Assertion -> Assertion),
			(forall H1 H2, operation H1 H2 **> operation H2 H1)
			-> (forall H1 H2, operation H1 H2 <*> operation H2 H1).
	Proof. intros; apply state_implies_antisymmetric; auto. Qed.

	Global Instance state_equivalent_reflexive: Reflexive state_equivalent.
	Proof. constructor; apply state_implies_reflexive. Qed.
	Global Instance state_equivalent_symmetric: Symmetric state_equivalent.
	Proof. hnf; intros ??[]; split; assumption. Qed.
	Global Instance state_equivalent_transitive: Transitive state_equivalent.
	Proof. hnf; intros ???[][]; split; eapply state_implies_transitive; eauto. Qed.
	Global Instance state_equivalence: Equivalence state_equivalent.
	Proof.
		constructor; auto using state_equivalent_reflexive, state_equivalent_symmetric,state_equivalent_transitive.
	Qed.
	Global Instance subrelation_state_equivalent_implies:
		subrelation state_equivalent state_implies.
	Proof. intros ??[]; assumption. Qed.

	Global Instance Proper_state_implies: Proper (state_equivalent ==> state_equivalent ==> flip impl) state_implies.
	Proof. intros ??[]??[]; hnf; eauto. Qed.

	Definition state_unknown: Assertion := fun state => state = empty.
	Notation "\[]" := (state_unknown) (at level 0): assertion_scope.

	Definition state_register (register: fin size) (value: nat): Assertion := fun state =>
		state = machine_state empty (singletonM register value).
	Notation "'$' register '==' value" :=
		(state_register register%fin value) (at level 32): assertion_scope.

	Definition state_counter (value: nat): Assertion := fun state =>
		state = machine_state (singletonM 0%fin value) empty.
	Notation "'pc_at' value" := (state_counter value) (at level 32): assertion_scope.

	Definition state_star (H1 H2: Assertion): Assertion :=
		fun state => exists s1 s2,
			H1 s1 /\ H2 s2
			/\ state_disjoint s1 s2
			/\ state = union s1 s2.
	Notation "H1 '\*' H2" :=
		(state_star H1 H2) (at level 41, right associativity): assertion_scope.

	Definition state_exists (A: Type) (P: A -> Assertion): Assertion :=
		fun state => exists a, P a state.
	Notation "'\exists' a1 .. an , H" :=
		(state_exists (fun a1 => .. (state_exists (fun an => H)) ..))
		(
			at level 39, a1 binder, H at level 50, right associativity,
			format "'[' '\exists' '/ ' a1 .. an , '/ ' H ']'"
		): assertion_scope.

	Definition state_forall (A: Type) (P: A -> Assertion): Assertion :=
		fun state => forall a, P a state.
	Notation "'\forall' a1 .. an , H" :=
		(state_forall (fun a1 => .. (state_forall (fun an => H)) ..))
		(
			at level 39, a1 binder, H at level 50, right associativity,
			format "'[' '\forall' '/ '  a1  ..  an , '/ '  H ']'"
		): assertion_scope.


	Definition state_pure (P: Prop): Assertion :=
		\exists (p:P), \[].
	Notation "\[ P ]" := (state_pure P)
		(at level 0, format "\[ P ]"): assertion_scope.

	Definition state_wand (H1 H2: Assertion): Assertion :=
		\exists H0, H0 \* state_pure ((H1 \* H0) **> H2).
	Notation "H1 \-* H2" := (state_wand H1 H2)
		(at level 43, right associativity): assertion_scope.


	(* ### state_unknown *)
	Theorem state_unknown_intro: \[] empty.
	Proof. hnf; trivial. Qed.

	Theorem state_unknown_inversion: forall state, \[] state -> state = empty.
	Proof. intros; hnf; auto. Qed.

	(* ### state_star *)
	Theorem state_star_intro: forall (H1 H2: Assertion) s1 s2,
		H1 s1 -> H2 s2 -> state_disjoint s1 s2
		-> (H1 \* H2) (union s1 s2).
	Proof. intros; exists s1, s2; auto. Qed.

	Theorem state_star_inversion: forall H1 H2 state,
		(H1 \* H2) state -> exists s1 s2,
			H1 s1 /\ H2 s2 /\ state_disjoint s1 s2 /\ state = union s1 s2.
	Proof. intros ??? A; hnf in A; eauto. Qed.

	Theorem state_star_commutative: forall H1 H2,
		 H1 \* H2 <*> H2 \* H1.
	Proof.
		apply state_operation_commutative; unfold state_star;
		intros ?? state (s1 & s2 & ? & ? & [] & U);
		rewrite state_union_commutative in U; trivial;
		exists s2, s1; repeat split; auto.
	Qed.

	Theorem state_star_associative H1 H2 H3:
		(H1 \* H2) \* H3 <*> H1 \* (H2 \* H3).
	Proof.
		apply state_implies_antisymmetric.
		-
			intros state (state' & h3 & (h1 & h2 & ?&?&?&?)&?& D%symmetry &?); subst state';
			exists h1, (union h2 h3);
			rewrite state_union_associative; assert (D' := D);
			apply state_disjoint_union_distributive in D' as [?%symmetry ?%symmetry];
			repeat split; repeat apply state_star_intro; trivial;
			apply state_disjoint_union_distributive; split; trivial.
		-
			intros state (h1 & state' &?&(h2 & h3 &?&?&?&?)&D&?); subst state';
			exists (union h1 h2), h3;
			rewrite <-state_union_associative; assert (D' := D);
			apply state_disjoint_union_distributive in D' as [];
			repeat split; repeat apply state_star_intro; trivial; symmetry;
			apply state_disjoint_union_distributive; split; symmetry; trivial.
	Qed.

	Theorem state_star_empty_l H:
		\[] \* H <*> H.
	Proof.
		apply state_implies_antisymmetric; hnf.
		-
			intros ? [? (? & ?%state_unknown_inversion & ? & ? & ?)]; subst;
			rewrite state_union_empty_l; assumption.
		-
			intros ?; exists empty, state; repeat split; simpl;
			try apply state_unknown_intro; try apply map_disjoint_empty_l;
			try rewrite state_union_empty_l; trivial.
	Qed.

	Theorem state_star_empty_r H:
		 H \* \[] <*> H.
	Proof. rewrite state_star_commutative; apply state_star_empty_l. Qed.

	Theorem state_star_exists A (P: A -> Assertion) H:
		(\exists a, P a) \* H <*> \exists a, (P a \* H).
	Proof.
		apply state_implies_antisymmetric; intros state.
		- intros (s1 & s2 & (a &?)&?&?&?); exists a, s1, s2; auto.
		- intros (a & (s1 & s2 &?&?&?&?)); exists s1, s2; split; auto; exists a; trivial.
	Qed.

	Theorem state_implies_frame_l H2 H1 H1':
		H1 **> H1' -> (H1 \* H2) **> (H1' \* H2).
	Proof. intros ?? (s1 & s2 & (?&?&?&?)); exists s1, s2; auto. Qed.

	Theorem state_implies_frame_r H1 H2 H2':
		H2 **> H2' -> (H1 \* H2) **> (H1 \* H2').
	Proof. intros ?? (s1 & s2 & (?&?&?&?)); exists s1, s2; auto. Qed.

	(*Theorem state_implies_frame_r' H1 H2 H2':
		H2 **> H2' -> (H1 \* H2) **> (H1 \* H2').
	Proof.
		intros ?; do 2 rewrite (state_star_commutative H1);
		apply state_implies_frame_l; assumption.
	Qed.*)

	Theorem state_implies_frame H1 H1' H2 H2':
		H1 **> H1'
		-> H2 **> H2'
		-> (H1 \* H2) **> (H1' \* H2').
	Proof. intros ??? (s1 & s2 & (?&?&?&?)); exists s1, s2; auto. Qed.

	Theorem state_implies_star_trans_l H1 H2 H3 H4:
		H1 **> H2
		-> H2 \* H3 **> H4
		-> H1 \* H3 **> H4.
	Proof. intros M1 M2 ? (s1 & s2 & (?&?&?&?)); apply M2; exists s1, s2; auto. Qed.

	Theorem state_implies_star_trans_r H1 H2 H3 H4:
		H1 **> H2 ->
		H3 \* H2 **> H4 ->
		H3 \* H1 **> H4.
	Proof. intros M1 M2 ? (s1 & s2 & (?&?&?&?)); apply M2; exists s1, s2; auto. Qed.

	(* ### state_pure *)
	Theorem state_pure_intro: forall P: Prop, P -> \[P] empty.
	Proof. intros ? P; exists P; hnf; auto. Qed.

	Theorem state_pure_inversion: forall P state, \[P] state -> P /\ state = empty.
	Proof. intros ?? A; hnf in A; naive_solver. Qed.

	Theorem state_star_pure_l P H state:
		(\[P] \* H) state <-> P /\ (H state).
	Proof.
		unfold state_pure, state_exists; split.
-


hnf.
rewrite state_star_exists.


-


		rewrite state_star_exists. rewrite* state_star_empty_l.
		iff (p&M) (p&M). { split~. } { exists~ p. }
	Qed.

	Theorem state_star_pure_r: forall P H h,
		(H \* \[P]) h = (H h /\ P).
	Proof.
		intros. rewrite hstar_comm. rewrite state_star_pure_l. apply* prop_ext.
	Qed.

	Theorem himpl_state_star_pure_r: forall P H H',
		P ->
		(H ==> H') ->
		H ==> (\[P] \* H').
	Proof. introv HP W. intros h K. rewrite* state_star_pure_l. Qed.

	Theorem state_pure_inv_hempty: forall P h,
		\[P] h ->
		P /\ \[] h.
	Proof.
		introv M. rewrite <- state_star_pure_l. rewrite~ hstar_hempty_r.
	Qed.

	Theorem state_pure_intro_hempty: forall P h,
		\[] h ->
		P ->
		\[P] h.
	Proof.
		introv M N. rewrite <- (hstar_hempty_l \[P]). rewrite~ state_star_pure_r.
	Qed.

	Theorem himpl_hempty_state_pure: forall P,
		P ->
		\[] ==> \[P].
	Proof. introv HP. intros h Hh. applys* state_pure_intro_hempty. Qed.

	Theorem himpl_state_star_pure_l: forall P H H',
		(P -> H ==> H') ->
		(\[P] \* H) ==> H'.
	Proof.
		introv W Hh. rewrite state_star_pure_l in Hh. applys* W.
	Qed.

	Theorem hempty_eq_state_pure_true :
		\[] = \[True].
	Proof.
		applys himpl_antisym; intros h M.
		{ applys* state_pure_intro_hempty. }
		{ forwards*: state_pure_inv_hempty M. }
	Qed.

	Theorem hfalse_hstar_any: forall H,
		\[False] \* H = \[False].
	Proof.
		intros. applys himpl_antisym; intros h; rewrite state_star_pure_l; intros M.
		{ false*. } { lets: state_pure_inv_hempty M. false*. }
	Qed.

	(* ### state_register *)
	Theorem state_register_intro: forall register value,
		($register == value) (machine_state empty {[ register := value ]}).
	Proof. intros; hnf; auto. Qed.

	Theorem state_register_inversion: forall register value state,
		($register == value) state
		-> state = (machine_state empty {[ register := value ]}).
	Proof. intros ??? A; hnf in A; auto. Qed.

	Theorem state_star_register_same register v1 v2:
		($register == v1) \* ($register == v2) **> \[False].
	Proof.
		hnf; intros ? (s1 & s2 & ?%state_register_inversion & ?%state_register_inversion & [] & _);
		elimtype False; subst; simpl in *;
		eapply map_disjoint_spec; trivial; apply lookup_singleton.
	Qed.

	(* ### state_counter *)
	Theorem state_counter_intro: forall counter,
		(pc_at counter) (machine_state {[ 0%fin := counter ]} empty).
	Proof. intros; hnf; auto. Qed.

	Theorem state_counter_inversion: forall counter state,
		(pc_at counter) state
		-> state = (machine_state {[ 0%fin := counter ]} empty).
	Proof. intros ?? A; hnf in A; auto. Qed.

	Theorem state_star_counter v1 v2:
		(pc_at v1) \* (pc_at v2) **> \[False].
	Proof.
		hnf; intros ? (s1 & s2 & ?%state_counter_inversion & ?%state_counter_inversion & [? _] & _);
		elimtype False; subst; simpl in *;
		eapply map_disjoint_spec; trivial; apply lookup_singleton.
	Qed.

	(* ### state_exists *)
	Theorem state_exists_intro: forall A (a: A) (P: A -> Assertion) state,
		P a state -> (\exists a, P a) state.
	Proof. intros; hnf; eauto. Qed.

	Theorem state_exists_inversion: forall X (P: X -> Assertion) state,
		(\exists x, P x) state -> exists x, P x state.
	Proof. intros ??? A; hnf in A; eauto. Qed.

	(* ### state_forall *)
	Theorem state_forall_intro: forall A (P: A -> Assertion) state,
		(forall a, P a state) -> (state_forall P) state.
	Proof. intros; hnf; assumption. Qed.

	Theorem state_forall_inversion: forall A (P: A -> Assertion) state,
		(state_forall P) state -> forall a, P a state.
	Proof. intros; hnf; trivial. Qed.

	(*Theorem state_star_forall H A (P: A -> Assertion):
		(state_forall P) \* H **> state_forall (P \* H).
	Proof.
		intros h M. destruct M as (h1&h2&M1&M2&D&U). intros x. exists~ h1 h2.
	Qed.*)

	Theorem state_implies_forall_r: forall A (P: A -> Assertion) H,
		(forall a, H **> P a) -> H **> (state_forall P).
	Proof. intros ??? M ???; apply M; assumption.  Qed.

	Theorem state_implies_forall_l: forall A a (P: A -> Assertion) H,
		(P a **> H) -> (state_forall P) **> H.
	Proof. intros ???? M ??; apply M; trivial. Qed.

	Theorem state_forall_specialize: forall A a (P: A -> Assertion),
		(state_forall P) **> (P a).
	Proof. intros; apply (state_implies_forall_l a); auto. Qed.

	(* ### state_wand *)
	Theorem state_wand_equiv: forall H0 H1 H2,
		(H0 **> H1 \-* H2) <-> (H1 \* H0 **> H2).
	Proof.
		unfold state_wand. iff M.
		{ rewrite state_star_comm. applys state_implies_state_star_trans_l (rm M).
			rewrite state_star_state_exists. applys state_implies_state_exists_l. intros H.
			rewrite (state_star_comm H). rewrite state_star_assoc.
			rewrite (state_star_comm H H1). applys~ state_implies_state_star_state_pure_l. }
		{ applys state_implies_state_exists_r H0.
			rewrite <- (state_star_hempty_r H0) at 1.
			applys state_implies_frame_r. applys state_implies_hempty_state_pure M. }
	Qed.

	Theorem state_implies_state_wand_r: forall H1 H2 H3,
		H2 \* H1 **> H3 ->
		H1 **> (H2 \-* H3).
	Proof. introv M. rewrite~ state_wand_equiv. Qed.

	Theorem state_implies_state_wand_r_inv: forall H1 H2 H3,
		H1 **> (H2 \-* H3) ->
		H2 \* H1 **> H3.
	Proof. introv M. rewrite~ <- state_wand_equiv. Qed.

	Theorem state_wand_cancel: forall H1 H2,
		H1 \* (H1 \-* H2) **> H2.
	Proof. intros. applys state_implies_state_wand_r_inv. applys state_implies_refl. Qed.

	Arguments state_wand_cancel: clear implicits.

	Theorem state_implies_hempty_state_wand_same: forall H,
		\[] **> (H \-* H).
	Proof. intros. apply state_implies_state_wand_r. rewrite~ state_star_hempty_r. Qed.

	Theorem state_wand_hempty_l: forall H,
		(\[] \-* H) = H.
	Proof.
		intros. applys state_implies_antisym.
		{ rewrite <- state_star_hempty_l at 1. applys state_wand_cancel. }
		{ rewrite state_wand_equiv. rewrite~ state_star_hempty_l. }
	Qed.

	Theorem state_wand_state_pure_l: forall P H,
		P ->
		(\[P] \-* H) = H.
	Proof.
		introv HP. applys state_implies_antisym.
		{ lets K: state_wand_cancel \[P] H. applys state_implies_trans K.
			applys* state_implies_state_star_state_pure_r. }
		{ rewrite state_wand_equiv. applys* state_implies_state_star_state_pure_l. }
	Qed.

	Theorem state_wand_curry: forall H1 H2 H3,
		(H1 \* H2) \-* H3 **> H1 \-* (H2 \-* H3).
	Proof.
		intros. apply state_implies_state_wand_r. apply state_implies_state_wand_r.
		rewrite <- state_star_assoc. rewrite (state_star_comm H1 H2).
		applys state_wand_cancel.
	Qed.

	Theorem state_wand_uncurry: forall H1 H2 H3,
		H1 \-* (H2 \-* H3) **> (H1 \* H2) \-* H3.
	Proof.
		intros. rewrite state_wand_equiv. rewrite (state_star_comm H1 H2).
		rewrite state_star_assoc. applys state_implies_state_star_trans_r.
		{ applys state_wand_cancel. } { applys state_wand_cancel. }
	Qed.

	Theorem state_wand_curry_eq: forall H1 H2 H3,
		(H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
	Proof.
		intros. applys state_implies_antisym.
		{ applys state_wand_curry. }
		{ applys state_wand_uncurry. }
	Qed.

	Theorem state_wand_inv: forall h1 h2 H1 H2,
		(H1 \-* H2) h2 ->
		H1 h1 ->
		Fmap.disjoint h1 h2 ->
		H2 (h1 \u h2).
	Proof.
		introv M2 M1 D. unfolds state_wand. lets (H0&M3): state_exists_inv M2.
		lets (h0&h3&P1&P3&D'&U): state_star_inv M3. lets (P4&E3): state_pure_inv P3.
		subst h2 h3. rewrite union_empty_r in *. applys P4. applys* state_star_intro.
	Qed.

End AbstractMachine.
