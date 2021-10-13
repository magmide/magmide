Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
(*Require Import List String Cpdt.CpdtTactics Coq.Program.Wf.*)
Require Import Cpdt.CpdtTactics.
From stdpp Require Import base options fin gmap.
(*Import ListNotations.*)
Require Import theorems.utils.

(*Inductive Bit: Type := B0 | B1.*)
(*Notation BitWord word_size := (vec Bit word_size).*)

(*Notation MemoryBank word_size := (gmap (BitWord word_size) (BitWord word_size)).*)
(*Notation MemoryBank size := (gmap (fin size) nat).*)

(*Definition bank: RegisterBank 3 := {[ 2%fin := 1 ]}.
Example test_bank: (bank !!! 2%fin) = 1. Proof. reflexivity. Qed.
Definition empty_bank: RegisterBank 3 := empty.
Example test_empty: (empty_bank !!! 2%fin) = 0. Proof. reflexivity. Qed.*)

(*Notation RegisterBank word_size register_count := (gmap (fin register_count) (BitWord word_size)).*)
Notation RegisterBank size := (gmap (fin size) nat).

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
		c1 = c2 -> r1 = r2 -> (machine_state c1 r1) = (machine_state c2 r2).
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
	Notation "H1 <*> H2" := (state_implies H1 H2 /\ state_implies H2 H1) (at level 60).

	Theorem state_implies_reflexive: forall H, H **> H.
	Proof. intros; hnf; trivial. Qed.

	Theorem state_implies_transitive: forall H2 H1 H3,
		(H1 **> H2) -> (H2 **> H3) -> (H1 **> H3).
	Proof. intros ??? M1 M2 state H1state; auto. Qed.

	Theorem state_implies_antisymmetric: forall H1 H2,
		(H1 **> H2) -> (H2 **> H1) -> H1 <*> H2.
	Proof. intros ?? M1 M2; split; auto. Qed.

	Theorem state_implies_transitive_r: forall H2 H1 H3,
		(H2 **> H3) -> (H1 **> H2) -> (H1 **> H3).
	Proof. intros ??? M1 M2; eapply state_implies_transitive; eauto. Qed.

	Theorem state_operation_commutative:
		forall (operation: Assertion -> Assertion -> Assertion),
			(forall H1 H2, operation H1 H2 **> operation H2 H1)
			-> (forall H1 H2, operation H1 H2 <*> operation H2 H1).
	Proof. intros; apply state_implies_antisymmetric; auto. Qed.


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

	Definition state_exists (X: Type) (P: X -> Assertion): Assertion :=
		fun state => exists x, P x state.
	Notation "'\exists' x1 .. xn , H" :=
		(state_exists (fun x1 => .. (state_exists (fun xn => H)) ..))
		(
			at level 39, x1 binder, H at level 50, right associativity,
			format "'[' '\exists' '/ ' x1 .. xn , '/ ' H ']'"
		): assertion_scope.

	Definition state_forall (X: Type) (P: X -> Assertion): Assertion :=
		fun state => forall x, P x state.
	Notation "'\forall' x1 .. xn , H" :=
		(state_forall (fun x1 => .. (state_forall (fun xn => H)) ..))
		(
			at level 39, x1 binder, H at level 50, right associativity,
			format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'"
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

	(* ### state_pure *)
	Theorem state_pure_intro: forall P: Prop, P -> \[P] empty.
	Proof. intros ? P; exists P; hnf; auto. Qed.

	Theorem state_pure_inversion: forall P state, \[P] state -> P /\ state = empty.
	Proof. intros ?? A; hnf in A; naive_solver. Qed.

	(* ### state_register *)
	Theorem state_register_intro: forall register value,
		($register == value) (machine_state empty {[ register := value ]}).
	Proof. intros; hnf; auto. Qed.

	Theorem state_register_inversion: forall register value state,
		($register == value) state
		-> state = (machine_state empty {[ register := value ]}).
	Proof. intros ??? A; hnf in A; auto. Qed.

	(* ### state_counter *)
	Theorem state_counter_intro: forall counter,
		(pc_at counter) (machine_state {[ 0%fin := counter ]} empty).
	Proof. intros; hnf; auto. Qed.

	Theorem state_counter_inversion: forall counter state,
		(pc_at counter) state
		-> state = (machine_state {[ 0%fin := counter ]} empty).
	Proof. intros ?? A; hnf in A; auto. Qed.

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

	(*Global Hint Extern 0 (state_union _ _) => (split; assumption): core.*)
	Hint Rewrite state_union_associative: core.

	Theorem state_star_associative: forall H1 H2 H3,
		(H1 \* H2) \* H3 <*> H1 \* (H2 \* H3).
	Proof.
intros ???; apply state_implies_antisymmetric.
-
intros state (state' & h3 & (h1 & h2 & ?&?&?&?)&?& D%symmetry &?); subst state';
exists h1, (union h2 h3);
rewrite state_union_associative;
assert (D' := D);
apply state_disjoint_union_distributive in D' as [?%symmetry ?%symmetry];
repeat split; repeat apply state_star_intro; trivial;
apply state_disjoint_union_distributive; split; trivial.
-
intros state (h1 & state' &?&(h2 & h3 &?&?&?&?)&D&?); subst state';
exists (union h1 h2), h3;
rewrite <-state_union_associative;
assert (D' := D);
apply state_disjoint_union_distributive in D' as [];
repeat split; repeat apply state_star_intro; trivial; symmetry;
apply state_disjoint_union_distributive; split; symmetry; trivial.
	Qed.

	Theorem state_star_empty_l: forall H,
		\[] \* H <*> H.
	Proof.
	Qed.

	(* ### state_exists *)
	Theorem state_exists_intro: forall A (a: A) (P: A -> Assertion) state,
		P a state -> (\exists a, P a) state.
	Proof. intros; hnf; eauto. Qed.

	Theorem state_exists_inversion: forall X (P: X -> Assertion) state,
		(\exists x, P x) state -> exists x, P x state.
	Proof. intros ??? A; hnf in A; eauto. Qed.

	(* ### state_forall *)








	Theorem state_star_exists: forall X (P: X -> Assertion) H,
		(\exists x, P x) \* H <*> \exists x, (P x \* H).

	Theorem state_implies_frame_l: forall H2 H1 H1',
		H1 **> H1' -> (H1 \* H2) **> (H1' \* H2).

End AbstractMachine.
