Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List.
Import ListNotations.
From stdpp Require Import base options list tactics.

(* All just collects unordered independent assertions. *)
Section All.
	Inductive All: list Prop -> Prop :=
		| All_empty: All []
		| All_push: forall (P: Prop) (l: list Prop), P -> All l -> All (P :: l)
	.
	Hint Constructors All: core.

	Theorem All_pop (P: Prop) (l: list Prop): All (P :: l) -> P.
	Proof. inversion 1; auto. Qed.

	Theorem All_And (P: Prop) (l: list Prop):
		P /\ All l <-> All (P :: l).
	Proof.
		split.
		- intros [??]; auto.
		- inversion 1; auto.
	Qed.

	Theorem All_flatten_head (A B: Prop) (l: list Prop):
		All ((A /\ B) :: l) <-> All (A :: B :: l).
	Proof.
		split.
		- inversion 1; naive_solver.
		- inversion 1 as [|??? H']; inversion H'; auto.
	Qed.

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
		eapply All_pop; eauto.
	Qed.

	Theorem All_In (P: Prop) (l: list Prop):
		In P l -> All l -> P.
	Proof.
		intros Hin Hall;
		apply in_split in Hin as [before [after]]; subst;
		rewrite cons_middle in Hall;
		eapply All_In_middle; eauto.
	Qed.
End All.
#[export] Hint Constructors All: core.

(* Compatible links assertions that must have some notion of compatibility between all items. *)
Section Compatible.
	Context {T: Type}.
	Hypothesis ItemsCompatible: T -> T -> Prop.
	Hypothesis ItemsCompatible_symmetric: forall t1 t2,
		ItemsCompatible t1 t2 -> ItemsCompatible t2 t1.

	Inductive Compatible: list T -> Prop :=
		| Compatible_empty: Compatible []
		| Compatible_push: forall t l,
			Forall (ItemsCompatible t) l ->
			Compatible (t :: l)
	.
	Hint Constructors Compatible: core.

	Theorem Compatible_symmetric t1 t2: Compatible [t1; t2] -> Compatible [t2; t1].
	Proof using ItemsCompatible_symmetric.
		intros H; inversion H as [| ?? HF];
		inversion HF; eauto.
	Qed.

	(*Theorem Compatible_swap t1 t2 l:
		Compatible (t1 :: t2 :: l) -> Compatible (t2 :: t1 :: l).
	Proof.
intros H.
inversion H as [| ???].
subst.

-
subst.
constructor.
	Qed.

	Global Instance Proper_Permutation_Compatible: Proper (Permutation ==> flip impl) Compatible.
	Proof.
intros ??[]?; try auto.
-
inversion H0; subst; simpl.
induction H as []; try auto; subst; simpl.





		intros ??[]?; eauto using All_permutation, Permutation_sym.
		inversion H as [| ??? Hl']; inversion Hl'; auto.
	Qed.

	Theorem Compatible_Permutation l1 l2: Permutation l1 l2 -> Compatible l1 -> Compatible l2.
	Proof.
intros HP HC.
induction HC as [|? ? ? ?].
- apply Permutation_nil in HP; naive_solver.
-
inversion H.
+ subst. apply Permutation_singleton_l in HP. naive_solver.
+
subst.

rewrite <-HP.

induction HP as []; try inversion HC; auto.


intros Hpermutation HA; induction Hpermutation as []; try inversion HA; auto.
inversion HA as [|??? Hl]; inversion Hl; auto.
	Qed.*)

End Compatible.
#[export] Hint Constructors Compatible: core.


Section test_Compatible_neq.
	Theorem Compatible_neq (a b c: nat):
		a <> b -> b <> c -> a <> c -> Compatible (fun a b => a <> b) [a; b; c].
	Proof. auto. Qed.
End test_Compatible_neq.



(* Chain links assertions in a strict order, where each assertion is implied by the previous. *)
Section Chain.
	Context {T: Type}.
	Hypothesis Link: T -> T -> Prop.

	Inductive Chain: list T -> Prop :=
		| Chain_empty: forall start, Chain [start]
		| Chain_link: forall past cur next,
			Link cur next
			-> Chain (cur :: past)
			-> Chain (next :: (cur :: past))
	.
	Hint Constructors Chain: core.

	Inductive Chained: T -> T -> Prop :=
		| Chained_start_finish: forall start mid finish,
			Chain (finish :: (mid ++ [start]))
			-> Chained start finish
	.

	Theorem Chain_to_Chained l:
		Chain l
		-> Chained start finish.
	Proof.

	Qed.


End Chain.
