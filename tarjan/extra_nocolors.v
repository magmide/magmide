From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ord_minn_le n (i j : 'I_n) : minn i j < n.
Proof. by rewrite gtn_min ltn_ord. Qed.
Definition ord_minn {n} (i j : 'I_n) := Ordinal (ord_minn_le i j).

Section ord_min.
Variable (n : nat).
Notation T := (ord_max : 'I_n.+1).
Notation min := (@ord_minn n.+1).

Lemma minTo : left_id T min.
Proof. by move=> i; apply/val_inj; rewrite /= (minn_idPr _) ?leq_ord. Qed.

Lemma minoT : right_id T min.
Proof. by move=> i; apply/val_inj; rewrite /= (minn_idPl _) ?leq_ord. Qed.

Lemma minoA : associative min.
Proof. by move=> ???; apply/val_inj/minnA. Qed.

Lemma minoC : commutative min.
Proof. by move=> ??; apply/val_inj/minnC. Qed.

Canonical ord_minn_monoid := Monoid.Law minoA minTo minoT.
Canonical ord_minn_comoid := Monoid.ComLaw minoC.

End ord_min.

Notation "\min_ ( i | P ) F" := (\big[ord_minn/ord_max]_(i | P%B) F%N)
  (at level 41, F at level 41, i at level 50,
   format "'[' \min_ ( i  |  P ) '/  '  F ']'") : nat_scope.
Notation "\min_ i F" := (\big[ord_minn/ord_max]_i F%N) 
  (at level 41, F at level 41, i at level 0,
   format "'[' \min_ i '/  '  F ']'") : nat_scope.
Notation "\min_ ( i 'in' A | P ) F" :=
 (\big[ord_minn/ord_max]_(i in A | P%B) F%N)
  (at level 41, F at level 41, i, A at level 50,
   format "'[' \min_ ( i  'in'  A  |  P ) '/  '  F ']'") : nat_scope.
Notation "\min_ ( i 'in' A ) F" :=
 (\big[ord_minn/ord_max]_(i in A) F%N)
  (at level 41, F at level 41, i, A at level 50,
   format "'[' \min_ ( i  'in'  A ) '/  '  F ']'") : nat_scope.

Section extra_bigmin.

Variables (n : nat) (I : finType).
Implicit Type (F : I -> 'I_n.+1).

Lemma geq_bigmin_cond (P : pred I) F i0 :
  P i0 -> F i0 >= \min_(i | P i) F i.
Proof. by move=> Pi0; rewrite (bigD1 i0) //= geq_minl. Qed.
Arguments geq_bigmin_cond [P F].

Lemma geq_bigmin F (i0 : I) : F i0 >= \min_i F i.
Proof. exact: geq_bigmin_cond. Qed.

Lemma bigmin_geqP (P : pred I) (m : 'I_n.+1) F :
  reflect (forall i, P i -> F i >= m) (\min_(i | P i) F i >= m).
Proof.
apply: (iffP idP) => leFm => [i Pi|].
  by apply: leq_trans leFm _; apply: geq_bigmin_cond.
by elim/big_ind: _; rewrite ?leq_ord // => m1 m2; rewrite leq_min => ->.
Qed.

Lemma bigmin_inf i0 (P : pred I) (m : 'I_n.+1) F :
  P i0 -> m >= F i0 -> m >= \min_(i | P i) F i.
Proof.
by move=> Pi0 le_m_Fi0; apply: leq_trans (geq_bigmin_cond i0 Pi0) _.
Qed.

Lemma bigmin_eq_arg i0 (P : pred I) F :
  P i0 -> \min_(i | P i) F i = F [arg min_(i < i0 | P i) F i].
Proof.
move=> Pi0; case: arg_minP => //= i Pi minFi.
by apply/val_inj/eqP; rewrite eqn_leq geq_bigmin_cond //=; apply/bigmin_geqP.
Qed.

Lemma eq_bigmin_cond (A : pred I) F :
  #|A| > 0 -> {i0 | i0 \in A & \min_(i in A) F i = F i0}.
Proof.
case: (pickP A) => [i0 Ai0 _ | ]; last by move/eq_card0->.
by exists [arg min_(i < i0 in A) F i]; [case: arg_minP | apply: bigmin_eq_arg].
Qed.

Lemma eq_bigmin F : #|I| > 0 -> {i0 : I | \min_i F i = F i0}.
Proof. by case/(eq_bigmin_cond F) => x _ ->; exists x. Qed.

Lemma bigmin_setU (A B : {set I}) F :
  \min_(i in (A :|: B)) F i =
  ord_minn (\min_(i in A) F i) (\min_(i in B) F i).
Proof.
have d : [disjoint A :\: B & B] by rewrite -setI_eq0 setIDAC setDIl setDv setI0.
rewrite (eq_bigl [predU (A :\: B) & B]) ?bigU//=; last first.
  by move=> y; rewrite !inE; case: (_ \in _) (_ \in _) => [] [].
symmetry; rewrite (big_setID B) /= [X in ord_minn X _]minoC -minoA.
congr (ord_minn _ _); apply: val_inj; rewrite /= (minn_idPr _)//.
by apply/bigmin_geqP=> i; rewrite inE => /andP[iA iB]; rewrite (bigmin_inf iB).
Qed.

End extra_bigmin.

Arguments geq_bigmin_cond [n I P F].
Arguments geq_bigmin [n I F].
Arguments bigmin_geqP [n I P m F].
Arguments bigmin_inf [n I] i0 [P m F].
Arguments bigmin_eq_arg [n I] i0 [P F].

Section extra_fintype.

Variable V : finType.

Definition relto (a : pred V) (g : rel V) := [rel x y | (y \in a) && g x y].
Definition relfrom (a : pred V) (g : rel V) := [rel x y | (x \in a) && g x y].

Lemma connect_rev (g : rel V) :
  connect g =2 (fun x => connect (fun x => g^~ x) ^~ x).
Proof.
move=> x y; apply/connectP/connectP=> [] [p gp ->];
[exists (rev (belast x p))|exists (rev (belast y p))]; rewrite ?rev_path //;
by case: (lastP p) => //= ??; rewrite belast_rcons rev_cons last_rcons.
Qed.

Lemma path_to a g z p : path (relto a g) z p = (path g z p) && (all a p).
Proof.
apply/(pathP z)/idP => [fgi|/andP[/pathP gi] /allP ga]; last first.
  by move=> i i_lt /=; rewrite gi ?andbT ?[_ \in _]ga // mem_nth.
rewrite (appP (pathP z) idP) //=; last by move=> i /fgi /= /andP[_ ->].
by apply/(all_nthP z) => i /fgi /andP [].
Qed.

Lemma path_from a g z p :
  path (relfrom a g) z p = (path g z p) && (all a (belast z p)).
Proof. by rewrite -rev_path path_to all_rev rev_path. Qed.


Lemma connect_to (a : pred V) (g : rel V) x z : connect g x z ->
  exists y, [/\ (y \in a) ==> (x == y) && (x \in a),
                 connect g x y & connect (relto a g) y z].
Proof.
move=> /connectP [p gxp ->].
pose P := [pred i | let y := nth x (x :: p) i in
  [&& connect g x y & connect (relto a g) y (last x p)]].
have [] := @ex_minnP P.
  by exists (size p); rewrite /= nth_last (path_connect gxp) //= mem_last.
move=> i /= /andP[g1 g2] i_min; exists (nth x (x :: p) i); split=> //.
case: i => [|i] //= in g1 g2 i_min *; first by rewrite eqxx /= implybb.
have i_lt : i < size p.
  by rewrite i_min // !nth_last /= (path_connect gxp) //= mem_last.
have [<-/=|neq_xpi /=] := altP eqP; first by rewrite implybb.
have := i_min i; rewrite ltnn => /contraNF /(_ isT) <-; apply/implyP=> axpi.
rewrite (connect_trans _ g2) ?andbT //; last first.
  by rewrite connect1 //= [_ \in _]axpi /= (pathP x _).
by rewrite (path_connect gxp) //= mem_nth //= ltnW.
Qed.

Lemma connect_from (a : pred V) (g : rel V) x z : connect g x z ->
  exists y, [/\ (y \in a) ==> (z == y) && (z \in a),
                connect (relfrom a g) x y & connect g y z].
Proof.
rewrite connect_rev => cgxz; have [y [ayaz]]//= := connect_to a cgxz.
by exists y; split; rewrite // connect_rev.
Qed.

Lemma connect1l (g : rel V) x z :
  connect g x z -> z != x -> exists2 y, g x y & connect g y z.
Proof.
move=> /connectP [[|y p] //= xyp ->]; first by rewrite eqxx.
by move: xyp=> /andP[]; exists y => //; apply/connectP; exists p.
Qed.

Lemma connect1r (g : rel V) x z :
  connect g x z -> z != x -> exists2 y, connect g x y & g y z.
Proof.
move=> xz zNx; move: xz; rewrite connect_rev => /connect1l.
by rewrite eq_sym => /(_ zNx) [y]; exists y; rewrite // connect_rev.
Qed.

Section connected.

Variable (g : rel V).

Definition connected := forall x y, connect g x y.

Lemma cover1U (A : {set V}) P : cover (A |: P) = A :|: cover P.
Proof. by apply/setP => x; rewrite /cover bigcup_setU big_set1. Qed.

Lemma connectedU (A B : {set V}) : {in A &, connected} -> {in B &, connected} ->
  {in A & B, connected} -> {in B & A, connected} -> {in A :|: B &, connected}.
Proof.
move=> cA cB cAB cBA z t; rewrite !inE => /orP[zA|zB] /orP[tA|tB];
by[apply: cA|apply: cB|apply: cAB|apply: cBA].
Qed.

End connected.

Section Symconnect.

Variable r : rel V.

(* x is symconnected to y *)
Definition symconnect x y := connect r x y && connect r y x.

Lemma symconnect0 : reflexive symconnect.
Proof. by move=> x; apply/andP. Qed.

Lemma symconnect_sym : symmetric symconnect.
Proof. by move=> x y; apply/andP/andP=> [] []. Qed.

Lemma symconnect_trans : transitive symconnect.
Proof.
move=> x y z /andP[Cyx Cxy] /andP[Cxz Czx].
by rewrite /symconnect (connect_trans Cyx) ?(connect_trans Czx).
Qed.
Hint Resolve symconnect0 symconnect_sym symconnect_trans.

Lemma symconnect_equiv : equivalence_rel symconnect.
Proof. by apply/equivalence_relP; split; last apply/sym_left_transitive. Qed.

(*************************************************)
(* Connected components of the graph, abstractly *)
(*************************************************)

Definition sccs := equivalence_partition symconnect setT.

Lemma sccs_partition : partition sccs setT.
Proof. by apply: equivalence_partitionP => ?*; apply: symconnect_equiv. Qed.

Definition cover_sccs := cover_partition sccs_partition.

Lemma trivIset_sccs : trivIset sccs.
Proof. by case/and3P: sccs_partition. Qed.
Hint Resolve trivIset_sccs.

Notation scc_of := (pblock sccs).

Lemma mem_scc x y : x \in scc_of y = symconnect y x.
Proof.
by rewrite pblock_equivalence_partition // => ?*; apply: symconnect_equiv.
Qed.

Definition def_scc scc x := @def_pblock _ _ scc x trivIset_sccs.

Definition is_subscc (A : {set V}) := A != set0 /\
                                      {in A &, forall x y, connect r x y}.

Lemma is_subscc_in_scc (A : {set V}) :
  is_subscc A -> exists2 scc, scc \in sccs & A \subset scc.
Proof.
move=> []; have [->|[x xA]] := set_0Vmem A; first by rewrite eqxx.
move=> AN0 A_sub; exists (scc_of x); first by rewrite pblock_mem ?cover_sccs.
by apply/subsetP => y yA; rewrite mem_scc /symconnect !A_sub.
Qed.

Lemma is_subscc1 x (A : {set V}) : x \in A ->
  (forall y, y \in A -> connect r x y /\ connect r y x) -> is_subscc A.
Proof.
move=> xA AP; split; first by apply: contraTneq xA => ->; rewrite inE.
by move=> y z /AP [xy yx] /AP [xz zx]; rewrite (connect_trans yx).
Qed.

End Symconnect.

Lemma setUD (B A C : {set V}) : B \subset A -> C \subset B -> 
  (A :\: B) :|: (B :\: C) = (A :\: C).
Proof.
move=> subBA subCB; apply/setP=> x; rewrite !inE.
have /implyP  := subsetP subBA x; have /implyP  := subsetP subCB x.
by do !case: (_ \in _).
Qed.

Lemma setUDl (T : finType) (A B : {set T}) : A :|: B :\: A = A :|: B.
Proof. by apply/setP=> x; rewrite !inE; do !case: (_ \in _). Qed.

Lemma subset_cover (sccs sccs' : {set {set V}}) :
  sccs \subset sccs' -> cover sccs \subset cover sccs'.
Proof.
move=> /subsetP subsccs; apply/subsetP=> x /bigcupP [scc /subsccs].
by move=> scc' x_in; apply/bigcupP; exists scc.
Qed.

Lemma disjoint1s (A : pred V) (x : V) : [disjoint [set x] & A] = (x \notin A).
Proof.
apply/pred0P/idP=> [/(_ x)/=|]; first by rewrite inE eqxx /= => ->.
by move=> xNA y; rewrite !inE; case: eqP => //= ->; apply/negbTE.
Qed.

Lemma disjoints1 (A : pred V) (x : V) : [disjoint A & [set x]] = (x \notin A).
Proof. by rewrite disjoint_sym disjoint1s. Qed.

End extra_fintype.
