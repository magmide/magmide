From mathcomp Require Import all_ssreflect.
Require Import extra_nocolors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section tarjan.

Variable (V : finType) (successor_seq : V -> seq V).
Notation successors x := [set y in successor_seq x].
Notation infty := #|V|.

(*************************************************************)
(*               Tarjan 72 algorithm,                        *)
(* rewritten in a functional style  with extra modifications *)
(*************************************************************)

Record env := Env {esccs : {set {set V}}; num: {ffun V -> nat}}.

Definition visited e := [set x | num e x <= infty].
Notation sn e := #|visited e|.
Definition stack e := [set x | num e x < sn e].

Definition visit x e :=
  Env (esccs e) (finfun [eta num e with x |-> sn e]).
Definition store scc e :=
  Env (scc |: esccs e) [ffun x => if x \in scc then infty else num e x].

Definition dfs1 dfs x e :=
    let: (n1, e1) as res := dfs (successors x) (visit x e) in
    if n1 < sn e then res else (infty, store (stack e1 :\: stack e) e1).

Definition dfs dfs1 dfs (roots : {set V}) e :=
  if [pick x in roots] isn't Some x then (infty, e) else
  let: (n1, e1) := if num e x <= infty then (num e x, e) else dfs1 x e in
  let: (n2, e2) := dfs (roots :\ x) e1 in (minn n1 n2, e2).

Fixpoint rec k r e :=
  if k is k.+1 then dfs (dfs1 (rec k)) (rec k) r e
  else (infty, e).

Definition e0 := (Env set0 [ffun _ => infty.+1]).
Definition tarjan := let: (_, e) := rec (infty * infty.+2) setT e0 in esccs e.

(*****************)
(* Abbreviations *)
(*****************)

Notation edge := (grel successor_seq).
Notation gconnect := (connect edge).
Notation gsymconnect := (symconnect edge).
Notation gsccs := (sccs edge).
Notation gscc_of := (pblock gsccs).
Notation gconnected := (connected edge).
Notation new_stack e1 e2 := (stack e2 :\: stack e1).
Notation new_visited e1 e2 := (visited e2 :\: visited e1).
Notation inord := (@inord infty).

(*******************)
(* next, and nexts *)
(*******************)

Section Nexts.
Variable (D : {set V}).

Definition nexts (A : {set V}) :=
  \bigcup_(v in A) [set w in connect (relfrom (mem D) edge) v].

Lemma nexts0 : nexts set0 = set0.
Proof. by rewrite /nexts big_set0. Qed.

Lemma nexts1 x :
  nexts [set x] = x |: (if x \in D then nexts (successors x) else set0).
Proof.
apply/setP=> y; rewrite /nexts big_set1 !inE.
have [->|neq_yx/=] := altP eqP; first by rewrite connect0.
apply/idP/idP=> [/connect1l[]// z/=/andP[/= xD xz zy]|].
  by rewrite xD; apply/bigcupP; exists z; rewrite !inE.
case: ifPn; rewrite ?inE// => xD /bigcupP[z]; rewrite !inE.
by move=> xz; apply/connect_trans/connect1; rewrite /= xD.
Qed.

Lemma nextsU A B : nexts (A :|: B) = nexts A :|: nexts B.
Proof. exact: bigcup_setU. Qed.

Lemma nextsS (A : {set V}) : A \subset nexts A.
Proof. by apply/subsetP=> a aA; apply/bigcupP; exists a; rewrite ?inE. Qed.

Lemma nextsT : nexts setT = setT.
Proof. by apply/eqP; rewrite eqEsubset nextsS subsetT. Qed.

Lemma nexts_id (A : {set V}) : nexts (nexts A) = nexts A.
Proof.
apply/eqP; rewrite eqEsubset nextsS andbT; apply/subsetP=> x.
move=> /bigcupP[y /bigcupP[z zA]]; rewrite !inE => /connect_trans yto /yto zx.
by apply/bigcupP; exists z; rewrite ?inE.
Qed.

Lemma in_nextsW A y : y \in nexts A -> exists2 x, x \in A & gconnect x y.
Proof.
move=>/bigcupP[x xA]; rewrite inE => xy; exists x => //.
by apply: connect_sub xy => u v /andP[_ /connect1].
Qed.

End Nexts.

Lemma sub_nexts (D D' A B : {set V}) :
  D \subset D' -> A \subset B -> nexts D A \subset nexts D' B.
Proof.
move=> /subsetP subD /subsetP subAB; apply/subsetP => v /bigcupP[a /subAB aB].
rewrite !inE => av; apply/bigcupP; exists a; rewrite ?inE //=.
by apply: connect_sub av => x y /andP[xD xy]; rewrite connect1//= subD.
Qed.

Lemma nextsUI A B C : nexts B A \subset A ->
  A :|: nexts (B :&: ~: A) C = A :|: nexts B C.
Proof.
move=> subA; apply/setP=> y; rewrite !inE; have [//|/= yNA] := boolP (y \in A).
apply/idP/idP; first by apply: subsetP; rewrite sub_nexts// subsetIl.
move=> /bigcupP[z zr zy]; apply/bigcupP; exists z; first by [].
rewrite !inE; apply: contraTT isT => Nzy; move: zy; rewrite !inE.
move=> /(connect_from (mem (~: A))) /= [t].
rewrite !inE => -[xtxy zt ty]; move: zt.
rewrite (@eq_connect _ _ (relfrom (mem (B :&: ~: A)) edge)); last first.
  by move=> u v /=; rewrite !inE andbCA andbA.
case: (altP eqP) xtxy => /= [<-|neq_yt]; first by rewrite (negPf Nzy).
rewrite implybF negbK => tA zt; rewrite -(negPf yNA) (subsetP subA)//.
by apply/bigcupP; exists t; rewrite // inE.
Qed.

Lemma nexts1_split (A : {set V}) x : x \in A ->
  nexts A [set x] = x |: nexts (A :\ x) (successors x).
Proof.
move=> xA; apply/setP=> y; apply/idP/idP; last first.
  rewrite nexts1 !inE xA; case: (_ == _); rewrite //=.
  by apply: subsetP; rewrite sub_nexts// subsetDl.
move=> /bigcupP[z]; rewrite !inE => /eqP {z}->.
move=> /connectP[p /shortenP[[_ _ _ /eqP->//|z q/=/andP[/andP[_ xz]]]]].
rewrite path_from => /andP[zq] /allP/= qA.
move=> /and3P[xNzq _ _] _ ->; apply/orP; right.
apply/bigcupP; exists z; rewrite !inE//.
apply/connectP; exists q; rewrite // path_from zq/=.
apply/allP=> t tq; rewrite !inE qA ?andbT//.
by apply: contraNneq xNzq=> <-; apply: mem_belast tq.
Qed.

(*******************)
(* Well formed env *)
(*******************)

Lemma num_le_infty e x : num e x <= infty = (x \in visited e).
Proof. by rewrite inE. Qed.

Lemma num_lt_sn e x : num e x < sn e = (x \in stack e).
Proof. by rewrite inE. Qed.

Lemma visited_visit e x : visited (visit x e) = x |: visited e.
Proof.
by apply/setP=> y; rewrite !inE ffunE/=; case: (altP eqP); rewrite ?max_card.
Qed.

Lemma sub_stack_visited e : stack e \subset visited e.
Proof.
by apply/subsetP => x; rewrite !inE => /ltnW /leq_trans ->//; rewrite max_card.
Qed.

Lemma sub_new_stack_visited e1 e2: new_stack e1 e2 \subset visited e2.
Proof. by rewrite (subset_trans _ (sub_stack_visited _)) ?subsetDl. Qed.

Section wfenv.

Record wf_env e := WfEnv {
  sub_gsccs : esccs e \subset gsccs;
  num_lt_V_is_stack : forall x, num e x < infty -> num e x < sn e;
  num_sccs : forall x, (num e x == infty) = (x \in cover (esccs e));
  le_connect : forall x y, num e x <= num e y < sn e -> gconnect x y;
}.

Variables (e : env) (e_wf : wf_env e).

Lemma num_gt_V x : x \notin visited e -> num e x > infty.
Proof. by rewrite inE -ltnNge. Qed.

Lemma num_lt_V x : (num e x < infty) = (num e x < sn e).
Proof.
apply/idP/idP => [/num_lt_V_is_stack//|]; first exact.
by move=> /leq_trans; apply; rewrite max_card.
Qed.

Lemma num_lt_card x (A : pred V) : visited e \subset A ->
  (num e x < #|A|) = (num e x < sn e).
Proof.
move=> subeA; apply/idP/idP => /leq_trans.
  by rewrite -num_lt_V; apply; rewrite max_card.
by apply; rewrite subset_leq_card.
Qed.

Lemma visitedE : visited e = stack e :|: cover (esccs e).
Proof. by apply/setP=> x; rewrite !inE leq_eqVlt -num_sccs// num_lt_V orbC. Qed.

Lemma sub_sccs_visited : cover (esccs e) \subset visited e.
Proof. by apply/subsetP => x; rewrite !inE -num_sccs// => /eqP->. Qed.

Lemma stack_visit x : x \notin visited e -> stack (visit x e) = x |: stack e.
Proof.
move=> xNvisited; apply/setP=> y; rewrite !inE/= ffunE/= visited_visit.
have [->|neq_yx]//= := altP eqP; first by rewrite cardsU1 xNvisited ltnS ?leqnn.
by rewrite num_lt_card// subsetUr.
Qed.

End wfenv.

Lemma wf_visit e x : wf_env e ->
   (forall y, num e y < sn e -> gconnect y x) ->
   x \notin visited e -> wf_env (visit x e).
Proof.
move=> e_wf x_connected xNvisited.
constructor=> [|y|y|] //=; rewrite ?inE ?ffunE/=.
- exact: sub_gsccs.
- rewrite visited_visit cardsU1 xNvisited; case: ifPn => // _.
  by rewrite num_lt_V// ltnS => /ltnW.
- have [->|] := altP (y =P x); last by rewrite num_sccs.
  rewrite -num_sccs// eq_sym !gtn_eqF ?num_gt_V//.
  by rewrite (@leq_trans #|x |: visited e|) ?max_card// cardsU1 xNvisited.
move=> y z; rewrite !ffunE/=.
have sub_visit : visited e \subset visited (visit x e).
  by apply/subsetP => ?; rewrite visited_visit !inE orbC => ->.
have [{y}->|neq_yx] := altP eqP; have [{z}->|neq_zx]//= := altP eqP.
+ by rewrite num_lt_card//; case: ltngtP.
+ move=> /andP[/leq_ltn_trans lt/lt].
  by rewrite num_lt_card//; apply: x_connected.
+ by rewrite num_lt_card//; apply: le_connect.
Qed.

Definition subenv e1 e2 := [&&
  esccs e1 \subset esccs e2,
  [forall x, (num e1 x <= infty) ==> (num e2 x == num e1 x)] &
  [forall x, (num e2 x < sn e1) ==> (num e1 x < sn e1)]].

Lemma sub_sccs e1 e2 : subenv e1 e2 -> esccs e1 \subset esccs e2.
Proof. by move=> /and3P[]. Qed.

Lemma sub_snum e1 e2 : subenv e1 e2 -> forall x, num e1 x <= infty ->
  num e2 x = num e1 x.
Proof. by move=> /and3P[_ /forall_inP /(_ _ _) /eqP]. Qed.

Lemma sub_vnum e1 e2 : subenv e1 e2 -> forall x, num e1 x < sn e1 ->
  num e2 x = num e1 x.
Proof.
move=> sube12 x /ltnW num_lt; rewrite (sub_snum sube12)//.
by rewrite (leq_trans num_lt)// max_card.
Qed.

Lemma sub_num_lt e1 e2 : subenv e1 e2 ->
  forall x, (num e1 x < sn e1) = (num e2 x < sn e1).
Proof.
move=> /and3P[_ /forall_inP /(_ _ _)/eqP num_eq /forall_inP] num_lt x.
have nume1_lt := num_lt x; apply/idP/idP => // {nume1_lt}nume1_lt.
by rewrite num_eq ?inE// (leq_trans (ltnW nume1_lt))//  max_card.
Qed.

Lemma sub_visited e1 e2 : subenv e1 e2 -> visited e1 \subset visited e2.
Proof.
move=> sube12; apply/subsetP=> x; rewrite !inE => x_visited1.
by rewrite (sub_snum sube12)// inE.
Qed.

Lemma leq_sn e1 e2 : subenv e1 e2 -> sn e1 <= sn e2.
Proof. by move=> sube12; rewrite subset_leq_card// sub_visited. Qed.

Lemma sub_stack e1 e2 : subenv e1 e2 -> stack e1 \subset stack e2.
Proof.
move=> sube12; apply/subsetP=> x; rewrite !inE => x_stack.
by rewrite (sub_vnum sube12)// (leq_trans x_stack)// leq_sn.
Qed.

Lemma new_stackE e1 e2 : subenv e1 e2 ->
  new_stack e1 e2 = [set x | sn e1 <= num e2 x < sn e2].
Proof.
move=> sube12; apply/setP=> x; rewrite !inE.
have [x_e2|] := ltnP (num e2 x) (sn e2); rewrite ?andbT ?andbF//.
have [e1_after|e1_before] /= := leqP (sn e1) (num e1 x).
  by rewrite leqNgt -sub_num_lt// -leqNgt.
by rewrite leqNgt -sub_num_lt// e1_before.
Qed.

Lemma new_visitedE e1 e2 : wf_env e1 -> wf_env e2 -> subenv e1 e2 ->
  (new_visited e1 e2) =
    (new_stack e1 e2) :|: cover (esccs e2) :\: cover (esccs e1).
Proof.
move=> e1_wf e2_wf sube12; rewrite !visitedE//; apply/setP=> x.
rewrite !inE -!num_sccs -?num_lt_V//; do 2!case: ltngtP => //=.
  by rewrite num_lt_V// (sub_num_lt sube12)// => ->; rewrite ltnNge max_card.
by move=> xe2 xe1; move: xe2; rewrite (sub_snum sube12)// ?xe1// ltnn.
Qed.

Lemma sub_new_stack_new_visited e1 e2 :
    subenv e1 e2 -> wf_env e1 -> wf_env e2 ->
  (new_stack e1 e2) \subset (new_visited e1 e2).
Proof.
by move=> e1wf e2wf sube12; rewrite (@new_visitedE e1 e2)// subsetUl.
Qed.

Lemma sub_refl e : subenv e e.
Proof. by rewrite /subenv !subxx /=; apply/andP; split; apply/forall_inP. Qed.
Hint Resolve sub_refl.

Lemma sub_trans : transitive subenv.
Proof.
move=> e2 e1 e3 sub12 sub23; rewrite /subenv.
rewrite (subset_trans (sub_sccs sub12))// ?sub_sccs//=.
apply/andP; split; apply/forall_inP=> x xP.
  by rewrite (sub_snum sub23) ?(sub_snum sub12)//.
have x2 : num e3 x < sn e2 by rewrite (leq_trans xP)// leq_sn.
by rewrite (sub_num_lt sub12)// -(sub_vnum sub23)// (sub_num_lt sub23).
Qed.

Lemma sub_visit e x : x \notin visited e -> subenv e (visit x e).
Proof.
move=> xNvisited; rewrite /subenv subxx/=; apply/andP; split; last first.
  by apply/forall_inP => y; rewrite !ffunE/=; case: ifP; rewrite ?ltnn.
apply/forall_inP => y y_in; rewrite !ffunE/=.
by case: (altP (y =P x)) xNvisited => // <-; rewrite inE y_in.
Qed.

Lemma visited_store (A : {set V}) e : A \subset visited e ->
  visited (store A e) = visited e.
Proof.
move=> A_sub; apply/setP=> x; rewrite !inE/= ffunE.
by case: ifPn => // /(subsetP A_sub); rewrite inE leqnn => ->.
Qed.

Lemma stack_store (A : {set V}) e : A \subset visited e ->
  stack (store A e) = stack e :\: A.
Proof.
move=> A_sub; apply/setP => x; rewrite !inE visited_store//= ffunE.
by case: (x \in A); rewrite //= ltnNge max_card.
Qed.

(*********************)
(* DFS specification *)
(*********************)

Definition outenv (roots : {set V}) (e e' : env) := [/\
  {in new_stack e e' &, gconnected},
  {in new_stack e e', forall x, exists2 y, y \in stack e & gconnect x y} &
  visited e' = visited e :|: nexts (~: visited e) roots ].

Variant dfs_spec_def (dfs : nat * env) (roots : {set V}) e :
  (nat * env) -> nat -> env -> Type := DfsSpec ne' (n : nat) e' of
    ne' = (n, e') &
    n = \min_(x in nexts (~: visited e) roots) inord (num e' x) &
    wf_env e' & subenv e e' & outenv roots e e' :
  dfs_spec_def dfs roots e ne' n e'.
Notation dfs_spec ne' roots e := (dfs_spec_def ne' roots e ne' ne'.1 ne'.2).

Definition dfs_correct dfs (roots : {set V}) e := wf_env e ->
  {in stack e & roots, gconnected} -> dfs_spec (dfs roots e) roots e.
Definition dfs1_correct dfs1 x e := wf_env e -> x \notin visited e ->
  {in stack e & [set x], gconnected} -> dfs_spec (dfs1 x e) [set x] e.

(*****************)
(* Correctness *)
(*****************)

Lemma dfsP dfs1 dfsrec (roots : {set V}) e:
  (forall x, x \in roots -> dfs1_correct dfs1 x e) ->
  (forall x, x \in roots -> forall e1, subenv e e1 ->
     dfs_correct dfsrec (roots :\ x) e1) ->
  dfs_correct (dfs dfs1 dfsrec) roots e.
Proof.
rewrite /dfs => dfs1P dfsP e_wf roots_connected.
case: pickP => /= [x x_roots|]; last first.
  move=> r0; have {r0}r_eq0 : roots = set0 by apply/setP=> x; rewrite inE.
  do ?constructor=> //=;
    rewrite ?setDv ?r_eq0 ?nexts0 ?sub0set ?eqxx ?setU0 ?big_set0 //=;
    by move=> ?; rewrite inE.
have [numx_gt|numx_le]/= := ltnP; last first.
  have x_visited : x \in visited e by rewrite inE.
  case: dfsP => //= [u v ve|_ _ e1 ->-> e1_wf subee1 [new1c new1old visited1E]].
    by rewrite inE => /andP[_ v_roots]; rewrite roots_connected.
  constructor => //=.
    rewrite -[in RHS](setD1K x_roots) nextsU nexts1 inE x_visited/= setU0.
    by rewrite bigmin_setU /= big_set1/= (@sub_snum e e1)// inordK//.
  constructor=> //=; rewrite -(setD1K x_roots) nextsU nexts1 inE x_visited/=.
  by rewrite setU0 setUCA setUA [x |: _](setUidPr _) ?sub1set.
case: dfs1P => //=; first by rewrite inE -ltnNge.
  by move=> u v ue; rewrite inE => /eqP->; apply: roots_connected.
move=> _ _  e1 -> -> e1_wf subee1 [new1c new1old visited1E].
case: dfsP => //= [u v ue1|_ _ e2 -> -> e2_wf sube12 [new2c new2old visited2E]].
  rewrite inE => /andP[_ v_roots].
  have [ue|uNe] := boolP (u \in stack e); first by rewrite roots_connected.
  have [|w we] := new1old u; first by rewrite inE ue1 uNe.
  by move=> /connect_trans->//; rewrite roots_connected//.
have sube2 : subenv e e2 by exact: sub_trans sube12.
have nexts_split : nexts (~: visited e) roots =
      nexts (~: visited e) [set x] :|: nexts (~: visited e1) (roots :\ x).
  rewrite -[in LHS](setD1K x_roots) nextsU visited1E.
  by rewrite setCU nextsUI// nexts_id.
constructor => //=.
  rewrite (eq_bigr (inord \o num e2)).
   by rewrite -[LHS]/(val (ord_minn _ _)) -bigmin_setU /= -nexts_split.
  move=> y y_in; rewrite /= (@sub_snum e1 e2)// num_le_infty.
  by rewrite visited1E setUC inE y_in.
constructor => /=.
+ rewrite -(@setUD _ (stack e1)) ?sub_stack//.
  apply: connectedU => // y z; last first.
    rewrite !new_stackE// ?inE => /andP[y_ge y_lt] /andP[z_ge z_lt].
    rewrite (@le_connect e2) // z_lt (leq_trans _ z_ge)//.
    by rewrite (sub_vnum sube12)// ltnW.
  rewrite !new_stackE// ?inE => /andP[y_ge y_lt] /andP[z_ge z_lt].
  have [|r] := new2old y; rewrite ?new_stackE ?inE ?y_ge//.
  move=> r_lt /connect_trans->//; have [rz|zr] := leqP (num e1 r) (num e1 z).
    by rewrite (@le_connect e1)// rz/=.
  by rewrite new1c ?new_stackE ?inE ?z_ge ?z_lt //= (leq_trans z_ge)// ltnW.
+ move=> y; rewrite ?new_stackE ?inE// => /andP[y_ge y_lt].
  have [y_lt1|y_ge1] := ltnP (num e1 y) (sn e1).
    have [|r] := new1old y; last by exists r.
    by rewrite new_stackE ?inE// ?y_lt1 -(sub_vnum sube12) ?y_ge.
  have [|r r_lt1 yr] := new2old y; first by rewrite !inE -leqNgt y_ge1//.
  rewrite ?inE in r_lt1; have [r_lt|r_ge] := ltnP (num e r) (sn e).
    by exists r; rewrite ?inE.
  have [|r' r's rr'] := new1old r; first by rewrite ?inE -leqNgt r_ge r_lt1.
  by exists r'; rewrite // (connect_trans yr rr').
+ by rewrite visited2E {1}visited1E nexts_split setUA.
Qed.

Lemma dfs1P dfs x e (A := successors x) :
  dfs_correct dfs A (visit x e) -> dfs1_correct (dfs1 dfs) x e.
Proof.
rewrite /dfs1 => dfsP e_wf xNvisited x_connected.
have subexe: subenv e (visit x e) by exact: sub_visit.
have numx : num e x > infty by apply: num_gt_V.
have xNstack : x \notin stack e.
  by rewrite inE -leqNgt (leq_trans _ numx) ?leqW ?max_card.
have xe_wf : wf_env (visit x e).
  by apply: wf_visit => // y y_lt; rewrite x_connected ?inE.
have nexts1E : nexts (~: visited e) [set x] =
    x |: nexts (~: (x |: visited e)) A.
  by rewrite nexts1_split ?setDE ?setCU 1?setIC 1?inE.
case: dfsP => //=.
  rewrite stack_visit// => u v; rewrite in_setU1=> /predU1P[->|ue];
  rewrite inE => /(@connect1 _ edge)// /(connect_trans _)->//.
  by rewrite x_connected// set11.
move=> _ _ e1 //= -> -> e1_wf subxe1 [newc new_old visited1E].
have sube1 : subenv e e1 by apply: sub_trans subxe1.
have num1x : num e1 x = sn e.
  by rewrite (sub_snum subxe1)// ?inE ?ffunE/= ?eqxx// max_card.
rewrite visited_visit in visited1E *.
have lt_sn_sn1 : sn e < sn e1.
  by rewrite (leq_trans _ (leq_sn subxe1))// visited_visit cardsU1 xNvisited.
have x_visited1 : x \in visited e1 by rewrite visited1E inE setU11.
have x_stack : x \in stack e1.
  by rewrite (subsetP (sub_stack subxe1))//= stack_visit// setU11.
have [min_after|min_before] := leqP; last first.
  constructor => //=.
    rewrite nexts1E bigmin_setU big_set1 /= inordK ?num1x ?ltnS ?max_card//.
    by rewrite (minn_idPr _)// ltnW.
  constructor=> //=; last by rewrite nexts1E setUCA setUA visited1E.
    move=> y z; have [-> _|neq_yx] := eqVneq y x.
      by rewrite new_stackE ?inE// -num1x; apply: le_connect.
    rewrite -(@setUD _ (stack (visit x e))) ?sub_stack//.
    rewrite [in X in _ :|: X]stack_visit// setDUl setDv setU0.
    rewrite [_ :\: stack e](setDidPl _) ?disjoint1s//.
    rewrite setUC !in_setU1 (negPf neq_yx)/=.
    move=> y_e1 /predU1P[->|]; last exact: newc y_e1.
    have [t] := new_old y y_e1; rewrite !inE => t_le /connect_trans->//.
    rewrite (@le_connect (visit x e))// andbC; move: t_le.
    by rewrite visited_visit !ffunE /= eqxx cardsU1 xNvisited add1n !ltnS leqnn.
  move=> y; have [v ve xv] : exists2 v, v \in stack e & gconnect x v.
    have [|v] := @eq_bigmin_cond _ _ (mem (nexts (~: (x |: visited e)) A))
                               (inord \o num e1).
      rewrite card_gt0; apply: contraTneq min_before => ->.
      by rewrite big_set0 -leqNgt max_card.
    rewrite !inE => v_in min_is_v; move: min_before; rewrite min_is_v/=.
    rewrite inordK; last by rewrite ltnS num_le_infty visited1E inE v_in orbT.
    rewrite -sub_num_lt// => v_lt; exists v; rewrite ?inE//.
    move: v_in => /in_nextsW[z]; rewrite inE => /(@connect1 _ edge).
    by apply: connect_trans.
  rewrite -(@setUD _ (stack (visit x e))) ?sub_stack//.
  rewrite [in X in _ :|: X]stack_visit// setDUl setDv setU0.
  rewrite [_ :\: stack e](setDidPl _) ?disjoint1s// setUC !in_setU1.
  move=> /predU1P[->|]; first by exists v.
  move=> /new_old[z]; rewrite stack_visit// in_setU1.
  move=> /predU1P[->|]; last by exists z.
  by move=> yx; exists v; rewrite // (connect_trans yx).
have all_geq y : y \in nexts (~: visited e) [set x] ->
  (#|visited e| <= num e1 y) * (num e1 y <= infty).
  have := min_after; have sn_inord : sn e = inord (sn e).
    by rewrite inordK// ltnS max_card.
  rewrite {1}sn_inord; move/bigmin_geqP => /(_ y) y_ge.
  rewrite nexts1E !inE => /predU1P[->|yA]; rewrite ?num1x ?max_card ?leqnn//.
  rewrite sn_inord (leq_trans (y_ge _))// ?inordK//;
  by rewrite ?ltnS num_le_infty visited1E 2!inE yA orbT.
constructor => //=.
- rewrite big1// => y xy; rewrite ffunE new_stackE ?inE//=.
  have y_visited1 : num e1 y <= infty.
    by rewrite num_le_infty visited1E -setUA setUCA -nexts1E inE xy orbT.
  apply/val_inj=> /=; case: ifPn; rewrite ?inordK//.
  by rewrite all_geq//= -num_lt_V// -leqNgt; move: y_visited1; case: ltngtP.
- constructor => //=; rewrite ?visited_store ?sub_new_stack_visited//.
  + rewrite subUset sub_gsccs// andbT sub1set.
    suff -> : new_stack e e1 = gscc_of x by rewrite pblock_mem ?cover_sccs.
    apply/setP=> y; rewrite mem_scc /symconnect.
    have [->|neq_yx] := eqVneq y x.
      by rewrite connect0 inE xNstack inE num1x lt_sn_sn1.
    apply/idP/andP=> [|[xy yx]].
      move=> y_ee1; have y_xee1 : y \in new_stack (visit x e) e1.
        by rewrite inE stack_visit// in_setU1 (negPf neq_yx)/= -in_setD.
      split; last first.
        have [z] := new_old _ y_xee1.
        rewrite stack_visit// in_setU1 => /predU1P[->//|/x_connected].
        by move=> /(_ _ (set11 x))/(connect_trans _) xz /xz.
      have: y \in new_visited (visit x e) e1.
        by apply: subsetP y_xee1; rewrite sub_new_stack_new_visited.
      rewrite inE visited1E in_setU visited_visit//; case: (y \in _) => //=.
      move=> /in_nextsW[z]; rewrite inE=> /(@connect1 _ edge).
      exact: connect_trans.
    have /(connect_from (mem (~: visited e))) [z []] := xy; rewrite inE.
    move=> eq_yz xz zy; have /all_geq [] : z \in nexts (~: visited e) [set x].
      by apply/bigcupP; exists x; rewrite !inE.
    rewrite leqNgt -sub_num_lt// -num_lt_V// -leqNgt => zNstack.
    have zNcover e' : wf_env e' -> z \in cover (esccs e') ->
                      x \in cover (esccs e').
      move=> e'_wf /bigcupP[C] Ce zC; apply/bigcupP; exists C => //.
      have /def_scc: C \in gsccs by apply: subsetP Ce; apply: sub_gsccs.
      move=> /(_ _ zC)<-; rewrite mem_scc /= /symconnect (connect_trans zy)//=.
      by apply: connect_sub xz => ?? /andP[_ /connect1].
    rewrite leq_eqVlt num_sccs// num_lt_V// => /orP[|z_stack].
       move=> /zNcover; rewrite -num_sccs// num1x => /(_ _) /eqP eq_V.
       by rewrite eq_V// ltnNge max_card in lt_sn_sn1.
    have zNvisited : z \notin visited e.
      rewrite inE -ltnNge ltn_neqAle zNstack andbT/= eq_sym num_sccs//.
      by apply: contraTN isT => /(zNcover _ e_wf); rewrite -num_sccs// gtn_eqF.
    move: eq_yz; rewrite zNvisited /= => /andP[/eqP eq_yz _].
    rewrite -eq_yz in zNstack z_stack.
    by rewrite !inE -num_lt_V// -leqNgt zNstack.
  + move=> v; rewrite ffunE/=; case: ifPn; rewrite ?ltnn// => vNe12.
    by rewrite num_lt_V// visited_store.
  + move=> v; rewrite ffunE /= cover1U [in RHS]inE.
    by case: ifPn; rewrite ?eqxx//= => vNe12; rewrite -num_sccs//.
  + move=> y z; rewrite !ffunE; case: ifPn => _.
      by move=> /andP[/leq_ltn_trans Vsmall/Vsmall]; rewrite ltnNge max_card.
    by case: ifPn => _; [by rewrite ltnNge max_card andbF|exact : le_connect].
- rewrite /subenv /= (subset_trans (sub_sccs sube1)) ?subsetUr//=.
  apply/andP; split; apply/forallP => v; apply/implyP;
  rewrite ffunE/= new_stackE// ?inE.
    move=> vs; rewrite (sub_snum sube1)// leqNgt -!num_lt_V// -leqNgt ifN//.
    by apply/negP => /andP[/leq_ltn_trans Vlt/Vlt]; rewrite ltnNge max_card.
  by case: ifPn; [move=> _; rewrite ltnNge max_card|rewrite -sub_num_lt].
- rewrite /outenv stack_store ?visited_store ?sub_new_stack_visited//.
  rewrite setDDr setDUl setDv set0D set0U setDIl !setDv setI0.
  split; do ?by move=> ?; rewrite inE.
  by rewrite visited1E -setUA setUCA -nexts1E.
Qed.

Theorem rec_terminates k (roots : {set V}) e :
  k >= #|~: visited e| * infty.+1 + #|roots| -> dfs_correct (rec k) roots e.
Proof.
move=> k_ge; elim: k => [|k IHk/=] in roots e k_ge *.
  move: k_ge; rewrite leqn0 addn_eq0 cards_eq0 => /andP[_ /eqP-> e_wf _]/=.
  constructor=> //=; rewrite /outenv ?nexts0 ?setDv ?big_set0// ?setU0.
  by split=> // ?; rewrite inE.
apply: dfsP=> x x_roots; last first.
  move=> e1 subee1; apply: IHk; rewrite -ltnS (leq_trans _ k_ge)//.
  rewrite (cardsD1 x roots) x_roots add1n -addSnnS ltn_add2r ltnS.
  by rewrite leq_mul2r //= subset_leq_card// setCS sub_visited.
move=> e_wf xNvisited; apply: dfs1P => //; apply: IHk.
rewrite visited_visit setCU setIC -setDE -ltnS (leq_trans _ k_ge)//.
rewrite (cardsD1 x (~: _)) inE xNvisited add1n mulSnr -addnA ltn_add2l.
by rewrite ltn_addr// ltnS max_card.
Qed.

Lemma visited0 : visited e0 = set0.
Proof. by apply/setP=> y; rewrite !inE ffunE ltnn. Qed.

Lemma stack0 : stack e0 = set0.
Proof. by apply/setP=> y; rewrite !inE ffunE ltnNge leqW ?max_card. Qed.

Theorem tarjan_correct : tarjan = gsccs.
Proof.
rewrite /tarjan mulnSr; case: rec_terminates.
- by rewrite visited0 setC0 cardsT.
- constructor; rewrite /= ?sub0set// => x; rewrite !ffunE//.
  + by rewrite ltnNge leqW//.
  + by rewrite gtn_eqF// /cover big_set0 inE.
  + by move=> y; rewrite !ffunE//= andbC ltnNge leqW// ?max_card.
- by move=> y; rewrite !inE !ffunE/= ltnNge leqW// max_card.
move=> _ _ e -> _ e_wf _ [_]; rewrite stack0 setD0.
have [stacke _|[x xe]] := set_0Vmem (stack e); last first.
  by move=> /(_ _ xe)[?]; rewrite inE.
rewrite visited0 set0U setC0 nextsT => visitede.
have numE x : num e x = infty.
  apply/eqP; have /setP/(_ x) := visitede.
  by rewrite visitedE// stacke set0U !inE -num_sccs.
apply/eqP; rewrite eqEsubset sub_gsccs//=; apply/subsetP => _/imsetP[/=x _->].
have: x \in cover (esccs e) by rewrite -num_sccs ?numE//.
move=> /bigcupP [C Csccs /(def_scc (subsetP (sub_gsccs e_wf) _ Csccs))] eqC.
rewrite -eqC (_ : [set _ in _ | _] = gscc_of x)// in Csccs *.
by apply/setP => y; rewrite !inE mem_scc /=.
Qed.

End tarjan.
