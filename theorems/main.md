```v
Theorem absurd_stuck instr:
  ~(stopping instr)
  -> forall program cur,
  (cur_instr cur program) = Some instr
  -> (forall next, ~(@step program cur next))
  -> False.
Proof.
  intros Hstopping ?? Hcur Hstuck;
  specialize (not_stopping_not_stuck Hstopping program cur Hcur) as [next];
  specialize Hstuck with next; contradiction.
Qed.s



Theorem absurd_well_founded_minimal {T} (P: T -> T -> Prop) (least other: T):
  well_founded P
  -> P least other
  -> ~(P other least).
Proof.
intros.


Qed.

Section well_founded_compatibility.
  Variable A B: Type.
  Variable RA: A -> A -> Prop.
  Variable RB: B -> B -> Prop.

  Variable RB_well_founded: well_founded RB.
  Variable f: A -> B.
  Hypothesis H_compat_A: forall a1 a2: A, (RA a1 a2) -> (RB (f a1) (f a2)).
  Hypothesis H_compat_B: forall a1 a2: A, (RB (f a1) (f a2)) -> (RA a1 a2).

  Theorem yo:
    forall min other, RB (f min) (f other) -> Acc RA min.
  Proof.
intros ?? HRB.
apply H_compat_B in HRB.
Hint Constructors Acc: core.


  Qed.


  Theorem well_founded_compat: well_founded RA.
  Proof.
constructor.

unfold well_founded in *.
constructor.
intros.
rename y into a1; rename a into a2.

specialize (H_compat a1 a2).
remember (f a1) as b1; remember (f a2) as b2.
destruct H_compat as [H_compat_A H_compat_B].
specialize (H_compat_A H) as ?.


specialize (RB_well_founded b1) as Hb1.
specialize (RB_well_founded b2) as Hb2.
inversion Hb1.


specialize (Acc_inv RB_well_founded).

  Qed.

Check RB_well_founded.

EndSection well_founded_compatibility.
```
