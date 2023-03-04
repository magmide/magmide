>
  “number of steps of computation that the program may perform”. This intuition is not entirely
  correct, but it is close enough.

  VJAKδ is now a predicate over both a natural number k ∈ N and a closed value v.
  Intuitively, (k,v) ∈ VJAKδ means that no well-typed program using v at type A will “go
  wrong” in k steps (or less).

what does it mean for something to hold for k steps?


>
  iProp is obtained from a more general construction: uniform predicates over
  a unital resource algebra M, written UPred(M).

  The type UPred(M) consists of predicates over step-indices and resources (from M) which
  are down-closed with respect to the step-index and up-closed with respect to the resource:

  UPred(M) := {P ∈ Prop(N, M) | ∀(n, a) ∈ P. ∀m, b. m ≤ n ⇒ a ;included b ⇒ (m, b) ∈ P}

so if some (n, a) is "proven", then so is any (m, b) where both m is `<=` (earlier than or same?) n and b is `>=` (includes or same) a
so you can take a valid (n, a) and make it either closer in number of steps or involving a larger piece of resource algebra state?


- how does step-indexing *actually* relate to program steps?
- are the step indexes only ever `infinity` or `1`?

```
In the base case, when the argument is a value v, we have to prove the postcondition Q(v)
(after potentially) updating the ghost state. Otherwise, if e is a proper expression, we get to
assume the state interpretation SI(h) (explained below) and have to show two conditions:
(1) the current expression e can make progress in the heap h where progress(e, h) :=
∃e
0
, h0
. (e, h) ❀ (e
0
, h0
) and (2) for any successor expression e
0 and heap h
0
, we have to
show the weakest precondition and the state interpretation after an update to the ghost
state and after a later.
The updates in both cases makes sure that we can always update our ghost state when
we prove a weakest precondition. These updates are instrumental for working with the
state interpretation below and for verifying code which relies on auxiliary ghost state.
The later in the second case ensures that the weakest precondition can be defined as a
guarded fixpoint. Moreover, it ties program steps to laters in our program logic (i.e., in the
rules LaterPureStep, LaterNew, LaterLoad, and LaterStore). In fact, this later in the
definition of the weakest precondition is responsible for the intuition: “. P means P holds
after the next step of computation”. More concretely, if one proves a weakest precondition
wp e {v. Q(v)} under the assumption . P then, after the next step of computation, the goal
becomes .wp e
0 {v. Q(v)}. We can then use the rule LaterMono to remove the later in
front of wp e
0 {v. Q(v)} and in front of . P.
```



the prefix `TC` is "typeclass" and comes from stdpp. it seems they've redefined a bunch of the basic operators in coq (eq, and, or, forall, etc) as typeclasses?




`bi` == bunched implications, which is just the logical ideas of separation logic (* operator as resource composition, -* like a "resource function" that can take resources and transform them, etc)

`si` == step-indexed, still don't entirely get the intuition behind step indexed relations, but whatever

`coPset` == set of positive binary numbers. `co` is for the idea of "cofiniteness"? a subset is `co`finite if it's `co`mplement is finite.
it looks like `coPset`s are used as the "masks"? the sets that hold ghost variable/invariant names?

`E` is generally used for masks

`Canonical` is just a command for making some typeclass instance available to coq's type inference, so it can be found automatically

`Structure` is the same as `Record`!!!!

`lb` == lower bound

`%I` means to resolve in `bi_scope`

Leibniz equality is the kind where two things are equal if all propositions that are true for one are true for the other


`|==>` is `bupd`, or basic update

`P ==∗ Q` is `(P ⊢ |==> Q)`, so P entails you can get an updatable Q, using separation logic entailment
confusingly it can also mean `(P -∗ |==> Q)` in bi_scope?

```
Class BUpd (PROP : Type) : Type := bupd : PROP → PROP.
Notation "|==> Q" := (bupd Q) : bi_scope.
Notation "P ==∗ Q" := (P ⊢ |==> Q) (only parsing) : stdpp_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q)%I : bi_scope.

Class FUpd (PROP : Type) : Type := fupd : coPset → coPset → PROP → PROP.
Notation "|={ E1 , E2 }=> Q" := (fupd E1 E2 Q) : bi_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q)%I : bi_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q) : stdpp_scope.

Notation "|={ E }=> Q" := (fupd E E Q) : bi_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q)%I : bi_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q) : stdpp_scope.
```

In general the `▷=>^ n` syntax indicates a number of steps `n` accompanying the mask update?


`wsat` is world satisfaction



in the context of ofes `dist` means distance
> The type `A -n> B` packages a function with a non-expansiveness proof

> When an OFE structure on a function type is required but the domain is discrete,
one can use the type `A -d> B`.  This has the advantage of not bundling any
proofs, i.e., this is notation for a plain Coq function type.

> When writing `(P)%I`, notations in `P` are resolved in `bi_scope`

so it looks like the suffix `I` means internal


`■ (P)` means "plainly P", meaning P holds when no resources are available

`Λ` is generally an instance of a `language`

it seems `tp` is generally a thread pool?

it seems `upd` is update
and `bupd` is basic update
and `fupd` is fancy update


It seems the suffix `G` is used to mean "in global"


the only purpose of "later" is to prevent the kinds of infinite loops that can make a logic invalid (able to prove False). it's used to define propositions like weakest preconditions that must somehow bake the idea of "the program takes a step" into their meaning

ordered families of equivalences (ofe's) are just a "convenient" (if you can call them that) way of encoding "steps" into the system. ofe's make the equivalence of some pieces of data dependent on a step index, so pieces of data might be equivalent at some indexes but not others.
but most of the time the step indexes don't matter! most actual *data types* aren't recursive or hold some concept of computational steps in them, so the "equivalences" hold for *all* step indexes!

a "cmra" or "camera" is the fully general version of a resource algebra that actually uses the idea of step-indexed equality.



just copying a chunk of `docs/resource_algebras.md`:

>
  The type of Iris propositions `iProp Σ` is parameterized by a *global* list `Σ:
  gFunctors` of resource algebras that the proof may use.  (Actually this list
  contains functors instead of resource algebras, but you only need to worry about
  that when dealing with higher-order ghost state -- see "Camera functors" below.)

  In our proofs, we always keep the `Σ` universally quantified to enable composition of proofs.
  Each proof just assumes that some particular resource algebras are contained in that global list.
  This is expressed via the `inG Σ R` typeclass, which roughly says that `R ∈ Σ`
  ("`R` is in the `G`lobal list of RAs `Σ` -- hence the `G`).



iris
  program_logic: it seems contains files related to the instantiation of iris and weakest preconditions for the general "language" concept with exprs and vals etc. I don't think I care except to look for patterns and examples

  base_logic: is all the pay dirt in here?

  bi: contains files related to bunched implications logic?
  si_logic: contains files related to step-indexed logic?

  algebra: contains files related to resource algebras?










So I'll have to define some `magmideG` typeclass and `magmideΣ` list of resource algebras and a `subG_magmideΣ` instance

`inG` asserts some resource algebra is in a list
`subG` asserts a list of resource algebras is contained in a list

> The trailing `S` here is for "singleton"

hmm

```coq
Class magmideG Σ := {
  magmide_inG: inG Σ magmideR;
  magmide_some_other_library: some_other_libraryG Σ
}.
Local Existing Instances magmide_inG.
Local Existing Instances magmide_some_other_library.
... other fields

Definition magmideΣ: gFunctors := #[GFunctor magmideR; some_other_libraryΣ].

Instance subG_magmideΣ {Σ}: subG magmideΣ Σ → magmideG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!magmideG Σ, !otherthingsG Σ}.
EndSection proof.
```

> The backtick (`` ` ``) is used to make anonymous assumptions and to automatically
generalize the `Σ`.  When adding assumptions with backtick, you should most of
the time also add a `!` in front of every assumption.  If you do not then Coq
will also automatically generalize all indices of type-classes that you are
assuming.  This can easily lead to making more assumptions than you are aware
of, and often it leads to duplicate assumptions which breaks type class
resolutions.

