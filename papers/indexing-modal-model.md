Before getting into the real paper, I'm going to quickly try to gain some clue about what modal logic and kripke semantics are, why they're useful, and how they might relate to step-indexing.

# https://plato.stanford.edu/entries/logic-modal/
In general, modal logic is a logic where the truth of a statement is "qualified", using some "mode" like "necessarily" or "possibly"

There's a weak logic called `K` (after Saul Kripke) that includes ~, -> as usual, but also the `nec` operator for "necessarily". (written with the annoying box symbol □)

`K` is just normal propositional logic with these rules added relating to the `nec`

Necessitation Rule: If A is a theorem of K, then so is `nec(A)`.

Distribution Axiom: `nec(A -> B) -> (nec(A) -> nec(B))`.

Then there's the `may` operator (for "possibly" or "maybe", written with the annoying diamond symbol ◊).
It can be defined from `nec` by letting `may(A) = ~nec(~A)`, or "not necessarily not A". This means `nec` and `may` mirror each other in the same way `forall` and `exists` do.

Uh oh, there's a whole family of modal logics based on which axioms of "simplification" they include? They're saying which ones make sense depends on what area you're working in. I'm sure this will lead to fun situations in step-indexing.

The important part! **Possible Worlds**

Every proposition is given a truth value *in every possible world*, and different worlds might have different "truthiness".

`v(p, w)` means that for some valuation `v`, propositional variable `p` is true in world `w`.

~ := `v(∼A, w) = True <-> v(A, w) = False`
-> := `v(A -> B, w) = True <-> v(A, w) = False or v(B, w) = True`
theorem 5 := `v(□A, w) = True <-> forall w': W, v(A, w') = True`
^^^^^^^^^
theorem 5 is important! it seems this is the thing that makes it all make sense.
since `nec` and `may` are equivalent to "all" and "some" when thinking about possible worlds, theorem 5 implies that `may` is similar to `exists`, `◊A = ∼□∼A`
`may` is true when the proposition is true in *some* worlds, but not necessarily all of them, or that we merely know that A isn't necessarily false *everywhere*.

Ah yeah hold on, theorem 5 isn't always reasonable for every kind of modal logic. in temporal logic, where a "world" is really just an "instant" (hint, this is almost certainly what we're dealing with in step-indexing), `nec` really means that something will *continue* to be true into the future, but may not have been in the past.

in these cases, we have to define some relation R to define "earlier than"

theorem K := `v(□A, w) = True <-> forall w', (R(w, w') -> v(A, w')) = True`

so essentially A is necessarily true in w if and only if forall worlds *that are later than w* A is still true

so then a kripke frame `<W, R>` is a pair of a set of worlds W and a relation R.

I'm skipping over a bunch of stuff that doesn't seem relevant for getting to step-indexing.

Okay bisimulation is a place where this is useful.
labeled transition systems (LTSs) represent computation pathways between different machine states.
An easily understood quote:

```
LTSs are generalizations of Kripke frames, consisting of a set W of states, and a collection of i-accessibility relations Ri, one for each computer process i. Intuitively, Ri(w, w') holds exactly when w' is a state that results from applying the process i to state w.
```

The last important thing I'll say: the properties (such as transitivity, or being a total preorder) of the *accessibility relation* R (it defines accessibility!) define what axioms are reasonable to use in some context.

# moving onto the paper!
https://www.irif.fr/~vouillon//smot/Proofs.html

okay they're just talking about what they're trying to achieve, especially how we need recursive and quantified types (quantifed means that they may be generic or unknown, as is the case with something like `forall t: T`, where t is quantified) in order to represent tree structures in memory and other such things. types need to allow impredicativity, so types can refer to themselves

they talk a little about the difference between syntactic and semantic interpretations. The way I choose to understand this distinction is that syntactic rules can only refer to themselves and can't derive value from other systems, whereas semantic ones are merely embedded in some larger logical system that itself can be used to extend the rules.

This seems to point to an important distinction I've been missing:

```
We start from the idea of approximation
which pervades all the semantic research in the area. If we
type-check v : τ in order to guarantee safety of just the
next k computation steps, we need only a k-approximation
of the typing-judgment v : τ .
```

The important part is *next* k computation steps. It seems this implies that the type judgment maybe become false *after* k. This isn't how I was thinking about it, which was that the judgment *will become* true in k steps. The less-than relationship to k makes a lot more sense with this interpretation.

This also seems important:

```
We express this idea here using a Kripke semantics whose possible-worlds accessibility
relation R is well-founded: every path from a world w into
the future must terminate. In this work, worlds characterize
abstract computation states, giving an upper bound on the
number of future computations steps and constraining the
contents of memory.
```

I'm a little scared about the implications of this "every path must terminate" thing. I'm hoping that doesn't mean we can't prove things about possibly non-terminating programs (maybe we could define infinite divergence as a terminating "world"?). Nope! They specify in a later section of the paper that we can still use this idea to prove things about *any finite prefix* of any program.

I'll write down some of their base rules to help me remember:

w ||- v: T
means v has type T in world w

U |- T
means every value u of type U in any world w also has type T in w

Then the modal operator "later"!
`lat` quantifies over all worlds (all times) *strictly in the future*

they point out that `nec` instead applies to *now* as well as the future. I guess this contradicts my intuition that the "less than k" steps thing is meaningful here

More seemingly important stuff

```
Indeed, the combination of a well-founded R with a strict modal operator `lat` provides a clean induction principle to the logic, called the Löb rule,

lat(T) |- T
-----------
    |- T
```

So if it is true that if a prop is True later then it is also true always, then it is always true always.
It seems this just means the later is meaningless, or that there's nothing in the prop that depends on the world.

> In this section we will interpret worlds as characterizing abstract properties of the current state of computation. In particular, in a  system with mutable references, each world contains a memory typing

In different types of machines, a "world" is a different thing (a lambda calculus with a store is a pair of an expression and that store, a von neumann machine is the pair of registers (including program pointer) and memory)

```
Clearly, the same value v may or may not have type T depending on the world w, that is, depending on the data structures in memory that v points to. Accordingly, we call a pair (w, v) a configuration (abbreviated "config"):

Config = W x V,

and define a type T ∈ Type as a set of configurations. Then,

(w, v) ∈ T
and
w |- v : T

are two alternative notations expressing the same fact.
```

So a type is just a set of configurations, or a set of values pointing to something in some world. This is basically saying that a type is all values *who exist in a world* that makes the type assertions true.
basic stuff like the top/bottom types, "logical" intersection/union, and function types are pretty easy to describe then.

```
forall x:A.T := global_intersection<a in A>(T[a/x])

exists x:A.T := global_union<a in A>(T[a/x])
```

These are harder to understand. the `a/x` is a replaced by x. I guess we're thinking about forall and exists as functions? which makes sense based on the curry-howard correspondence?

<!-- although I'm stopping in the middle of section 3, I ought to start there again -->
