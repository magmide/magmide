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
means every value u of type U in any world w also has type T in w this seems equivalent to saying U is a subtype of T.

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
It seems this just means the later is meaningless, *or that there's nothing in the prop that depends on the world*.

> In this section we will interpret worlds as characterizing abstract properties of the current state of computation. In particular, in a  system with mutable references, each world contains a memory typing

In different types of machines, a "world" is a different thing (a lambda calculus with a store is a pair of an expression and that store, a von Neumann machine is the pair of registers (including program pointer) and memory)

```
Clearly, the same value v may or may not have type T depending on the world w, that is, depending on the data structures in memory that v points to. Accordingly, we call a pair (w, v) a configuration (abbreviated "config"):

Config = W x V,

and define a type T ∈ Type as a set of configurations. Then,

(w, v) ∈ T
and
w |- v : T

are two alternative notations expressing the same fact.
```

> We will show how our semantics connects the relation R between worlds and the relation >-> between states.

I guess they're saying there's some sort of correspondence between the R relation showing how "worlds" are accessible in time from one-another and the small step relation `>->` that shows how computation states are accessible from one-another. This makes sense since worlds and states are the same thing.


So a type is just a set of configurations, or a set of values pointing to something in some world. This is basically saying that a type is all values *who exist in a world* that makes the type assertions true. Yeah, they say "a type is just any set of configurations"
basic stuff like the top/bottom types, "logical" intersection/union, and function types are pretty easy to describe then.

I'll put the first few in my own words:

top := {(w, v) | True}
the top type describes all configs! so it is a subtype of all configs

bot := {}
the bot type is the empty set, so it describes no configs, so it is unrepresentable

T /\ U := T intersection U
type and set intersection are equivalent, since the intersection of type T and U is only the types that are described by both conditions

T \/ U := T union U
similar idea, we smush together the types which means any config describe by either of them is valid
related, discriminated unions then are the union of types which have no intersection, or where the description of each type necessarily precludes the other

U => T := {(w, v) | (w, v) ∈ U => (w, v) ∈ T }
this is slightly more involved, but only because I'm not sure if he's talking about implication or functions. I'm going to guess implication, since there's no talk of substitution or anything like that
all configs such that if the config is in U, it is also in T


Now he gets into how quantification is represented in the type system. These are more interesting.
importantly, in the below, A can be either Type, Loc, or Mem.

forall x:A.T := global_intersection<a in A>(T[a/x])
okay, first parsing it:
forall x which is an A, then T is defined as
the global intersection of all items a in A, for each which we've subsituted the a in the set which our variable x
that basically means that forall is the intersection set of all configs (or locs or mems) where...
I'm not sure I get it yet. the exists below is similar just with union, so I'll wait until later to understand what's going on. hopefully he gives an applied example.

exists x:A.T := global_union<a in A>(T[a/x])

Quantification over values in a world.
pretty simple,

!T := {(w, v) | forall v'. (w, v') in T}
all values in the current world have type T

?T := {(w, v) | exists v'. (w, v') in T}
some value in the current world has type T


Then they brag how they can define types in terms of their primitives without using the underlying logic.

T <=> U = T => U /\ U => T
T iff U, pretty simple (this confirms my suspicion that => was meant to indicate implication, although implication is isomorphic with functions, so there's something there as well)

teq(T, U) = !(T <=> U)
basically type equality, since for all values in (the current world) the types are equivalent to each other
the dependence on the current world is the only part I don't love....

world types (which teq(T, U) is one of) are types that only depend on the world, not the value (I'm guessing persistent types are ones that depend on neither)



Okay Vector Values is where I got kind of stuck before, let's write things out as we go to keep it clear.

```
we have locations `l: Loc`, that index a mutable store m;
storable values `u: SV` that are the range of m (contents of memory cells);
and values `v: V`.

We assume Loc subset SV (meaning locations are storable values, but there are more storable values than just locations)

On a von Neumann machine, SV = Loc (so locations *do* in fact fully describe storable values)
and v is a vector of locations (one could think of a register-bank) indexed by a natural number j.
That is, if v is a value, then v(j) is a Loc. (meaning a "value" is a terrible name for what they're talking about! value is a register bank, so v(j. but they're using value in the config sense of a (w, v), or a world and a *value*. this means they're saying the world is the state of memory and the value is the state of the registers, at least on a von Neumann machine) is choosing a particular register to grab a Loc from. Magmide will make this clearer by just making all things byte arrays and lists of byte arrays)
```

This part is where is gets hairier:

```
In order to type locations, we choose an injective function (a function that is one-to-one) `.->` from storable values to values (ints to register banks), for instance
`u-> := lambda j. u`
This way the same set of types can be used for all kinds of values.
```

The "in order to type locations" is important. I'm hoping this will become more clear. I understand all the parts of that sentence, but not the purpose of the sentence.

I think it becomes clearer with the "This way the same set of types can be used for all kinds of values." They're talking about *world/value/config* values in this context, so I guess this injective function is trying to produce some kind of equivalence between von Neumann machines and lambda calculus.

This is even less clear

```
In lambda-calculus, `SV = V` is the usual set of values, so we have `Loc strictsubset SV` by syntactic inclusion, and we take `u-> := u`
```

again I understand the parts but not the sentence.
perhaps they're saying that in lambda calculus the store can hold anything, and the "value" of a von Neumann machine is the current expression being reduced, so there isn't a need for this injective function? I'm still not sure what the injective function is for.


Singletons and slots.

I don't want to get stuck on this stuff.

based on this definition of the single type `just u` (the single storable value (SV) u)

just u := {(w, v) | v = u->}

I'm going to choose to believe that the injective arrow function is just saying that the value (register bank) v *can possibly produce u*????

and then

u: T = !(just u => T)
: here means "has type" in the more traditional sense
so for all values in the current world, if the value is u, then it has type T


exists l: Loc. just l /\ w(l)


Okay this makes more sense:

The type `slot(j, T)` characterizes values v such that the jth slot has type T.

slot(j, T) := {(w, v) | w ||- v(j): T}
all configs such that in the current world the storable value at slot j has type T

I think all this stuff was simpler than they made it seem, by this sentence:

> To say that register 2 has the value 3 we write slot(2, just 3).


Now on to the important stuff,

## Necessity and the modal operator "later"

Given two types U and T, we write
U |- T
when the type U is a subset of the type T, meaning
for every world w and value v,

w ||- v: U
implies
w ||- v: T

(if a value is a U, then it is also a T, so Us can be replaced with Ts, U is a subtype of T)

We write
|- T
to mean
top |- T
(so we don't assume any (useful) types are subsets of T, only the top type, which is a subtype of all types)


The accessibility relation R has to be transitive and well-founded, such as the less-than (<) relation.

So R(w, w') means the world w' comes at a strictly later stage than the world w.

From this we can define the later operator:

later(T) := {(w, v) | forall w'. R(w, w') => (w', v) in T}
so for all worlds strictly later than now (so w < w', or the step-index of w is less than w')
so v has type later(T) when v has type T in all worlds strictly later than now (the world w)

Some stuff can be proven about later,

it's monotone (if U is a subtype of T, then later(U) is a subtype of later(T))
it distributes over intersection:
  `later(global_intersection(Ti)) = global_intersection(later(Ti))`

now the necessity operator (the box), `nec`
`nec` means now and later, and is defined simply:

nec(T) = T /\ later(T)

also monotone,
forall T, nec(T) subtype of T
if nec(U) subtype T, then nec(U) subtype nec(T)
also distributes over intersection


necessary types
types that, once true in some world w, are true forever.

necessary(T) = T subtype later(T)
so if T is true then also later(T)
or T is a subtype of later(T)
or T can be used as later(T)

this won't always be true, since the store evolves from one world to the next, possibly destroying some type

forall T, necessary(nec(T))
since nec(T) simply contains lat(T) so we can grab it

forall T, necessary(lat(T))


The lob rule
since R is well-founded, this induction principle is true:

```
later(T) judges T
------------------
    judges T
```



Recursive types

I'm not going to go over this in detail.
Basically, let's say we have a *type* operator F, which maps types to types.
such an operator is contractive if



A Kripke semantics of stores


I think this sentence is what makes the later operator make sense:

In this definition we write `later(m(l): T)`. There is some value u in memory at address l, and we guarantee to every future world that `u: T`. We don’t need to guarantee `u: T` in the current world because it takes one step just to dereference `m(l)`, and in that step we move to a future world.
This use of the later operator rather than the nec operator is crucial in order to solve the cardinality issue. Indeed, for a
configuration ((n, Ψ), v), only the configurations of index
strictly less than n are then relevant in the type Ψ(l).

So basically types can only refer to themselves because the assertions on memory locations only apply to future states.
All types can only refer (at least in regards to memory) to worlds later than the current.

this especially applies to reference types, since by necessity accessing the value requires a step of computation, so `ref T` just means that some location has type T *later*.




Oh my god, they say in section 11 that a type T describes *the entire register bank*. it's the type of the whole machine! since reference types are attached to the locations stored in the "value" (the register bank), we can assert the state of memory just by the type of the register bank.
we can type stack arguments by making assertions about the state of memory around the stack pointer.

A minimal machine could get by with just a program counter and memory, since even the return address can be put in stack arguments in memory


This paper hasn't heard of separation logic or something ha. They keep saying they have to specify that other registers aren't changed. no thanks.


This paper still doesn't explain why *props* have to have step-indexing when they are self-referencing!!


I get it all, at least at a high level, but I'm unsatisfied. maybe cpdt will help.

## cpdt because I said so (Universes)

> A predicative system enforces the constraint that, when an object is defined using some sort of quantifier, none of the quantifiers may ever be instantiated with the object itself.

an object can be passed itself as an argument.
but what counts as "itself"?
I guess Prop gets around this by not taking *itself*, but *instances* of itself
okay all he really says is that since Prop is always eliminated at extraction, and therefore doesn't produce infinite regressions allowing infinite loops to prove anything, it doesn't matter if it's impredicative.

so why can't iris use them directly!!!???
