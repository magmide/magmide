An affine logic seems to only mean that the logic includes the weakening rule: `P * Q -> P`, you can *throw away* knowledge/resources

Resources algebras seem to be the important thing.

A resource algebra is a tuple


(M, V : M → Prop, |−| : M → M ? , (·) : M × M → M)

rules:

RA-associative: forall a, b, c. (a · b) · c = a · (b · c)
it doesn't matter what order the composition operator is used in

RA-commutative: forall a, b. a · b = b · a
it doesn't matter what order the variables are composed in

RA-core-composition-identity: forall a. |a|: M ⇒ |a| · a = a
if the core of a value is in the type, then composing the core with the same value is the same as the original value

RA-core-idempotent: forall a. |a|: M ⇒ ||a|| = |a|
if the core of a value is in the type, then the core of the core is the same as the core
(this also implies the core of the core composed with the original value is the same as the original value)

RA-core-monotonic: forall a, b. |a|: M ∧ a << b ⇒ |b|: M ∧ |a| << |b|
not sure yet

M? := M union {False}
M? basically is just the set of type invariants extended with contradiction

M? · False <-> False · M? <-> M?
composition with False is commutative and identical with M?

a << b := exists c: M. b = a · c
a is "less than", or "extended by" by
some c exists that "fill the gap" between a and b in terms of composition

a --> B := forall c?: M?. V(a · c?) -> exists b: B. V(b · c?)
a --> b := a --> {b}


a unital resource algebra (uRA) is a resource algebra M with an element ep satisfying these propositions:

V(ep)
ep is valid

forall a: M. ep · a = a
ep can be composed with anything without changing the original thing

|ep| = ep
the duplication of ep is the same as ep


a frame-preserving update is an update from some resource a to some resource b, such that if a is compatible (according to the V function) with all c?: M?, then b is also compatible with all c?
this essentially means that you can only update resources to a different state if you both already have valid resources and the updated state will be valid.



the core function |−| is basically the *duplication* function. it can be partial when some variants of a type aren't duplicable

The validity function V: M -> Prop basically defines what variants of the type are valid or acceptable

the composition function · defines what happens when you combine resources from different threads, or maybe more correctly it's equivalent to the separating conjunction `*` from separation logic


ghost state view shifts are *consuming*, to update `P ==>_ep Q` you have to update the state, or consume or destroy P. normal propositions `A -> B` are *constructive*, and wands

a mask on a hoare triple is like a set or map keeping track of which invariants are in force. accessing an invariant removes that invariant's *namespace* from the mask.



