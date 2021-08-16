https://gitlab.mpi-sws.org/iris/examples/-/tree/master/theories/lecture_notes

iris invariants let different threads read/write to the same locations, as long as they don't violate the invariant
iris ghost state lets invariants evolve over time, and keep track of information that doesn't exist in the actual program

# lambda,ref,conc

> A configuration consists of a heap and a thread pool, and a thread pool is a mapping from thread identifiers (natural numbers) to expressions, i.e., a finite set of named threads. Note that reduction of configuations is nondeterministic: we may choose to reduce in any thread in the thread pool. This reflects that we are modelling a kind of preemptive concurrent system.

> In the case of Iris the underlying language of “things” is simple type theory with a number of basic constants. These basic constants are given by the signature S.

This signature concept is probably going to be important.


> The types of Iris are built up from the following grammar, where T stands for additional base types which we will add later, Val and Exp are types of values and expressions in the language, and Prop is the type of Iris propositions.

τ ::= T | Z | Val | Exp | Prop | 1 | τ + τ | τ × τ | τ → τ

1 is basically just shorthand for unit? I guess?

> The judgments take the form Γ |-S t: τ and express when a term t has type τ in context Γ , given signature S. The variable context Γ assigns types to variables of the logic. It is a list of pairs of a variable x and a type τ such that all the variables are distinct. We write contexts in the usual way, e.g., x1: τ 1 , x2: τ 2 is a context.


> The magic wand P −∗ Q is akin to the difference of resources in Q and those in P : it is the set of all those resources which when combined with any resource in P are in Q



Then they go on for a long time discussing pretty obvious rules that I already understand (basic logic, separation logic, basic lambda calculus stuff).
