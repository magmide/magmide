so far this paper is really simple, it's just saying what proof-carrying-code (PCC) is and why it's valuable. he's also saying it would be great for these systems to not assume a particular type-system, but instead just be rooted in mathematics/logic.

VC generator: verification condition generator (akin to a tactic that examines code and infers hoare triples?)

so the first 4 sections of this paper are just talking about how we can specify the operational semantics of a physical machine and instruction set, then define program state safety and program safety in terms of the step relation given by the operational semantics. pretty simple! especially interesting is the idea of a safe *program*, which depends on the program being written in a *position independent* manner (which I suppose would mean all instructions merely reference offsets from the program counter).

see now in section 5 he's talking about *typed* intermediate representations, which is dumb! metaprogrammable recombination forever!

he's also talking about the difference between syntactic and semantic type representation. I guess the core difference is that syntactic type representation is *opaque*, the syntax rules are basically assigned axiomatically. whereas semantic ones are rooted in actual logic, so all the transformation rules can be derived from the underlying meaning of the types.

but now we're getting to "recursive contravariance?" and how it makes step-indexing necessary? I'm almost there.

Instead of saying a type is a set of values, we say it is a set of pairs `<k, v>`, where k is an approximation index and v is a value. The judgement `<k, v>` ∈ τ means, "v approximately has type τ, and any program that runs for fewer than k instructions can't tell the  difference."" The indices k allow the construction of a well founded recursion, even when modeling contravariant recursive types.

So I guess the k-indexing is just a wrapper of some kind? I think contravariant recursion is just another way of saying it has to be strictly postive in the coq sense. an inductive constructor can't accept as an argument a function that itself takes the inductive type being defined as an argument, because this allows for infinite recursion and therefore unsoundness.
