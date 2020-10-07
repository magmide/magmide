- dependent type proof checker with purely logical `prop` and `set?` types
- definition of bits and bit arrays that are given special treatment
- definition of representation of logical types by bit arrays
- prop of a "machine representable" type. since we can represent props as bit arrays, these can be represented
- some syntactic metaprogramming commands, which can take basic syntactic structures like strings or tokens or identifiers and transform them into commands or other instructions
- some semantic metaprogramming commands, which can operate on variables or identifiers or whatever to extract compile time information about them such as their type

- abstract instructions that are able to operate on bit arrays (for now we take as given that these abstract instructions can be validly encoded as bit arrays with a known size, since llvm will actually do the work of translating them for now. in the future we'll absorb what llvm does by creating a system of concrete "hardware axioms" that represent the instruction set and memory layout etc of a real machine, and a mapping from the abstract instructions to these concrete ones. in the immediate future we'll also need "operating system" axioms, at least until there are operating systems built in bedrock that can simply be linked against)
- formalization of instruction behaviors, especially control flow, locations, and allocation, and investigations into the well-foundedness of recursive locations


---

Random theorizing about syntax:

```
fn debug value;
  match known(value).type;
    struct(fields) =>
      for key in fields;
        print("#{key}: #{value[key]}")
    nat(n) => print(n)
    bool(b) => print(b)
```

---

basically this project will have a few large steps:

first we'll define some really basic proof of concept of a theory of known types. this first version will basically just use the "computable terms are a subset of terms, and we only bother to typecheck terms once we've fully reduced them to computable terms". there are a million ways to go about doing this, so we'll just keep it really simple. we'll do this in a "simply typed lambda calculus" so it's easy to reason about.

we'd probably want to demonstrate that this pattern can handle literally any meta-programming-like pattern, including:

- generics
- bounded generics
- higher-kinded generics (demonstrate a monad type?)
- macros of all kinds

probably our definition of preservation and soundness etc would be a little more nuanced. we'd probably also require the assumption that the known functions reduced "correctly", something that would depend on the situation


all computable types as simply a bit array with some predicate over that bit array. with this we can define n-ary unions, tuples, structs, the "intersection" type that simply "ands" together predicate of the two types

then we can get more interesting by having "pre" typechecks. really what we would be doing there is just trying to allow people authoring higher order "known" functions to prove their functions correct, rather than simply relying on the "this known function will eventually reduce to some terms and *those* terms will be typechecked :shrug:". Basically we want these kinds of authors to have strong typing for their things as well, in a way that goes beyond just typechecking the actual "type value" structs that they happen to be manipulating
we can think about it this way: in languages like rust, macros just input/output token streams. from a meta-programming perspective, that's like a program just operating on bytestreams at both ends. we want people to be able to type their known functions just as well as all the *actual* functions. what this can allow us to do is typecheck a program, and know *even before we've reduced certain known functions* that those known functions aren't being used appropriately in their context, and won't reduce to terms that will typecheck. in a language that's formally verified, we can then even potentially do the (very scary) potentially very performance enhancing task of *not actually bothering to typecheck the outputs of these known functions*. if we've verified the pre-conditions of the known function, and we have a proof that the known function will always output terms having some particular type, we can just take that type as a given

after we've defined the semantics of types that consist *only* of bit arrays with a predicate, we can start actually defining the language semantics. the big things are n-ary unions and match statements, module paths and the dag, type definition syntax etc. but also the very interesting and potentially massive area of figuring out how we can prove that a loop (or family of co-recursive functions) will always terminate. since this language would have a rich proof system, doing that can actually be tractable and useful from the perspective of programmers.

defining and proving correct a type inference algorithm


then we have all the cool little ideas:

- the "infecting" types of certain operations. we want infecters for code that potentially panics, diverges, accesses out of bounds memory (unsound), accesses uninitialized memory (unsafe?), or leaks any "primitive" resource (we could make this generic by having some kind of predicate that is "optional" but as a result of being optional infects the result type. so someone could write a library that has optional invariants about the caller needing to give back resources or something like that, and you can represent a program that doesn't maintain these invariants, but then your types will get infected. perhaps a more interesting way to do this is simply by understanding that any predicate over a type that *doesn't actually make any assertions about the type value's byte array* is like this?). it's probably also true that if we do this "infecting" correctly, we can notice programs where *it's certain* that some infected type consequence will happen, and we can warn programmers about it.

- a "loop" command that's different than the "while" command, in the sense that the program doesn't ask for any proof that a "loop" will always terminate, since it's assumed that it might not. we can still maybe have some finer-grained check that simply asks if a loop construct has any code after it, and if it does there has to be *some* way of breaking out of the loop (other than the process being forcefully terminated, such as by receiving some control signal), or else that code is all dead.

- with a tiny language that's so flexible, we can define and reason about a host of ergonomic sugars and optimizations.

- all the little syntax things you like, such as the "block string", the different ways of calling and chaining functions, the idea of allowing syntax transforming known functions (or "keywords") and of allowing these kinds of functions to be attached as "members" of types for maximum ergonomics and allowing things like custom "question mark" effectful operators.

- in our language we can define "stuckness" in a very different way, because even very bad things like panics or memory unsafe operations aren't *stuck*, they're just *infected*. this means that the entire range of valid machine code can be output by this language. this probably means the reasonable default return type of the `main` function of a program (the one that we will assume if they don't provide their own) should be `() | panic`, so we only assume in the common case that the program might be infected with the panic predicate but not any of the "unsoundness" ones.

- "logical" vs normal computable types. logical types would basically only be for logic and verification, and not have any actual output artifacts, which means that all the values inhabiting logical types have to be known at compile time, and we can cheat about how efficient they are to make it more convenient to write proofs about them

- wouldn't it be cool to connect proofs about this language to existing verification efforts around llvm?





for co-recursive functions: we can create graphs of dependencies between functions, and we can group them together based on how strongly connected they are. for example

here we mean that a and b both reference the other (and potentially themselves), so once we enter this group we might never leave
(a - b)

but if a and b point to some other function c, if c doesn't reference a or b (or any function that references a or b), then we'll never visit that group of a and b ever again, *but c might be co-recursive with some other family of functions*. however it's still useful in this situation to understand that we have in some important way *made progress in the recursion*.
it seems that the important idea of a co-recursive family of functions is that from any of the functions you could go through some arbitrary set of steps to reach any of the other functions.


if we unbundle both functions and the loops/conditionals into mere basic blocks like in llvm, then it's possible to do this graph analysis over the entire program in the same way. with some interesting new theories about what it means to make progress towards termination *in data* rather than *in control flow*, we can merge the two to understand and check if programs are certainly terminating.
we can also unbundle the idea of "making progress in data" to "making progress in predicates", since our types are basically only defined as predicates over bit arrays.






after all this, we really start to think about the proof checker, and how the proof aspect of the language interacts with the known functions.
the simplest thing to notice is that theorems are just known functions that transform some instantiation of a logical type (so all the values of the logical type are known at compile time) to a different type.
the more interesting thing to notice is that the same kind of really slick "tacticals" system that's included in coq can just be *fallible* functions that take props and try to produce proofs of them. this means that the "typecheck" function that the compiler actually uses when compiling code should be exposed to all functions (and therefore of course the known functions), and that it should return some kind of `Result` type. that way tacticals can just call it at will with the proofs they've been constructing, and return successfully if they find something the core typechecking algorithm is happy with.
