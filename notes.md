https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf
https://gitlab.mpi-sws.org/iris/tutorial-popl21
https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/heap_lang.md
https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/proof_mode.md




I like the idea of having a `by` operator that can be used to justify passing a variable as some type with the accompanying proof script. so for example you could say `return x by crush`, or more complicated things such as `return x by (something; something)`
a small and easy to use operator for embedding the proof language into the computational language would probably go a long way to making Rok popular and easy to understand.


look at koka lang
what rok can add is *unannotated* effects. polymorphic effects in a language like koka seem (at first glance) to require annotation, whereas in rok they are simply implied by the `&` combination of assertions that is inherent to what a type is.


The term "gradual verification" is useful to sell people on what's unique about this project. Rok is tractable for the same reasons something like typescript or mypy is tractable.




An exciting idea, of having the "language" be generic over a *machine*, which includes possibly none or many register (a bit array of known length) or memory location (also a bit array of known length, which accounts for architecture alignment) banks (a possibly infinite list), and a concrete instruction set. Then we can understand the "language" to just be a set of common tools and rules for describing machines.

Some nice things follow from this:

- "artifical" machines such as those supported by a runtime of some sort are easily described
- machines can have multiple register and memory banks of different sizes, and dependent types could allow us to have different access rules or restrictions or semantics for them each. metaprogramming can "unbundle" these banks into simple names if that makes sense.
- it becomes pretty simple to check if a machine is "abstract" or "concrete", by determining if all the sizes of register/memory banks are known or unknown (or possibly the correct thing is finite vs infinite?). with that information we can add alerts or something if the memory allocation function of an abstract machine isn't somehow fallible (in a concrete machine, failure to allocate is actually just a program failure! it has a more concrete meaning of having too much data of a specific kind. this concrete semantic failure in a concrete machine is what "bubbles up" to create an infinite but fallible allocation instruction in an abstract machine)






I'm starting to think that what I'm really designing is more a *logic* for typed assembly languages. it's not *quite* like llvm precisely, because to really correctly compile to each individual instruction set, those instruction sets have to be fully specified!
it seems I'm more moving toward a general logic with a *toolbox* of abstract instruction semantics, each of which can be tied concretely to actual applications. but the full instruction set of any architecture can be specified in full.
it really does point toward having a few different "families" of programs:

- embedded programs, in which the exact specifications are known up front
- os programs? ones here the instruction set can be known but things like memory sizes aren't?
- runtime programs, ones where some existing environment is already provided, often allowing looser assumptions

probably what we want is a "general core" of instructions we assume every machine has some equivalent for, which we can build the more "higher level" languages on top of. then to write a "backend" someone would fully specify the instruction set and tie the real instructions to the general core ones, at least if they wanted to be able to support the higher level languages








https://www.ralfj.de/blog/2020/12/14/provenance.html
john regehr office hours



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
lexicographic ordering of stack arguments ["Proving termination"](http://www.fstar-lang.org/tutorial/).

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




---


read introduction to separation logic

the biggest way to make things more convenient for people is to have the *certified decision procedures* described by CPDT in the form of the type checking functions!!! that means that certain macros or subportions of the language that fit into some decidable type system can just have their type checking function proven and provided as the proof object!


rather than have many layers of "typed" compilers each emitting the language of the one below it as described in the foundational proof carrying code paper, we simply have *one* very base low level language with arbitrarily powerful metaprogramming and proof abilities! we can create the higher level compilers as embedded constructs in the low level language. we're building *up* instead of *down*.


https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/cs818A3-11.html
(here now: 3.12 More about Annotated Specifications)
https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/ch3.pdf

https://en.wikipedia.org/wiki/Bunched_logic
http://www.lsv.fr/~demri/OHearnPym99.pdf

https://arxiv.org/pdf/1903.00982.pdf
https://aaronweiss.us/pubs/popl19-src-oxide-slides.pdf

the real genius of rust is education! people can understand separation logic and formal verification if we teach them well!

a basic theory of binary-representable types would also of course be incredibly useful here.
it seems that carbon could be specified completely by defining the simple `bit` type, and the basic tuple/record, union, and intersection combinators (it seems that intersection types can/should only be used between named records, and to add arbitrary logical propositions to types? it might make sense to only use intersection (as in `&`) for propositions, and have special `merge` and `concat` etc type transformer known functions to do the other kinds of operations people typically think of as being "intersection". then `&` is simple and well-defined and can be used to put any propositions together? it might also function nicely as the syntactic form for declaring propositions, instead of `must`, so `type Nat = int & >= 0`)

logical propositions are so powerful that they could be the entire mode of specifying the base types! booleans are just a `byte` or whatever with props asserting that it can only hold certain values. traits are just props asserting that there exists an implementation in scope satisfying some shape. and of course arbitrary logical stuff can be done, including separation logic/ghost state type things.

a reason to include the same kind of constructive inductive propositions is because it provides two ways of attacking

a theory of "known" types that allows known functions to produce data structures representing these types is probably the most important first step. it seems you could prove that known types are general enough to provide the language with generics, all kinds of macros, and then dramatically expands the reach of usual static type systems by providing "type functions", which allow arbitrary derivations (you can easily do rust derived traits) and mapping, which allows for the kind of expressivity that typescript mapped and conditional types allows

a general truth to remember about the goals of carbon is to remember what really made rust successful. it didn't shy away from complexity, and it didn't water down what people were capable of achieving, but it did find clean abstractions for complex things, and *especially* it did an amazing job **teaching** people how those concepts work. an amazing next generation language is equal parts good language/abstraction design and pedagogy. if you give people a huge amount of power to build incredible things, *and* you do an excellent job teaching them both how to use and why they should use it, then you've got an amazing project on your hands.

also very important, and something that the academics have *miserably* failed to do (in addition to their language design and the teaching materials, both of which are usually absolutely dreadful), is building the *tooling* for the language. the tools (think `cargo`) and community infrastructure (think the crates system) are probably *more* important on average for the success of a language community than the language itself. people won't use even the most powerful language if it's an absolute godawful chore to accomplish even the smallest thing with it

another thing the academics don't realize and do wrong (especially in coq) is just their conventions for naming things! in Coq basic commands like `Theorem` are both inconveniently capitalized and fully spelled out, but important variable names that could hint to us about the semantic content of a variable are given one letter names! that's completely backwards from a usability standpoint, since commands are something we see constantly, can look up in a single manual, and can have syntax highlighters give us context for; whereas variable names are specific to a project or a function/type/proof. shortening `Theorem` to `th` is perfectly acceptable, and lets us cut down on syntax in a reasonable place so we aren't tempted to do so in unreasonable places. `forall` could/should be shortened to something like `fa` or even a single character like `@`. `@(x: X, y: Y)` could be the "forall tuple", equivalent to `forall (x: X) (y: Y)`

## building a proof checker!
https://cstheory.stackexchange.com/questions/5836/how-would-i-go-about-learning-the-underlying-theory-of-the-coq-proof-assistant
https://www.irif.fr/~sozeau/research/publications/drafts/Coq_Coq_Correct.pdf
https://github.com/coq/coq/tree/master/kernel

you should almost certainly do everything you can to understand how coq works at a basic level, and read some of the very earliest papers on proof checkers/assistants to understand their actual machinery. hopefully the very basics are simple, and most of the work is defining theories etc on top. hopefully the footprint of the actual checker is tiny, and it's the standard libraries and proof tactics and such that really create most of the weight

theory of known types
carbon (and various projects in carbon) (when thinking about the compiler and checking refinement/dependent types, it probably makes sense to use an SMT solver for only the parts that you can't come up with a solid algorithm for, like the basic type checking, or to only fall back on it when some simple naive algorithm fails to either prove or disprove)

https://www.cs.princeton.edu/~appel/papers/fpcc.pdf
https://www.google.com/books/edition/Program_Logics_for_Certified_Compilers/ABkmAwAAQBAJ?hl=en&gbpv=1&printsec=frontcover

https://www3.cs.stonybrook.edu/~bender/newpub/2015-BenderFiGi-SICOMP-topsort.pdf


https://hal.inria.fr/hal-01094195/document
https://coq.github.io/doc/V8.9.1/refman/language/cic.html
https://ncatlab.org/nlab/show/calculus+of+constructions
https://link.springer.com/content/pdf/10.1007%2F978-0-387-09680-3_24.pdf ????


https://softwarefoundations.cis.upenn.edu/lf-current/ProofObjects.html
has a little portion about type-checking and the trusted base, reassuring



"Given a type T, the type Πx : T, B will represent the type of dependent
functions which given a term t : T computes a term of type B[t/x] corresponding to proofs of
the logical proposition ∀x : T, B. Because types represent logical propositions, the language will
contain empty types corresponding to unprovable propositions.
Notations. We shall freely use the notation ∀x : A, B instead of Πx : A, B when B represents
a proposition."

theorems are just *dependently* typed functions! this means there's a nice "warning" when people construct propositions that don't use their universally quantified arguments, the propositions are vacuous or trivial and don't prove anything about the input.



a big reason unit tests are actually more annoying and slower in development is the need for fixture data! coming up with either some set of examples, or some fixture dataset, or some model that can generate random data in the right shape is itself a large amount of work that doesn't necessarily complement the actual problem at hand. however proving theorems about your implementation is completely complementary, the proofs lock together with the implementation exactly, and you can prove your whole program correct without ever running it! once someone's skilled with the tool, that workflow is massively efficient, since they never have to leave the "code/typecheck" loop.
also, proof automation is actually *much more general and easier* than automation of testing. with testing, you need to be able to generate arbitrarily specific models and have checking functions *that aren't the same as the unit under test*. doing that is a huge duplication of effort.



probably ought to learn about effect systems as well

an infecting proposition for a blocking operation in an async context is a good idea



https://www.cs.cmu.edu/~rwh/papers/dtal/icfp01.pdf
http://www.ats-lang.org/
looking at dml and xanadu might be good

a very plausible reason that projects like dependently-typed-assembly-language and xanadu and ats haven't worked, is that smart separation logic wasn't there yet, and those languages didn't have powerful enough metaprogramming!

in bedrock, the actual *language* can literally just be a powerful dependently typed assembly language along with the arbitrarily powerful meta-programming allowed by known types and some cool "keyword"-like primitives, but then the *programmer facing* language can have structs and functions and all the nice things we're used to but all defined with the meta-programming! the meta-programming is the thing that really allows us to package the hyper-powerful and granular dependent type system into a format that is still usable and can achieve mass adoption. in this way we can kinda call this language "machine scheme/lisp".


a mistake everyone's been making when integrating dependant/refinement types into "practical" languages is requiring that only first order logic be used, and therefore that the constraints are *always* automatically solvable. We can still keep those easy forms around just by checking if they're applicable and then using them, but some people need/want more power and we should just give it to them! they'll be on their own to provide proofs, but that's fine!
we're really making this tradeoff: would we rather have a bunch of languages that are easy to use but lack a bunch of power that makes us routinely create unsafe programs, or occasionally encounter a problem that's a huge pain in the ass to formalize correctness but we're still capable of doing so? I think we definitely want the second! And we can make abstractions to allow us to work in the first area for a subset of easily-shaped problems but still directly have "escape hatches" to the more powerful layer underneath. a full proof checker in a language gives us the exciting option to always include in our meta languages a direct escape hatch right down into the full language!




as a future thing, the whole system can be generic over some set of "hardware axioms" (the memory locations and instructions that are intrinsic to an architecture), along with functions describing how to map the "universal" instructions and operations into the hardware instructions. an "incomplete" mapping could be provided, and compiling programs that included unmapped universal instructions would result in a compiler error






this is interesting, he's making a lot of the same arguments I am
https://media.ccc.de/v/34c3-9105-coming_soon_machine-checked_mathematical_proofs_in_everyday_software_and_hardware_development
https://github.com/mit-plv/bedrock2

http://adam.chlipala.net/frap/frap_book.pdf


email to adamc@csail.mit.edu:
I want to help bring formal methods to the mainstream, by learning from Rust



`bedrock`
write `bedrock` post, with lots of specific technical examples
create unproven functions implementing basic mutating assembly language in coq, using naturals instead of bit sequences
figure out how to use iris enough to implement some basic allocation examples
figure out how to use iron enough to implement allocation and deallocation

blog post series discussing the failure of untyped languages/software engineers and the dream of a common formal language
read basic category theory for computer scientists
