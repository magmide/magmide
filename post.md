- software is important

- software generally sucks. it's unreliable, brittle, unsafe, and terrible

- if software *didn't* suck, then we could confidently use it for a lot more things, to build bigger and more ambitious things, and with less maintenance cost. wouldn't it be nice if voting machines and virtual currencies and government databases were proven to be correct?

- it doesn't have to be like this, there's this field called formal verification, and it's become very mature and has the *theoretical* tools and practices to make formal verification of *all* code possible and tractable

- the *practical* tools are kinda garbage from an engineering practice perspective (inelegant syntax, way too many features and sugars piled on the project, overly academic/obtuse naming conventions, **awful** package/module system). even though many of the recent advancements in theory enable arbitrary bit/heap manipulating programs, those techniques are trapped inside coq. coq is amazing, but since it's purely functional and doesn't have a way of "escaping" into bit/heap manipulation, it's inefficient compared to what's possible with imperative programming, and it's very difficult and annoying to integrate formally proven programs into larger projects, and it's *impossible* to write a *full* program in coq.

- I want to convince you that this dream is possible, all through a dependently typed assembly language with powerful metaprogramming capabilties that I'm calling `bedrock`. it's an extraordinarily ambitious goal, but we can slowly build up to the full dream, bootstrapping from existing tools and taking some things as a given at different stages. I also want to convince you that software engineers can understand and productively use tools this sophisticated, *especially* if we do a good job creating documentation and educational materials. the promise of the sheer power of a language like this would act as a strong motivation for individual engineers to get up the learning curve, and for the community to create a wealth of learning materials.

- first I'll describe the dream in it's final form, and then describe how we can incrementally build up to that

- by building a dependent type proof checker with embedded definitions of instructions/storage/heaps and some hardware/os axioms, the type checker could formally verify a truly useful assembly language

- and then by adding both syntactic and semantic metaprogramming commands, that assembly language could be used to slowly layer more abstractions and high level programming languages on top of the assembly language, enabling full formal verification *of the entire software stack*, all from first principles and without any assumptions between layers. and as a bonus, all of the tools and languages built in bedrock are all in principle interoperable, since they can be unpackaged into simple propositions about bit arrays and abstract instructions

- specify the actual bedrock language, the assembly language and metaprogramming capabilities, in coq
- define the bedrock representation of the syntactic structures and datatypes etc of bedrock, *in* bedrock
- define the compilation capabilities of bedrock *in* bedrock, but as a computable coq function?
- in the spirit of the `metacoq` or `coqcoqcorrect` projects, specify a new dependently typed proof checker in coq, but in bedrock datatypes
- use the compilation function to compile the first version of the bedrock compiler! this first version only outputs an llvm compatible abstract instruction set
- with this first bootstrapped version of bedrock, the work of building up everything on top of that base can begin. the definitions
