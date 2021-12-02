Magma has two essential components:

- Logic Magma, the dependently typed lambda calculus of constructions. This is where "imaginary" types are defined and proofs are conducted.
- Host Magma, the imperative language that actually runs on real machines.

These two components have a symbiotic relationship with one another: Logic Magma is used to define and make assertions about Host Magma, and Host Magma computationally represents and implements both Logic Magma and Host Magma itself.

```
                     represents and
                       implements
     +---------------------+-------------------+
     |                     |                   |
     |                     |                   |
     v                     |                   |
Logic Magma                +-------------> Host Magma
     |                                         ^
     |                                         |
     |                                         |
     +-----------------------------------------+
                    logically defines
                       and verifies
```

Since Host Magma is the computational language, all metaprogramming routines are written in it, including ones that are intended to produce Logic Magma terms. This means the compiler has to be built with a definition of Host Magma present so it knows how to check and run metaprograms.

Host Magma must be a runnable on the various development machines that could be used by engineers, so it needs to be highly abstract and capable of being assembled or "rendered" to many different specific architectures/environments. This means it must be similar to LLVM in terms of abstractness. However something as low-level as LLVM would be very painful to write a full production-grade compiler in, so it makes sense for Host Magma to *really* be some higher level language that's lowered to the LLVM equivalent using metaprogramming. Since Host Magma will be at the same level as LLVM, it will similarly need "backends" capable of rendering it to the concrete instruction set. We could very well choose to piggyback on LLVM for the first stage of the project! However LLVM doesn't have any verification/separation logic capabilities, and the backends themselves aren't verified to maintain IR semantics to the concrete architecture, so LLVM can't be the final goal.

Logic Magma can of course be used to define any *other* object language. So if you wanted to use Magma to verify and compile a program in some other architecture/environment, you would give that architecture/environment a full definition in Logic Magma, write your program in whatever format you choose, use Host Magma to parse and convert that format to the language's Logic Magma form so you can make assertions about it, and then use Host Magma to render the program so it can be used elsewhere.

So the final compiler must include:

- Syntax tree datatypes and a parser for whatever top-level syntax we choose. This syntax must support all of Logic Magma (inductive types, proofs, functions, theorems), whatever top-level metaprogrammatic entrypoints we choose, and whatever layer/variant of Host Magma we choose to directly support outside of metaprogrammatic entrypoints.
- Core libraries defining and exposing Host Magma. These core libraries can also include whatever other theories of logic or computation we think could be helpful for users.
- A proof checking kernel for Logic Magma programs. This must include an interpreter that can evaluate Logic Magma terms according to the [calculus of constructions reduction rules](TODO). This kernel should be verified to correspond to a trusted theory base of the calculus of constructions, heavily inspired by [Coq Coq Correct](TODO). This means that Magma won't only be self-hosting, but self-verifying.
- A build/run engine capable of running a cascade of metaprograms. This engine will accept a metaprogram AST representation and use the builtin Host Magma definition/renderer to process it into a runnable program, set up the program's inputs, jump to the rendered metaprogram in memory, collect the outputs of the program, and continue that process using the outputs of each metaprogram until a stopping point is reached. An implied part of this loop is running proof checking to verify each program, since type checking a Host Magma program is merely proof checking the various assertions made within it both by type annotations and things like `assert` statements.
- The above build/run engine must also be capable of rendering programs in any language with a full definition to the filesystem, including Host Magma.

To actually interact with Magma, I imagine using a cli with these basic commands:

- `magma check` performs proof checking. If there are any computable code blocks that make any kind of assertions (even type annotations are assertions!) then those assertions are checked. This implies the necessity to run the cascade of metaprograms, and therefore perform any side-effects performed by those metaprograms. Any commands that ask for Logic Magma to be "evaluated" (such as coq's `Compute` command) would happen at this level, since evaluation of Logic Magma is merely done in the kernel.
- `magma compile` performs `check` first, and implies the presence of *some* computational programs, and therefore a full definition for it that includes a renderer. The compiler ships with a full definition for Host Magma, so users don't have to supply a definition if that's their target. If there isn't any configured path to a computational program and its definition, an error is thrown. We could include a flag to merely exit successfully if there isn't any computational program present.
- `magma run` performs `check` and `compile` first, and so again implies a computational program and full definition. It also implies the availability of a machine capable of running the rendered artifact, either the host machine itself if the program is in or compatible with Host Magma, or some connected debuggable device. If there isn't a usable machine available, an error is thrown.

To build a self-hosting and self-verifying compiler, we need to bootstrap it from a language capable of performing both functions. For this I've chosen Coq.

Here are the steps I plan to take:

- Create the foundations of the purely abstract computational theory in Coq. This is itself a fairly large task we can break up:
  - Formalize binary values and operations. This is pretty straightforward, and has already been done in [several](https://github.com/coq-community/bits) [other](https://github.com/mit-plv/bbv) [projects](https://github.com/jasmin-lang/coqword). However since Magma intends to tie many trackable effects to binary operations such as integer overflow or division by zero, we might have to have our own implementation. We'll cross that bridge when we come to it!
  - Formalize generic abstract machine states. Essentially we need a machine state definition that is polymorphic in what cores/instruction sets, register/memory banks, and environmental system calls it has access to. This definition should be as generic as possible so it can support even software hosted environments such as what's available to webassembly.
  - Formalize a reusable theory of well-founded termination in assembly languages. Especially we want a proof obligation generator capable of finding the smallest number of control flow jumps that need special proof justification. More in [`posts/toward-termination-vcgen.md`](./posts/toward-termination-vcgen.md).
  - Integrate the above machine state theory with Iris, to create a similarly polymorphic separation logic. This will probably be the most difficult step, since Iris, while being very well designed, wasn't designed with ergonomic use by engineers in mind. We'll likely need a lot of help from the Iris core team with this step.
  - Formalize trackable effects with inspiration from Iron-style fractional tokens. This could need a custom resource algebra in order to be reusable for different types of effects, that remains to be seen.

- Define the bottom layer of Host Magma. This will be something analogous to LLVM in terms of abstractness and environment level. We might even choose to formalize a subset of LLVM itself in order to benefit from the project's maturity!

- Now comes the tricky bit! The actual bootstrapping could be accomplished several ways, depending on whether we'd prefer to:
  - write the Magma compiler *inside* Coq perhaps using notations (I don't like this option)
  - write the Magma compiler all in Magma and write a full compiler in Coq (perhaps, but involves a lot of duplicate work)
  - write the Magma compiler in its own files and use a parser/metacoq combination to ingest it into Coq (I'm leaning toward this)

- Once the first full version of the compiler is bootstrapped, we're off to the races! Then we just start down the long road of implementing:
  - Awesome educational materials.
  - Standard libraries for both Logic and Host Magma.
  - The package management system.
  - Build tooling such as the `magma` cli.

- And of course the process of improving the power, performance, usability of the language will never end.












## metacoq parser

build a simple and strict indentation based block-line oriented parser in coq/ocaml, and use it within metacoq to be able to ingest things from other files.

what this would let us do is define all the initial logic stuff in magma syntax, and just convert it into coq to leverage the existing proof checker and even tactic runners etc.




## Host Magma definition in coq

Start at the lowest level possible (probably a level equivalent to an LLVM with operating system syscalls available, probably only linux ones at first). prove as much stuff about it as necessary, probably link it with iris.

also define shorthands and sugars and predicates representing useful types and notations and higher level constructs for Host Magma, all at the coq level. this is to make it tractable to actually write programs. possibly here do some metacoq parser so you can ingest these definitions from other files or strings and such

at this stage we only have coq code

## define trusted theory base

define coq types representing Logic Magma, define the trusted theory base of the calculus of constructions (heavily reusing coqcoqcorrect) using those Logic Magma models.

still only coq

## implement Logic Magma in magma, prove in coq

define the Host Magma types and functions capable of representing and implementing Logic Magma and the calculus of constructions proof checking kernel. at the coq level ingest and prove them correct according to the above trusted theory base. if you were to render this proof checking kernel now, it would work and implicitly encode that trusted theory base without having to actually textually include it (prop types are erased!)

at this stage we have the magma implementation of Logic Magma, but we're still not capable of self-hosting. all the metaprogrammatic unfolding and computation and rendering and such is happening in coq.

## implement parser and metaprogrammatic infrastructure in magma

define Host Magma types and functions capable of representing and implementing the rest of the actual compiler design.















<!-- Now with a proof language, one can define types that model bits, binary arrays, register banks, memory banks, and therefore total machine states. Then one can define various predicates over these types, and model "computable types" by defining specific predicates. One can prove partial or total symmetries/modelings between binary arrays fulfulling certain predicates and other normal ideal types. one can define ideal types representing machine instructions, and parser/render functions that are provably inverses, and prove assertions about machine instructions and their effects on a machine state.
then you can write programs, and prove things about them.

going between ideal and computable values
if we have metaprogramming, then whenever you define an ideal type, you can access the computational representation of both the *type and any value fulfilling that type*. you can do whatever you want with this information, maybe by converting it into a value representing some other type or fulfilling some other type, possibly in a different layer of abstraction such as a computable one or props or whatever

types constrain/define values
values fulfill types
values can computationally represent types

so no type is a fixed point of itself, but a type *system* can be, if it's able to define itself.


type      type
|          |
v     |        v
value-+       value


logic types constrain/define and can make assertions about logic values
logic values fulfill logic types
logic values can

what's the difference between a bit array defined in Logic Magma but computationally represented in the smart packed format, and a real bit array? there's no difference at all, at least between a particular concrete one.
 -->

However there are some subtleties we have to contend with since Magma is so inherently intended for verification of *real* computational programs.
The kernel has to be actually *implemented* in some real computational language, and we'd prefer it was a maximally performant one. Also, metaprogramming of all kinds, whether manipulating Logic Magma terms or anything else, also has to be implemented in a real computational language. These might as well be the same language. This language needs to be one that can be run on *development* machines, the ones that will compile whatever final artifacts. Let's define the term Host Magma to refer to this aspect.

So the final compiler will be a binary artifact runnable on some collection of host architectures. This artifact will have a few components:

parser, capable of parsing Logic Magma, metaprogramming constructs, and any other constructs we choose to include in the shipped language syntax, all into Host Magma data structures.
proof checking kernel, which accepts some Host Magma data structure representing Logic Magma terms.
metaprogramming checker/runner. the compiler has builtin definitions and models of Host Magma, so it can take ast structures representing Host Magma and check them (Host Magma likely includes syntax to make assertions about state, which are implicitly predicates over binary arrays), render/assemble them to some place in memory or a file, and jump to them to execute them (possibly having provided arguments by fulfilling whatever calling convention)

use cases

## just doing logic/mathematics, not intending to create runnable programs

although it would seem this use case doesn't need to be able to check/compile/run computable programs, the user might still use metaprogramming to manipulate proofs, or use libraries that do. before sending the Logic Magma structures representing the code being worked on to the kernel, any metaprogrammatic constructs need to be unfolded, which means the Host Magma programs that are implied by those metaprogrammatic constructs need to be checked/compiled/run.

the flow for codebases like this would be: parse into data structures, check/compile/run any meta programs using the built in Host Magma algorithms, send fully unfolded Logic Magma structures to the kernel

this means that the compiler needs to have built in notions of some known Host Magma. the truly final version of Magma can have the *syntax* of some layer/variant of Host Magma built in rather than always nesting Host Magma underneath metaprogrammatic entry points

## writing code intended to run on the same architecture as the host

here all we need is the same Host Magma used within the compiler. the user doesn't have to do anything unusual, they just need to write Host Magma that's somehow "marked" as the "main" entry point

of course prop predicates can be indexed by host types/values, so Host Magma will include custom entry points/sugars for assertions about code state that assumes these indexed predicates. assertions about host values are just logical props but more specific versions of them.

so there's the *ideal* definition of a computable type, which is just a predicate about binary arrays
this ideal definition must itself be represented computationally, so in memory it will be shaped in whatever way we decide to represent inductive types (probably with some array of values with tags and index offsets to avoid having pointers to different parts of memory and improve cache locality)
then at the runtime of the target program, the real bits will just be formed according to how the predicate demanded they would be

## cross-compiling code for a different architecture, but written in Host Magma

same as above, they just have to somehow signal what architecture(s) are intended

## compiling code using a completely different compute language, one incompatible with Host Magma

in order to do this, the user has to specify ast datatypes for their language. they have to do this in Host Magma, since these datatypes need to be computationally represented and manipulated.

they can optionally choose to create macros to convert some custom syntax into these ast datatypes, and if they do this these macros will be in Host Magma.

they will almost certainly define logical specifications for their host architecture, the machine type, how their ast datatypes relate to these things, and probably (definitely?) purely imaginary logical datatypes that model the real computational ones, and all of this will be done in Logic Magma. Logic Magma terms aren't really intended to be "computed", only evaluated using the reduction rules with an interpreter inside (alongside?) the kernel.

they need to be able to render/assemble their program, and they have to provide a custom rendering function. this step is ultimately a meta one, since "compile time" refers to compilation of the target program! so compilation is really just running a metaprogram that happens to produce some artifact. looking back at the more "normal" use cases we can see that those are just the same thing, except the path at each step was more known. the only thing that really distinguishes this use case from the others is that the ast/specifications/renderer were all provided custom.

but the logical stuff is the thing that's confusing. should logic Prop types be indexable by Host datatypes?

remember, at the very bottom of all of this is just the Host Magma *logic types*. logical inductive types are at the bottom of the tree. those types are just modeling a real computational machine state and making assertions about it.
when we make assertions about "host types", we aren't making assertions about *it*, but about the machine state it represents?

it's silly to get hung up on whether Host Magma types/values can be asserted by the Prop universe, because of course they can! host types are just predicates over binary arrays, and host values are just binary arrays. to say that some host value is equal to another is the exact same as saying two ideal values are equal. in both cases they're *definitionally* equal in the strict coq convertibility sense.



the magma compiler is a program that can operate in any specific machine of a universe of machines that have been modeled at the time of the compiler being compiled. this universe of machines has been modeled with some kind of with input/output capabilities and probably some concepts of operating system services such a filesystem. so Host Magma can include functions to write to files, and can expose functions for core concepts such as rendering compilation artifacts (probably accepting custom ast/assertions/checkers/renders etc)






















# Metaprogramming system

instead of defining an extremely complicated set of macro definition rules, metaprogramming in magma chooses to give three very simple "syntactic entrypoints", and then just expose as much of the compiler query api as possible to allow for compile-time type introspection or other higher-level capabilities.

macros can either accept raw strings as input and parse them themselves (this allows for arbitrarily flexible and evolving community parsing patterns) or accept Magma parsed token trees (like most languages). to actually call them you can do so inline, as a block, or using a "virtual" import that processes an entire file

## Inline macros

inspired by Rust's explicit `!` macros and javascript template literals

raw string version:

```
macro_name`inline raw string`
```

syntax tree version

```
macro_name$(some >magma (symbols args))
```

## Block macros

uses explicit indentation to clearly indicate scope without requiring complex parsing rules

raw string version uses a "stripped indentation" syntax inspired by [scala multiline strings](https://docs.scala-lang.org/overviews/scala-book/two-notes-about-strings.html#multiline-strings), but using pure indentation instead of manual `|` characters.

```
// the |` syntax could be generally used to create multiline strings
// with the base indentation whitespace automatically stripped
let some_string = |`
  my random `string`
    with what'''
    ''' ever I want

// placing the literal directly against a path expression
// will call that expression as a raw string macro
macro_name|`
  some
    raw string
  the base indentation
  will be stripped
```

token tree version is like "custom keywords", with an "opening block" that takes two token trees for header and body, and possible contination blocks. here's an example of a "custom" if-else block being used.

```
$my_if some.conditional statement;
  the.body
  >> of my thing

/my_else; some_symbol()
```

## Import macros

allows entire files to be processed by a macro to fulfill an import command. you'll notice the syntax here is exactly the same as inline macros, but the language will detect their usage in an import statement and provide file contents and metadata automatically.

```
// raw string version
use function_name from macro_name`./some/file/path.extension`
// token tree version
use function_name from macro_name$(./some/file/path.extension)
```

---

Magma has three type universes:

- `Prop`, representing propositions (equivalent to coq `Prop`).
- `Ideal`, representing pure logical types arranged in an infinite hierarchy of universes (equivalent to coq `Set`/`Type`).
- `Data`, representing concrete computable types encodable in bits.

---

- Magma syntax rules only allow custom notation through the macro system, which ensures it is always scoped beneath a tracable and searchable name, making it much easier for new users to find explanations or definitions of custom notation.
- Magma syntax is whitespace sensitive and designed to make program structure and code formatting directly correspond.
- Magma syntax intentionally compresses different ways of expressing the same thing into the most general syntax choices, and requires the use of syntax sugars when they are available.
- Magma's import mechanisms usefully expose different kinds of definitions differently, allowing users to not ever need problematic implicit imports.
- Magma enables readable markdown documentation comments for definitions.
- Magma's builtin formatter warns about inconsistent naming and capitalization.
- Magma's core educational materials set a convention of approachability, tracability (calling out prerequisites), and clarity.

---

## progress and roadmap

the project is in a very early embryonic state right now. I'm trying to create the essential skeleton of correctness reasoning for one specific very simple abstract assembly language, and then with that skeleton make it both more detailed, more accurate, and more general. pieces of the skeleton:

- basic reasoning about "well-formedness" and safe execution. A real machine can have its program counter set to any address in memory, even ones that don't hold known or even well-formed instructions (depending on the instruction set, some possible memory contents might not even be executable). in the current basic model, programs are simply lists of well-typed instructions, and well-formedness must simply guarantee that all execution steps will keep the program counter *within the indices of that list*. this needs to be generalized to handle position independence of the program when embedded in any memory, and then define trackable effects for execution of both "known" code (as in safe and type-checked) code and "executable" code (as in [representing a valid instruction](https://en.wikipedia.org/wiki/Signal_(IPC)#SIGILL)). fully modeling execution as what it really is, a program counter accessing arbitrary portions of memory, allows us to verify the correctness of truly exotic programs, such as those that execute foreign code after checking it (this is necessary in order to verify a metaprogrammable compiler) or even that modify themselves!
- basic reasoning about termination, and a well-foundedness verification condition generator. for this we need a step relation (done), and a multi-step closure of the relation. then I intend to create a coinductive "trace" type and demonstrate it's equivalence to the multi-step relation, and prove the "execute_program" variants follow this multi-step closure. with this toolkit we can even reason about intentionally infinite programs and fully demonstrate determinism of execution and guaranteed termination




- basic reasoning about binary words, memories, and operations. It isn't good enough to simply model binary with "binary" inductive constructors, since vital correctness dimensions related to finite word sizes or memory constraints (which will be realized in the final language with trackable effects) aren't baked into the representation. we might as well model binary words as what they really are, arrays of discrete bits.

then we generalize to any environment, as in environments both with known/fixed processor/memory arrangements and those where precise machine representation is abstracted behind "allocation" operations (which includes allocation of memory and processors etc)


any instruction set can be presented, but it has to have a few things
- a determinisic step relation
- encodable in binary
- a parser/renderer pair for the ast of the instructions and a proof that they are inverses
- some kind of "exit" instruction (importantly, this can be a "fake" exit instruction presented to a sub-environment, for example an infinitely running operating system can present the same instruction set but with a fake "exit" instruction that will actually be translated to whatever series of operations are necessary to signal to the operating system the program is finished and transfer control back to it)

from all that we can probably reuse everything else (well-foundedness, well-formedness, stuckness, etc)


### phase 0, fully specifying real computation, but abstractly (crafting a firesteel)

termination verification condition generator based on strongly connected components

reasoning about intentionally infinite programs, what does it mean for an infinite program to be "correct"? productive looping, any infinite program can always be modeled as a single infinite loop with a possible state switch describing what inner function to perform, and that inner function must terminate normally. another useful property is that an infinite program is "responsive" or "yields" control in every loop, in a way that it can be stopped or pass control elsewhere, such as a program checking some os provided flag (which in some ways allows the operating system to signal a program should stop) although there are many other ways, such as an actor system always terminating and giving control back to the executor

integrating with iris, can this direct full fidelity approach fit with iris' design?

defining everything as literal bit arrays instead of some proxy

splittable effects
non-deterministic reads
termination
known code execution

abstraction over concrete machines

### phase 1, bootstrapping the magma compiler (catching a spark)

specifying calculus of constructions in coq (reusing coqcoqcorrect)

defining an abstract assembly language program that implements the proof checking kernel

building parser/renderer that can translate that assembly language program (and maybe it's higher-level forms?) into some usable machine code program, possibly reusing something like llvm but also possibly just going directly into x86? (at this point we're building an environment that acts like a "castle in the air", since the environment is merely stated axiomatically rather than directly inheriting its semantics from a verified lower-level host system)

we actually have a few different possible avenues here
- build the first version of the compiler in coq and extract to ocaml, which means we *might* have a functioning compiler sooner to use while building the self-hosting version, and we have a functional model to use while verifying the magma version. however it also means we have to implement the whole compiler twice.
- build a mere execution function in coq that interprets magma. probably really slow, not sure I like this option
- merely build a coq parser capable of ingesting the magma implementation *to verify it in coq* and then just a barebones renderer to compile it as llvm or x86

the *finished, self-hosting* compiler will have these layers:
- the axiomatic specification of the calculus of constructions (trusted theory base), written in ideal/prop magma
- the proof checker component, written in compute magma but verified using the axiomatic specification (probably useful to introduce a concept of "perfectly models" vs "models with assumptions" to link datatypes between ideal/prop magma and compute magma. for example something like a fixed width bit-word can only model numbers within certain assumptions, but enums or records or other such things can be a perfect correspondence)
- the compute theory libraries, written in ideal/prop magma but *modeling* compute magma
- the compiler component, written in compute magma *defining* the compute datatypes that *represent* magma, and verified using the compute theory libraries
- the standard library

this is really as far as the core project will likely have to go, once something is usable it will hopefully be much easier to attract outside contributions

### phase 2, build standard library and educational materials (shoring up our hearth)

figure out initial interop story with other proof assistants (interop with programs is baked into the inherent interop of assembly language, you just have to define calling/memory conventions etc on a case-by-case basis)

in this phase we aim at releasing a stable first version

### phase 3, build ergonomic tools (fashioning torches)

unified check/build/run tool
package management
syntax highlighting/language server

### phase 4, build the whole ecosystem! (lighting up the world)

---


## How does Magma work?

The logical language where proofs are conducted is in concert with the concrete language where computation is done. The computational language defines the instructions that perform type(proof)-checking and manipulate proof terms. But then proof terms justify the computational types of the concrete language, and are used to define the instructions that are then assembled into real programs.

The Magma compiler is a program, whose source is written in the Magma abstract assembly language (but of course any part of it can be *actually* written in some embedded language and then unfolded metaprogramatically to the abstract assembly language)
This program includes definitions for the basic ast of Magma. This ast is almost entirely the (path-based) module system, and all the logical stuff (coq equivalents). The abstract assembly language is then entirely defined within this logical language, and metaprogrammatically converted

So you could possibly say that the "object" language is the logical proof one, and the "meta" language is the concrete computational one. However the "object" language has an unusual link back to the "meta" language, since the meta language is defined and proven in terms of the object language.

The only things the compiler needs to function are:

- the `use` keyword
- ability to parse `use` keywords and the basic metaprogrammatic capture syntax *and nothing else*. all the other stuff can just be captured with the capture primitives and then processed with libraries. however it's silly to have that extra level of indirection for the "base" languages. the logical language and "preferred" computational language can both be "primitive" from the perspective of the parser, even if they aren't truly primitive from a logical perspective.
- libraries to perform more fine-grained parsing of the logical language and do type-checking etc.
- a backend to assemble/render instructions
- definitions of types/instructions enough to do all of those above things


The final language will have the logical subset and a rust-like high-level computational subset that aligns nicely with the logical language but is imperative and stateful.
