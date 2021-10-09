# The technical design of Rok.

This post describes the design of Rok *as if it were finished*, with the intent of clearly defining the path forward and soliciting feedback. It doesn't try to persuade you this is the right design, merely describe the design in detail. It's intended for people who already understand formal verification, especially in the Coq proof assistant. If you'd like to be able to understand and contribute to this project at its current stage, you ought to read [software foundations](), [certified programming with dependent types](), [introduction to separation logic](), and the [iris from the ground up]() paper. You probably also ought to understand basic computer hardware/architecture design and assembly languages.

"Progress and Roadmap" describes what has already been done and the plan forward.

## Project goals and values

The design of the project is directly informed by its values and ambitions. Rok a metaprogrammable dependently typed language based on the calculus of constructions with an integrated abstract assembly language with trackable effects. Its goal is to enable formalization/verification/compilation of any software for any environment, therefore (*finally*) making formal verification mainstream and normal. The project doesn't have any direct goals to do cutting edge research work or advance the state of the art, but merely to combine existing research into a usable tool.

To achieve that goal the project has these values:

- **Correctness**: this project should be a flexible toolkit capable of verifying and compiling any software for any architecture or environment. It should make it as easy as possible to model the abstractions presented by any hardware or host system with full and complete fidelity.
- **Clarity**: this project should be accessible to as many people as possible, because it doesn't matter how powerful a tool is if no one can understand it. To guide us in this pursuit we have a few maxims: speak plainly and don't use jargon when simpler words could be just as precise; don't use a term unless you've given some path for the reader to understand it either by using a traceable definition or for prerequisites pointing readers toward them; assume your reader is capable but busy; use fully descriptive words, not vague abbreviations and symbols.
- **Practicality**: a tool must be usable, both in terms of the demands it makes and its design. This tool is intended to be used by busy people building real things with real stakes.
- **Performance**: often those programs which absolutely must be fast are also those which absolutely must be correct. Infrastructural software is constantly depended on, and must perform well.

The design decisions of the project were made intentionally to support those values. All the bullets below are given their own section discussing the details.

- **Correctness**
  - Rok is dependently typed in a strong type theory, giving it the logical power necessary to verify any property a user can prove in the calculus of constructions. Quote [Adam Chlipala "Why Coq?"](http://adam.chlipala.net/cpdt/html/Cpdt.Intro.html)
  - Rok is self-hosting but bootstrapped from Coq, meaning it is able to verify itself and was originally verified in a well-tested and [even verified tool](TODO coqcoqcorrect).
- **Clarity**
  - Rok syntax rules only allow custom notation through the macro system, which ensures it is always scoped beneath a tracable and searchable name, making it much easier for new users to find explanations or definitions of custom notation.
  - Rok syntax is whitespace sensitive and designed to make program structure and code formatting directly correspond.
  - Rok syntax intentionally compresses different ways of expressing the same thing into the most general syntax choices, and requires the use of syntax sugars when they are available.
  - Rok's import mechanisms usefully expose different kinds of definitions differently, allowing users to not ever need problematic implicit imports.
  - Rok enables readable markdown documentation comments for definitions.
  - Rok's builtin formatter warns about inconsistent naming and capitalization.
  - Rok's core educational materials set a convention of approachability, tracability (calling out prerequisites), and clarity.
- **Practicality**
  - Rok is arbitrariliy metaprogrammable, allowing all the flexibility and power that entails, including creating "zero-cost languages" that enable fine-grained verification at higher levels of abstraction. It also means the compiler doesn't require any kind of extension or plugin API, the metaprogramming facilities subsume such things especially when combined with a query-based compiler.
  - Rok compute theory is generic over the environment, allowing programs in any environment to be verified. It includes a core "abstract assembly language" akin to llvm that allows general-purpose programs to be compiled to many architectures.
  - Rok trackable effects (based on Iron trackable resources) allow programs to be gradually verified, allowing users to understand and accept tradeoffs as they work on a codebase.
  - Rok trackable effects are generic over the environment, allowing environments to introduce new trackable effects.
  - Rok is designed with usability in mind, and has an easy to use `cargo`-like cli and package manager.
  - Rok is a "one-stop-shop" for engineers creating correct and performant software, since it can both verify and compile code.
  - Rok uses a query-based compiler, so its internals can be more easily exposed to allow more ergonomic and powerful macros.
- **Performance**
  - Rok compute theory goes all the way down to the metal, allowing arbitrarily fine-grained guarantees and optimizations.
  - Rok is itself built in compute Rok, meaning the same performance benefits it promises to users it also gives during type-checking and compilation.
  - Rok metaprograms are defined in Rok, meaning they perform well and can even be verified.
  - Rok uses a query-based compiler, so it efficiently avoids recomputing unchanged forms of a program.


My hypothesis for what determines language enthusiasm is: `possible_correctness * possible_performance * average_productive_usability`

# Design

Rok has three type universes:

- `Prop`, representing propositions (equivalent to coq `Prop`).
- `Ideal`, representing pure logical types arranged in an infinite hierarchy of universes (equivalent to coq `Set`/`Type`).
- `Type`, representing concrete computable types encodable in bits.






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

### phase 1, bootstrapping the rok compiler (catching a spark)

specifying calculus of constructions in coq (reusing coqcoqcorrect)

defining an abstract assembly language program that implements the proof checking kernel

building parser/renderer that can translate that assembly language program (and maybe it's higher-level forms?) into some usable machine code program, possibly reusing something like llvm but also possibly just going directly into x86? (at this point we're building an environment that acts like a "castle in the air", since the environment is merely stated axiomatically rather than directly inheriting its semantics from a verified lower-level host system)

we actually have a few different possible avenues here
- build the first version of the compiler in coq and extract to ocaml, which means we *might* have a functioning compiler sooner to use while building the self-hosting version, and we have a functional model to use while verifying the rok version. however it also means we have to implement the whole compiler twice.
- build a mere execution function in coq that interprets rok. probably really slow, not sure I like this option
- merely build a coq parser capable of ingesting the rok implementation *to verify it in coq* and then just a barebones renderer to compile it as llvm or x86

the *finished, self-hosting* compiler will have these layers:
- the axiomatic specification of the calculus of constructions (trusted theory base), written in ideal/prop rok
- the proof checker component, written in compute rok but verified using the axiomatic specification (probably useful to introduce a concept of "perfectly models" vs "models with assumptions" to link datatypes between ideal/prop rok and compute rok. for example something like a fixed width bit-word can only model numbers within certain assumptions, but enums or records or other such things can be a perfect correspondence)
- the compute theory libraries, written in ideal/prop rok but *modeling* compute rok
- the compiler component, written in compute rok *defining* the compute datatypes that *represent* rok, and verified using the compute theory libraries
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
