# Design of Magmide

Magmide has two essential components:

- Logic Magmide, the dependently typed lambda calculus of constructions. This is where "imaginary" types are defined and proofs are conducted.
- Host Magmide, the imperative language that actually runs on real machines.

These two components have a symbiotic relationship with one another: Logic Magmide is used to define and make assertions about Host Magmide, and Host Magmide computationally represents and implements both Logic Magmide and Host Magmide itself.

```
                       represents and
                         implements
      +----------------------+--------------------+
      |                      |                    |
      |                      |                    |
      v                      |                    |
Logic Magmide                +-------------> Host Magmide
      |                                           ^
      |                                           |
      |                                           |
      +-------------------------------------------+
                      logically defines
                        and verifies
```

The easiest way to understand this is to think of Logic Magmide as the type system of Host Magmide. Logic Magmide is "imaginary" and only exists at compile time, and constrains/defines the behavior of Host Magmide. Logic Magmide just happens to itself be a Turing complete dependently typed functional programming language!

Host Magmide must be runnable on the various development machines that could be used by engineers, so it needs to be highly abstract and capable of being assembled or "rendered" to many different specific architectures/environments. This means it must be similar to LLVM in terms of abstractness.

The initial bootstrapped version of the compiler will actually literally target LLVM intermediate representation! By doing this we'll be able to benefit from LLVM's maturity and large feature set to quickly build working programs. We'll also sacrifice perfect initial verification, since the LLVM implementation isn't verified. This is a worthwhile tradeoff to keep the project tractable.

The long term goal however is for Magmide to step into the same role as LLVM. Magmide will define an abstract assembly language similar in function to LLVM intermediate representation, intended to be assembled to real machine code by various "backends".

![LLVM compiler infrastructure](https://i.stack.imgur.com/9xGDe.png)

However in contrast to LLVM, this process can be end-to-end verified if backends formally define the semantics of the target instruction set architecture and operating environment and prove the assembly process correctly translates programs to the target.

Magmide has the opportunity to expose a more pleasant language than LLVM though, and to use metaprogramming to actually expose several layers at different levels of abstraction. I feel it's very important that programmers have access to lower levels of abstraction without having to drop all the way down to a specific assembly language. So I propose three layers of Host Magmide:

- Host Magmide itself, essentially at the level of C or Rust. This will be the actual syntactic language exposed by the compiler. It will have roughly the same syntactic feel as its Logic counterpart, so it should have functions, struct/tuple/union type definitions, match/if statements, and some reasonable loops (`for .. in`, `while`, `forever`) (it's unclear at this point if we want to give it a Rust-like ownership/lifetime system). Lower levels can be exposed using macros.
- Low Level Host Magmide, at the same level of LLVM. This means it has typed functions with labeled blocks and parameters that abstract away details of calling conventions and ABIs, as well as abstractions for system/external calls.
- Assembly Host Magmide, at the same level as a real assembly language, but with abstract instructions and registers so it can still be rendered to different architectures. This means it only has labeled sections with jump/branch instructions, allowing it to encode arbitrarily exotic control flow. However we can still use type preconditions over registers and memory locations. This layer is where calling conventions and function behaviors would be implemented.

Host Magmide is named intentionally, since it is only really intended to function for "typical" architectures, ones with a sufficient operating system environment to run the actual Magmide compiler. However the tool will be useful to write code for any architecture, since Logic Magmide can be used to define *other* languages than Host Magmide. All these use cases will be directly supported:

- Writing code for an architecture compatible with Host Magmide. This is obvious, since Host Magmide will be able to compile or cross-compile to any architecture is has a backend for. Initially this will be any architecture supported by LLVM.
- Writing code for an architecture that *isn't* compatible with Host Magmide. To do this you would formalize your target architecture/environment in Logic Magmide, write your program in whatever format you choose, use Host Magmide to parse and convert that format to the language's Logic Magmide form so you can make assertions about it, and then use Host Magmide to render the program so it can be used elsewhere. This pattern can support literally any language imaginable, from arbitrary assembly languages to custom DSLs to smart contract languages.
- Formalizing logic/mathematics, not intending to create runnable programs. Although it would seem this use case doesn't need to be able to check/compile/run computable programs, the user might still use metaprogramming to manipulate proofs, or use libraries that do. Before sending Logic Magmide structures to the kernel, any metaprogrammatic constructs need to be unfolded, which means the Host Magmide programs that are implied by those metaprogrammatic constructs need to be checked/compiled/run.

I believe this Logic/Host separation is one of the key ideas that will make Magmide successful. If a dependently typed language is going to be self-hosting/verifying, then it will necessarily formalize a computational language capable of being compiled for many different specific architectures and environments. The very act of doing that *for itself* has the happy coincidence of also giving it the ability to do so *for anything else*. We can support two massive families of use cases with one body of work. By "maxing out" both logical and computational power, we ironically end up having to make fewer built-in decisions.

Since Host Magmide is the computational language, it would make most sense to use it for metaprogramming routines, including ones that are intended to produce Logic Magmide terms. This means the compiler has to be built with a definition of Host Magmide present so it knows how to check and run metaprograms. (Since Logic Magmide strictly speaking can be evaluated at compile time by the reduction rules in the kernel, users could write compile-time functions using it, but the functions would be much slower. Language guides should focus on using Host Magmide for metaprogramming.)

To support all of this, the final compiler must include:

- Syntax tree datatypes and a parser for whatever top-level syntax we choose. This syntax must support all of Logic Magmide (inductive types, proofs, functions, theorems), Host Magmide, and whatever top-level metaprogrammatic entrypoints we choose.
- Core libraries defining and exposing Host Magmide. These core libraries can also include whatever other theories of logic or computation we think could be helpful for users.
- A proof checking kernel for Logic Magmide programs. This must include an interpreter that can evaluate Logic Magmide terms according to the [calculus of constructions reduction rules](https://coq.inria.fr/refman/language/core/conversion.html). This kernel should be verified to correspond to a trusted theory base of the calculus of constructions, heavily inspired by [Coq Coq Correct](https://metacoq.github.io/coqcoqcorrect). This means that Magmide won't only be self-hosting, but self-verifying.
- A build/run engine capable of running a cascade of metaprograms. This engine will accept a metaprogram AST representation and use the builtin Host Magmide definition/renderer to process it into a runnable program, set up the program's inputs, jump to the rendered metaprogram in memory, collect the outputs of the program, and continue that process using the outputs of each metaprogram until a stopping point is reached. An implied part of this loop is running proof checking to verify each program, since type checking a Host Magmide program is merely proof checking the various assertions made within it both by type annotations and things like `assert` statements.
- The above build/run engine must also be capable of rendering programs in any language with a full definition to the filesystem, including Host Magmide.

# Project plan

To build a self-hosting and self-verifying compiler, we need to bootstrap it from a language capable of performing both functions. For this I've chosen Coq.

In order to make sure the project is reasonable and going in the right direction, we need to prioritize working code and steady incremental iteration. It would be unwise to simply jump into bootstrapping the full real compiler. We also need to design our milestones strategically so that each milestone will be useful or exciting enough to inspire contributors to help push the project to the next milestone.

My general project plan is this:

- First create a toolchain capable of parsing Low Level Host Magmide code (easiest since it's just a razor thin convenience layer around LLVM), verifying assertions about it inside Coq, and rendering it to real LLVM. This whole pipeline will be a combination of Rust functions to parse source code and [construct LLVM](https://github.com/TheDan64/inkwell), linked together with a [Coq Ocaml plugin](http://gallium.inria.fr/blog/your-first-coq-plugin/) using the [Rust Ocaml bindings](https://docs.rs/ocaml/latest/ocaml/). Using unverified languages like Rust and Ocaml mean that this first version won't itself be verified, but it will still be capable of producing LLVM programs verified by the Coq kernel. These verified LLVM programs can be linked with any compatible language, such as Rust or WebAssembly. This milestone will already be useful to anyone willing to write their own theory and proofs in Coq and deal with this awkward toolchain.
- Then we can expand the syntax, capabilities, and theory of the language, and integrate Iris into the theory. Using Iris we can define how trackable effects work, and define the most important trackable effects relating to termination, execution safety, memory safety, and memory conservation. With each step of this milestone the language gets more legitimately useful to more people, since more things can be done and more things proven safe, they just have to write proofs in Coq. It would be possible and maybe useful to create Rust macros to allow easily binding to these externally verified programs.
- Build metaprogramming capability into the language, by using the Rust LLVM bindings to JIT compile metaprograms, set up their inputs, pass them control, gather their outputs, and continue the cycle.
- Now we can bootstrap the real compiler. More on that below.
- After the full language is bootstrapped it can be used for non-trivial but still extremely low level applications such as cryptography/networking libraries, deeply embedded applications such as IOT devices or firmware, or OS kernel level functions. During this phase we can begin to aggressively seek support and contributions from a much larger community, and start building the ecosystem foundations (awesome educational materials, standard libraries for Logic and Host Magmide, a package management system, a cli, a standard formatter, syntax highlighting and auto-completion plugins for common editors).
- With confidence in the design and growing support, begin to use Magmide to define *other* languages. Magmide could be used to incrementally reimplement the foundations of Rust, giving it built-in access to a proof checker. Magmide would be a perfect fit to implement smart contract languages. I have some fun ideas for a highly inferred async actor language. It might even be cool to write something at the level of Typescript with a verified interpreter. These higher level languages will likely be even more exciting to a broader audience and can give the project even more momentum.
- Then with higher level and more diverse languages, we can start to tackle ambitious projects that are uniquely enabled by Magmide. I've shared some ideas in [this section of the README](https://github.com/magmide/magmide#what-could-we-build-with-magmide) (operating systems, databases, UI frameworks, etc etc).

To summarize:

- Write/verify *any* program.
- Write/verify small programs with useful theory.
- Build metaprogramming.
- Bootstrap the compiler.
- Write/verify interesting but low level programs.
- Implement higher level languages in Magmide.
- Tackle truly novel projects.

Bootstrapping the compiler is just one bullet in the above plan, but it's a massive endeavor all its own! At that stage we'll have a Coq compiler capable of parsing/verifying/rendering Host Magmide, but with all propositions and proofs existing in Coq.

The final compiler however must be fully integrated, with all the theory, proofs, and implementation together in one codebase. Although the most straightforward way to achieve this is to simply implement the entire compiler all at once in Host Magmide, I think we can wriggle our way there incrementally by following this path:

- Implement Logic Magmide (parsing, AST, proof checker) using Host Magmide, checking the implementation using a Coq trusted theory base, which must be very carefully defined and audited by as many qualified people as possible.
- Implement an interactive proof system as a cli or language server. It will be extremely painful to implement the total compiler in an integrated way without this capability. We now officially have a usable proof assistant!
- Now we can port the theory and Host Magmide formalization from Coq to Logic Magmide, and get it working correctly with the new bare metal proof checker.
- And finally we can reimplement Host Magmide compilation using Host Magmide!

This first version will only focus on correctness, and leave performance and ergonomics for future iterations.

As we progress from Coq bootstrapping compiler to real compiler, we'll need to formalize many different aspects of computation, all of which will be exposed in the final standard library for reuse by other projects. Examples are:

- A formalization of binary values and operations, as well as common type patterns (tuples/structs, unions, lists, etc) as propositional predicates over binary arrays. This is pretty straightforward, and has already been done in [several](https://github.com/coq-community/bits) [other](https://github.com/mit-plv/bbv) [projects](https://github.com/jasmin-lang/coqword). However since Magmide intends to tie many trackable effects to binary operations such as integer overflow or division by zero, we might have to have our own implementation.
- A formalization of generic abstract machine states. Essentially we need a machine state definition that is polymorphic in what cores/instruction sets, register/memory banks, and environmental system calls it has access to. This definition should be as generic as possible so it can support even software hosted environments such as what's available to WebAssembly.
- A formalization of a reusable theory of well-founded termination in assembly languages. Especially we want a proof obligation generator capable of finding the smallest number of control flow jumps that need special proof justification. More in [`posts/toward-termination-vcgen.md`](./posts/toward-termination-vcgen.md). Possibility of non-termination can be allowed, but needs to be signaled with trackable effects.
- A formalization of a step relation compatible with mixed data/instruction memory. Fully modeling execution as what it really is, a program counter accessing arbitrary locations in memory, allows us to verify the correctness of truly exotic programs, such as those that execute foreign code after checking it (this is necessary in order to verify a metaprogrammable compiler) or even that modify themselves! Normal techniques such as defining a small-step relation and its big-step transitive closure don't work in this context, so reasoning about total program execution requires some inductive trace type. Alongside this step relation we need theory and helpers for reasoning about execution of well-formed (as in truly executable) and safe (as in checked) instructions. These also need to have accompanying trackable effects.
- A formalization of trackable effects with inspiration from Iron-style fractional tokens. This could need a custom resource algebra in order to be reusable for different types of effects, that remains to be seen.

# Notable design choices

## No `Set` type

`Set` is just `Type{0}`, so I personally don't see a reason to bother with `Set`. It makes learning more complex, and in the situations where someone might demand their objects to live at the lowest universe level (I can't come up with any convincing places where this is truly necessary, please reach out if you can think of one), they can simply use some syntax equivalent of `Type{0}`.

## Proof-irrelevant `Prop` type?

I haven't had time to thoroughly read [these](https://tel.archives-ouvertes.fr/tel-03236271/document) [papers](https://dl.acm.org/doi/pdf/10.1145/3290316) about proof-irrelevant proposition universes and how their design is related to homotopy type theory. However from my early reading it seems as if `Prop` could simply be made proof-irrelevant along with some changes to the rules about pattern matching from `Prop` to `Type` universes, and the language would be more convenient and cleaner.

Please reach out if you have knowledge about this topic you'd like to share!

## No distinction between inductive and coinductive types

Every coinductive type could be written as an inductive type and vice-versa, and the real difference between the two only appears in `fix` and `cofix` functions. Some types wouldn't actually be useful in one or other of the settings (a truly infinite stream can't possibly be finitely constructed and so would never be useful in a normal recursive function), but occasionally we might appreciate types that can be reasoned about in both ways.

So Magmide will only have one entrypoint for defining "inductive" types, and if a type could be compatible with use in either recursive or corecursive contexts then it can be used in either. It seems we could always infer whether a type is being used inductively or coinductively based on call context. If we can't, we should have a syntax that explicitly indicates corecursive use rather than splitting the type system.

Please reach out if you have knowledge about this topic you'd like to share!

## Interactive tactics are just metaprogramming

In Coq the tactics system and `Ltac` are "baked in", so writing proofs in a different tactic language requires a plugin.

In Magmide the default tactic language will just be a metaprogrammatic entrypoint that's picked up automatically by the parser, so any user can create their own.

```
// `prf` (or whatever syntax we choose) is basically just a "first-class" macro
thm four_is_even: even(4); prf;
  + add_two; + add_two; + zero

// you could write your own!
thm four_is_even: even(4); my_prf$
  ++crushit
```

## Builtin syntax for tuple-like and record-like types

In Coq all types are just inductive types, and those that only have one constructor are essentially equivalent to tuple or record types in other languages. This means that *all* data accesses have to ultimately desugar to `match` statements.

This cleanliness is fine and ought to remain that way in the kernel, but we don't have to make users deal with this distinction in their own code. Although Coq has somewhat supported these patterns with `Record` and primitive projections and other constructs, the implementation is cluttered and confusing.

Here's a possible example of defining and using a few inductive types:

```
// nothing interesting here, just pointing out it can be done
type MyUnit

// unions are roughly the same, again no interesting differences
type MyBool =
  | True
  | False

// however for record-like types, there should only be as much syntactic difference with other types as is absolutely necessary
type Person =
  name: string
  age: nat
// the only syntax allowed to construct a record-like type
let some_person = Person { name: "Alice", age: 12 }
print some_person.name
// we could still allow explicit partial application with a "hole" operator
let unknown_youth = Person { age: 12, _ }
let known_youth = unknown_youth { name: "Bob" }

// tuple-like types are similar
type Ip = (byte, byte, byte, byte)
// only syntax allowed to construct tuple-like types
let some_ip = Ip(127, 0, 0, 1)
// zero indexed field accessors
print some_ip.0
// partial application
let unknown_ip = Ip(_, 0, 0, _)
let known_ip = unknown_ip(127, 1)
```

## Anonymous union types

Often we find ourselves having to explicitly define boring "wrapper" union types that are only used in one place. It would be nice to have a syntax sugar for an anonymous union type that merely defines tuple-like variants holding the internal types. For example:

```
def my_weird_function(arg: bool | nat | str): str;
  match arg;
    bool(b); if b; "yes" \else; "no"
    nat(n); format_binary(nat)
    str(s); "string = #{s}"

// values can be passed without being wrapped or converted?
my_weird_function(true)
my_weird_function(2)
my_weird_function("hello")
```

## No implicit type coercion

Although type coercions can be very convenient, they make code harder to read and understand for those who didn't write it.

Similarly to how Rust chose to make all type conversions explicit with casts or [the `From`/`To` traits](https://doc.rust-lang.org/std/convert/trait.From.html), Magmide would seek to do the same. This means Magmide will have a trait/typeclass system.

We can however choose to make these conversions less verbose, perhaps choosing a short name such as `to` for the conversion function, or supporting conversions directly with some symbolic syntax (`.>`?).

## Inferred proof holes

The common case of writing verified functions is to write the `Type` level operations out explicitly (programmers are often quite comfortable with this kind of thinking), and then in a separate interactive proof block after the function body "fill in the blanks" for any implied `Prop` operations. In general it's more natural to separate data operations from proof operations, and Magmide will make this mode of operation the well-supported default.

Users can still choose to specify both `Type` and `Prop` operations explicitly. Or since `prf` is just a macro that constructs a term of some type, interactive tactics can be used to specify an entire term (as is possible in Coq), or *just a portion* of a term.

```
def my_function(arg: input_type): output_type;
  // I know I need to call this function with some known inputs...
  arg.inner_function(
    known_input, other_known_input,
    // ... but what should this be again?
    prf;
      // some tactics...
  )
```

Since often we need to help a type-checking algorithm along at some points, an `assert` keyword can be used to generate a proof obligation making sure some hypothesis type is actually available at some point in a function. This would basically be a `Prop` level type cast that must be justified in the proof block after the function.

```
def my_function(arg: input_type): output_type;
  let value1 = arg.function(known_value)
  let value2 = arg.other(something)
  // I know something should be true about these values...
  assert SomeProp(value1, value2)
  // ... which makes the rest of my function easier
  some_function_requiring_SomeProp(value1, value2)
prf;
  // tactics proving SomeProp(value1, value2)
```

## Builtin "asserted types"

Subset types are often a more natural way of thinking about data, and packaging assertions about data into the type of the data itself frees us from a few annoyances such as having to declare proof inputs as separate arguments to functions or at different levels of a definition.

Although in a dependent type theory a subset type is absolutely a strictly different type than a normal constructed value, we can make life easier by making it easy to define and quickly pull values in and out of subset types. I call these cheap representations of subset types "asserted types".

```
// using & is syntactically cheap
type MyByte = nat & < 256
// multiple assertions
type EligibleVoter = Person & .age >= 18 & .alive
// with parentheses if we want to be clearer
type EligibleVoter = Person & (.age >= 18) & .alive

// using a list of predicates and a proof that all of them hold is more flexible than a single nested proposition
type AssertedType (T: Type) (assertions: list (T -> Prop)) =
  forall (t: T), (t, ListForall assertions (|> assertion; assertion(t)))
```

We can provide universal conversion implementations to and from types and asserted versions of themselves. Pulling a value out of an asserted type is easy. Putting a value into an asserted type or converting between two seemingly incompatible asserted types would just generate a proof obligation.

## Cargo-like tooling

To actually interact with Magmide, I imagine using a cli with these basic commands:

- `magmide check` would perform proof checking. If there are any computable code blocks that make any kind of assertions (even type annotations are assertions!) then those assertions are checked. This implies the necessity to run the cascade of metaprograms, and therefore perform any side-effects performed by those metaprograms. Any commands that ask for Logic Magmide to be "evaluated" (such as Coq's `Compute` command) would happen at this level, since evaluation of Logic Magmide is merely done in the kernel.
- `magmide compile` would perform `check` first, and implies the presence of *some* computational programs, and therefore a full definition for it that includes a renderer. The compiler ships with a full definition for Host Magmide, so users don't have to supply a definition if that's their target. If there isn't any configured path to a computational program and its definition, an error is thrown. We could include a flag to merely exit successfully if there isn't any computational program present.
- `magmide run` would perform `check` and `compile` first, and so again implies a computational program and full definition. It also implies the availability of a machine capable of running the rendered artifact, either the host machine itself if the program is in or compatible with Host Magmide, or some connected debuggable device. If there isn't a usable machine available, an error is thrown.

## Metaprogramming instead of custom Notation

Coq's [Notation system](https://coq.inria.fr/refman/user-extensions/syntax-extensions.html) is extremely complex. It essentially allows creating arbitrary custom parsers within Coq. While this may seem like a good thing, it's a bad thing. Reasoning about these custom parsing and scoping rules is extremely difficult, and easy to get wrong. It adds a huge amount of work to maintain the system in Coq, and learn the rules for users.

It also makes it extremely easy to create custom symbolic notation that makes code much more difficult to learn and understand. Allowing custom symbolic notation is a bad design choice, since it blurs the line between the primitive notations defined by the language (which are reasonable to expect as prerequisite knowledge for all users) and custom notations. Although Coq makes it possible to query for notation definitions, this is again just more maintenance burden and complexity that still adds significant reading friction.

Magmide's metaprogramming system won't allow unsignified custom symbolic notation, and will require all metaprogrammatic concepts to be syntactically scoped within known identifiers. Instead of defining an extremely complicated set of macro definition rules, metaprogramming in Magmide will give three very simple "syntactic entrypoints", and then just expose as much of the compiler query api as possible to allow for compile-time type introspection or other higher-level capabilities.

Macros can either accept raw strings as input and parse them themselves or accept Magmide parsed token trees. This complete generality means that Magmide can support *any* parsing pattern for embedded languages. Someone could even define something just like Coq's notation system if they really want to, and their custom system would be cleanly cordoned off behind a clear `macro_name$` style signifier. By just leaning all the way into the power of metaprogramming, we can allow *any* feature without having to explicitly support it.

To actually use macros you can do so inline, as a block, or using a "virtual" import that processes an entire file.

### Inline macros

Inspired by Rust's explicit `!` macros and javascript template literals.

Raw string version:

```
macro_name`inline raw string`
```

Syntax tree version:

```
macro_name$(some >magmide (symbols args))
```

### Block macros

Uses explicit indentation to clearly indicate scope without requiring complex parsing rules.

Raw string version uses a "stripped indentation" syntax inspired by [Scala multiline strings](https://docs.scala-lang.org/overviews/scala-book/two-notes-about-strings.html#multiline-strings), but using pure indentation instead of manual `|` characters.

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

Token tree version is like "custom keywords", with an "opening block" that takes two token trees for header and body, and possible continuation blocks. Here's an example of a "custom" if-else block being used.

```
$my_if some.conditional statement;
  the.body
  >> of my thing

/my_else; some_symbol()
```

### Import macros

Allows entire files to be processed by a macro to fulfill an import command. you'll notice the syntax here is exactly the same as inline macros, but the language will detect their usage in an import statement and provide file contents and metadata automatically.

```
use function_name from macro_name`./some/file/path.extension`
```


<!-- Now with a proof language, one can define types that model bits, binary arrays, register banks, memory banks, and therefore total machine states. Then one can define various predicates over these types, and model "computable types" by defining specific predicates. One can prove partial or total symmetries/modelings between binary arrays fulfilling certain predicates and other normal ideal types. one can define ideal types representing machine instructions, and parser/render functions that are provably inverses, and prove assertions about machine instructions and their effects on a machine state.
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

what's the difference between a bit array defined in Logic Magmide but computationally represented in the smart packed format, and a real bit array? there's no difference at all, at least between a particular concrete one.
 -->
<!--
However there are some subtleties we have to contend with since Magmide is so inherently intended for verification of *real* computational programs.
The kernel has to be actually *implemented* in some real computational language, and we'd prefer it was a maximally performant one. Also, metaprogramming of all kinds, whether manipulating Logic Magmide terms or anything else, also has to be implemented in a real computational language. These might as well be the same language. This language needs to be one that can be run on *development* machines, the ones that will compile whatever final artifacts. Let's define the term Host Magmide to refer to this aspect.

So the final compiler will be a binary artifact runnable on some collection of host architectures. This artifact will have a few components:

parser, capable of parsing Logic Magmide, metaprogramming constructs, and any other constructs we choose to include in the shipped language syntax, all into Host Magmide data structures.
proof checking kernel, which accepts some Host Magmide data structure representing Logic Magmide terms.
metaprogramming checker/runner. the compiler has builtin definitions and models of Host Magmide, so it can take AST structures representing Host Magmide and check them (Host Magmide likely includes syntax to make assertions about state, which are implicitly predicates over binary arrays), render/assemble them to some place in memory or a file, and jump to them to execute them (possibly having provided arguments by fulfilling whatever calling convention)


the magmide compiler is a program that can operate in any specific machine of a universe of machines that have been modeled at the time of the compiler being compiled. this universe of machines has been modeled with some kind of with input/output capabilities and probably some concepts of operating system services such a filesystem. so Host Magmide can include functions to write to files, and can expose functions for core concepts such as rendering compilation artifacts (probably accepting custom AST/assertions/checkers/renders etc)
 -->

<!--
- Magmide syntax rules only allow custom notation through the macro system, which ensures it is always scoped beneath a traceable and searchable name, making it much easier for new users to find explanations or definitions of custom notation.
- Magmide syntax is whitespace sensitive and designed to make program structure and code formatting directly correspond.
- Magmide syntax intentionally compresses different ways of expressing the same thing into the most general syntax choices, and requires the use of syntax sugars when they are available.
- Magmide's import mechanisms usefully expose different kinds of definitions differently, allowing users to not ever need problematic implicit imports.
- Magmide enables readable markdown documentation comments for definitions.
- Magmide's builtin formatter warns about inconsistent naming and capitalization.
- Magmide's core educational materials set a convention of approachability, traceability (calling out prerequisites), and clarity.
-->
