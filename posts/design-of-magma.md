# Overall design and roadmap

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

The easiest way to understand this is to think of Logic Magma as the type system of Host Magma. Logic Magma is "imaginary" and only exists at compile time, and constrains/defines the behavior of Host Magma. Logic Magma just happens to itself be a turing complete dependently typed functional programming language!

Since Host Magma is the computational language, it would make most sense to write metaprogramming routines in it, including ones that are intended to produce Logic Magma terms. This means the compiler has to be built with a definition of Host Magma present so it knows how to check and run metaprograms. (Of course since Logic Magma strictly speaking can be evaluated at compile time by the reduction rules in the kernel, then people could write compile-time functions in it, but the functions would be much slower. Language guides should focus on using Host Magma for metaprogramming.)

Host Magma must be runnable on the various development machines that could be used by engineers, so it needs to be highly abstract and capable of being assembled or "rendered" to many different specific architectures/environments. This means it must be similar to LLVM in terms of abstractness. However something as low-level as LLVM would be very painful to write a full production-grade compiler in, so it makes sense for Host Magma to *really* be some higher level language that's lowered to the LLVM equivalent using metaprogramming. Since Host Magma will be at the same level as LLVM, it will similarly need "backends" capable of rendering it to the concrete instruction set. We could very well choose to piggyback on LLVM for the first stage of the project! However LLVM doesn't have any verification/separation logic capabilities, and the backends themselves aren't verified to maintain IR semantics to the concrete architecture, so LLVM can't be the final goal.

Logic Magma can of course be used to define any *other* object language. So if you wanted to use Magma to verify and compile a program in some other architecture/environment, you would give that architecture/environment a full definition in Logic Magma, write your program in whatever format you choose, use Host Magma to parse and convert that format to the language's Logic Magma form so you can make assertions about it, and then use Host Magma to render the program so it can be used elsewhere.

So the final compiler must include:

- Syntax tree datatypes and a parser for whatever top-level syntax we choose. This syntax must support all of Logic Magma (inductive types, proofs, functions, theorems), whatever top-level metaprogrammatic entrypoints we choose, and whatever layer/variant of Host Magma we choose to directly support outside of metaprogrammatic entrypoints.
- Core libraries defining and exposing Host Magma. These core libraries can also include whatever other theories of logic or computation we think could be helpful for users.
- A proof checking kernel for Logic Magma programs. This must include an interpreter that can evaluate Logic Magma terms according to the [calculus of constructions reduction rules](https://coq.inria.fr/refman/language/core/conversion.html). This kernel should be verified to correspond to a trusted theory base of the calculus of constructions, heavily inspired by [Coq Coq Correct](https://metacoq.github.io/coqcoqcorrect). This means that Magma won't only be self-hosting, but self-verifying.
- A build/run engine capable of running a cascade of metaprograms. This engine will accept a metaprogram AST representation and use the builtin Host Magma definition/renderer to process it into a runnable program, set up the program's inputs, jump to the rendered metaprogram in memory, collect the outputs of the program, and continue that process using the outputs of each metaprogram until a stopping point is reached. An implied part of this loop is running proof checking to verify each program, since type checking a Host Magma program is merely proof checking the various assertions made within it both by type annotations and things like `assert` statements.
- The above build/run engine must also be capable of rendering programs in any language with a full definition to the filesystem, including Host Magma.

To actually interact with Magma, I imagine using a cli with these basic commands:

- `magma check` would perform proof checking. If there are any computable code blocks that make any kind of assertions (even type annotations are assertions!) then those assertions are checked. This implies the necessity to run the cascade of metaprograms, and therefore perform any side-effects performed by those metaprograms. Any commands that ask for Logic Magma to be "evaluated" (such as Coq's `Compute` command) would happen at this level, since evaluation of Logic Magma is merely done in the kernel.
- `magma compile` would perform `check` first, and implies the presence of *some* computational programs, and therefore a full definition for it that includes a renderer. The compiler ships with a full definition for Host Magma, so users don't have to supply a definition if that's their target. If there isn't any configured path to a computational program and its definition, an error is thrown. We could include a flag to merely exit successfully if there isn't any computational program present.
- `magma run` would perform `check` and `compile` first, and so again implies a computational program and full definition. It also implies the availability of a machine capable of running the rendered artifact, either the host machine itself if the program is in or compatible with Host Magma, or some connected debuggable device. If there isn't a usable machine available, an error is thrown.

To build a self-hosting and self-verifying compiler, we need to bootstrap it from a language capable of performing both functions. For this I've chosen Coq.

Here are the steps I plan to take:

## Formalize theory foundation

Create the foundations of the purely abstract computational theory in Coq. This is itself a fairly large task we can break up:

- Formalize binary values and operations, as well as common type patterns as propositional predicates over binary arrays. This is pretty straightforward, and has already been done in [several](https://github.com/coq-community/bits) [other](https://github.com/mit-plv/bbv) [projects](https://github.com/jasmin-lang/coqword). However since Magma intends to tie many trackable effects to binary operations such as integer overflow or division by zero, we might have to have our own implementation.
- Formalize generic abstract machine states. Essentially we need a machine state definition that is polymorphic in what cores/instruction sets, register/memory banks, and environmental system calls it has access to. This definition should be as generic as possible so it can support even software hosted environments such as what's available to webassembly.
- Formalize a reusable theory of well-founded termination in assembly languages. Especially we want a proof obligation generator capable of finding the smallest number of control flow jumps that need special proof justification. More in [`posts/toward-termination-vcgen.md`](./posts/toward-termination-vcgen.md). Possibility of non-termination can be allowed, but needs to be signaled with trackable effects.
- Formalize a step relation compatible with mixed data/instruction memory. Fully modeling execution as what it really is, a program counter accessing arbitrary locations in memory, allows us to verify the correctness of truly exotic programs, such as those that execute foreign code after checking it (this is necessary in order to verify a metaprogrammable compiler) or even that modify themselves! Normal techniques such as defining a small-step relation and its big-step transitive closure don't work in this context, so reasoning about total program execution requires some inductive trace type. Alongside this step relation we need theory and helpers for reasoning about execution of well-formed (as in truly executable) and safe (as in checked) instructions. These also need to have accompanying trackable effects.
- Integrate the above machine state theory with Iris, to create a similarly polymorphic separation logic. This will probably be the most difficult step, since Iris, while being very well designed, wasn't designed with ergonomic use by engineers in mind. We'll likely need a lot of help from the Iris core team with this step.
- Formalize trackable effects with inspiration from Iron-style fractional tokens. This could need a custom resource algebra in order to be reusable for different types of effects, that remains to be seen.

## Define Host Magma

This will involve:

- Using the above foundational theory to define the "bottom" axiomatic layer of Host Magma in Coq. This layer is the LLVM-like environment. We might even choose to formalize a subset of LLVM itself in order to benefit from the project's maturity!
- Defining any "temporary" notations or metaprogrammatic constructs in Coq to define higher-level usage patterns for Host Magma. These will be helpful to keep us sane as we try to define Host Magma programs, but won't be the "official" higher-level constructs that will end up being used in the actual Magma implementation.

## Bootstrap the compiler

This is the tricky bit!

Obviously once the whole process is done, all of the components stated above (trusted theory base, computational theory, Host Magma definition, proof checking kernel, parser and build/render engine) will exist as Magma files, since that's what a self-hosting compiler is! However there could be a few ways forward to that goal.

The most obvious path forward is to just write a fully capable (but not fully performant and ergonomic) compiler in Coq first, then use it to verify/render Magma files. Then we can write the self-hosting Magma compiler in Magma and compile/verify the first version using the Coq implementation. While this is very obvious, it would involve a lot of duplication of work.

That path will likely be the one we take, but I'd love to figure out some way to write less Coq by bootstrapping individual components of the compiler independently, and using them to help bootstrap the others. I haven't figured out a consistent way to do so, but I'm open to any thoughts!

<!--
indulge me for a moment while I toy around with ways it could possibly be a bit easier.

Logic Magma is just a calculus of constructions, so we could think of it as merely an alternate syntax for Coq. This means we could write all the Logic Magma up front and then just use Coq to verify it.

It seems we can cheat a little by bootstrapping just the parser/renderer by itself first, by writing a Coq program only capable of doing that portion, and using it to compile the bare metal version. With just the parser/renderer we can still compile runnable versions of Magma programs, we just have to find some way to ingest them into Coq to be verified.

It seems all the Logic Magma stuff and the proof checking kernel is the part we can avoid writing until the very end, as long as all the assertions in Magma code can be converted into an accurate Coq equivalent.

, as long as it can somehow share an accurate representation with Coq to do all the actual verifying. We'd still have to write the initial version of the parser/renderer in Coq, but that's not as difficult as writing the entire compiler in Coq. With a bare metal parser/renderer in our hands that can output files for Coq to verify (possibly `.v` files or even raw binary files of an AST to pass directly to the existing Ocaml kernel) we can write everything else directly in Magma, verify it in Coq, then fully compile it and iterate until it's capable of verifying and compiling itself.

## metacoq parser

build a simple and strict indentation based block-line oriented parser in Coq/Ocaml, and use it within metacoq to be able to ingest things from other files.

what this would let us do is define all the initial logic stuff in magma syntax, and just convert it into Coq to leverage the existing proof checker and even tactic runners etc.
-->

## Build the ecosystem

Once the first full version of the compiler is bootstrapped then the real work begins. The language isn't truly done until it has:

- Awesome educational materials.
- Standard libraries for both Logic and Host Magma.
- A package management system.
- Tooling such as the `magma` cli, a standard formatter, and syntax highlighters and auto-completion plugins for common editors.

And of course the process of improving the power, performance, and usability of the language, and the maturity of the broader ecosystem, will never end.

# Notable design differences with Coq

## No `Set` type

`Set` is just `Type{0}`, so I personally don't see a reason to bother with `Set`. It makes learning more complex, and in the situations where someone might demand their objects to live at the lowest universe level (I can't come up with any convincing places where this is truly necessary, please reach out if you can think of one), they can simply use some syntax equivalent of `Type{0}`.

## Proof-irrelevant `Prop` type?

I haven't had time to thoroughly read [these](https://tel.archives-ouvertes.fr/tel-03236271/document) [papers](https://dl.acm.org/doi/pdf/10.1145/3290316) about proof-irrelevant proposition universes and how their design is related to homotopy type theory. However from my early reading it seems as if `Prop` could simply be made proof-irrelevant along with some changes to the rules about pattern matching from `Prop` to `Type` universes, and the language would be more convenient and cleaner.

Please reach out if you have knowledge about this topic you'd like to share!

## No distinction between inductive and coinductive types

Every coinductive type could be written as an inductive type and vice-versa, the real difference between the two really happens in `fix` and `cofix`. Some types wouldn't actually be useful in one or other of the settings (a truly infinite stream can't possibly be finitely constructed and so would never be useful in a normal recursive function), but occasionally we might appreciate types that can be reasoned about in both ways.

So Magma will only have one entrypoint for defining "inductive" types, and if a type could be compatible with use in either recursive or corecursive contexts then it can be used in either. It seems we could always infer whether a type is being used inductively or coinductively based on call context. If we can't, we should have a syntax that explicitly indicates corecursive use rather than splitting the type system.

Please reach out if you have knowledge about this topic you'd like to share!

## Interactive tactics are just metaprogramming

In Coq the tactics system and `Ltac` are "baked in", so writing proofs in a different tactic language requires a plugin.

In Magma the default tactic language will just be a metaprogrammatic entrypoint that's picked up automatically by the parser, so any user can create their own.

```
// `prf` (or whatever syntax we choose) is basically just a "first-class" macro
thm four_is: even(4); prf;
  + add_two; + add_two; + zero

// you could write your own!
thm four_is: even(4); my_prf$
  ++crushit
```

## Builtin syntax for tuple-like and record-like types

In Coq all types are just inductive types, and those that only have one constructor are essentially equivalent to tuple or records types in other languages. This means that *all* data accesses have to ultimately desugar to `match` statements.

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

## No implicit type coercion

Although type coercions can be very convenient, they make code harder to read and understand for those who didn't write it.

Similarly to how Rust chose to make all type conversions explicit with casts or [the `From`/`To` traits](https://doc.rust-lang.org/std/convert/trait.From.html), Magma would seek to do the same. This means Magma will have a trait/typeclass system.

We can however choose to make these conversions less verbose, perhaps choosing a short name such as `to` for the conversion function, or supporting conversions directly with some symbolic syntax (`.>`?).

## Inferred proof holes

The common case of writing verified functions is to write the `Type` level operations out explicitly (programmers are often quite comfortable with this kind of thinking), and then in a separate interactive proof block after the function body "fill in the blanks" for any implied `Prop` operations. In general it's more natural to separate data operations from proof operations, and Magma will make this mode of operation the well-supported default.

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
  (x, ListForall assertions (|> assertion; assertion(x)))
```

We can provide universal conversion implementations to and from types and asserted versions of themselves. Pulling a value out of an asserted type is easy. Putting a value into an asserted type or converting between two seemingly incompatible asserted types would just generate a proof obligation.

## Metaprogramming instead of custom Notation

Instead of defining an extremely complicated set of macro definition rules, metaprogramming in Magma will give three very simple "syntactic entrypoints", and then just expose as much of the compiler query api as possible to allow for compile-time type introspection or other higher-level capabilities.

Macros can either accept raw strings as input and parse them themselves (this allows for arbitrarily flexible and evolving community parsing patterns) or accept Magma parsed token trees (like most languages). To actually call them you can do so inline, as a block, or using a "virtual" import that processes an entire file.

### Inline macros

Inspired by Rust's explicit `!` macros and javascript template literals.

Raw string version:

```
macro_name`inline raw string`
```

Syntax tree version:

```
macro_name$(some >magma (symbols args))
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

Token tree version is like "custom keywords", with an "opening block" that takes two token trees for header and body, and possible contination blocks. Here's an example of a "custom" if-else block being used.

```
$my_if some.conditional statement;
  the.body
  >> of my thing

/my_else; some_symbol()
```

### Import macros

Allows entire files to be processed by a macro to fulfill an import command. you'll notice the syntax here is exactly the same as inline macros, but the language will detect their usage in an import statement and provide file contents and metadata automatically.

```
// raw string version
use function_name from macro_name`./some/file/path.extension`
// token tree version
use function_name from macro_name$(./some/file/path.extension)
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

what's the difference between a bit array defined in Logic Magma but computationally represented in the smart packed format, and a real bit array? there's no difference at all, at least between a particular concrete one.
 -->
<!--
However there are some subtleties we have to contend with since Magma is so inherently intended for verification of *real* computational programs.
The kernel has to be actually *implemented* in some real computational language, and we'd prefer it was a maximally performant one. Also, metaprogramming of all kinds, whether manipulating Logic Magma terms or anything else, also has to be implemented in a real computational language. These might as well be the same language. This language needs to be one that can be run on *development* machines, the ones that will compile whatever final artifacts. Let's define the term Host Magma to refer to this aspect.

So the final compiler will be a binary artifact runnable on some collection of host architectures. This artifact will have a few components:

parser, capable of parsing Logic Magma, metaprogramming constructs, and any other constructs we choose to include in the shipped language syntax, all into Host Magma data structures.
proof checking kernel, which accepts some Host Magma data structure representing Logic Magma terms.
metaprogramming checker/runner. the compiler has builtin definitions and models of Host Magma, so it can take AST structures representing Host Magma and check them (Host Magma likely includes syntax to make assertions about state, which are implicitly predicates over binary arrays), render/assemble them to some place in memory or a file, and jump to them to execute them (possibly having provided arguments by fulfilling whatever calling convention)


the magma compiler is a program that can operate in any specific machine of a universe of machines that have been modeled at the time of the compiler being compiled. this universe of machines has been modeled with some kind of with input/output capabilities and probably some concepts of operating system services such a filesystem. so Host Magma can include functions to write to files, and can expose functions for core concepts such as rendering compilation artifacts (probably accepting custom AST/assertions/checkers/renders etc)
 -->

<!--
- Magma syntax rules only allow custom notation through the macro system, which ensures it is always scoped beneath a traceable and searchable name, making it much easier for new users to find explanations or definitions of custom notation.
- Magma syntax is whitespace sensitive and designed to make program structure and code formatting directly correspond.
- Magma syntax intentionally compresses different ways of expressing the same thing into the most general syntax choices, and requires the use of syntax sugars when they are available.
- Magma's import mechanisms usefully expose different kinds of definitions differently, allowing users to not ever need problematic implicit imports.
- Magma enables readable markdown documentation comments for definitions.
- Magma's builtin formatter warns about inconsistent naming and capitalization.
- Magma's core educational materials set a convention of approachability, traceability (calling out prerequisites), and clarity.
-->
