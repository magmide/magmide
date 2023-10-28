# Design of Magmide

To achieve the goals of the Magmide project, we have to arrive at a system with these essential components:

- The Logic language, a dependently typed lambda calculus of constructions. This is where "imaginary" types are defined and proofs are conducted.
- The Host language, an imperative language that actually runs on real machines.

If we have such a system, then *both* components (Logic and Host) can *formally reason about each other and themselves*, and can *run with bare-metal performance*.

```
         represents and
           implements
  +------------+------------+
  |            |            |
  |            |            |
  v            |            |
Logic          +---------> Host
  |                         ^
  |                         |
  |                         |
  +-------------------------+
        logically defines
          and verifies
```

These two components have a symbiotic relationship with one another: Logic is used to define and make assertions about Host, and Host computationally represents and implements both Logic and Host itself.

The easiest way to understand this is to think of Logic as the type system of Host. Logic is "imaginary" and only exists at compile time, and constrains/defines the behavior of Host. Logic just happens to itself be a dependently typed functional programming language!

This architecture makes it possible to max out all the important aspects of the language:

- **Max out logical power** by making the full power of dependent type theory available to all components at all stages. Without this the design wouldn't be able to handle lots of interesting/useful/necessary problems, and couldn't be adopted by many teams. It wouldn't be able to act as a true *foundation* for verified computing.
- **Max out computational power** by self-hosting in a bare metal language. If the language were interpreted or garbage collected then it would always perform worse than is strictly possible.
- **Max out expressive power** by allowing deep metaprogramming capability. Metaprogramming is basically a cheat code for language design, since it gives a language access to an infinite range of possible features without having to explicitly support them. It's the single best primitive to add in terms of implementation overhead versus expressiveness.

For a long time the goal of this project was to build a *new* Host language, something analogous to [LLVM](https://en.wikipedia.org/wiki/LLVM), so that all the formal reasoning could be made *foundational* (reaching all the way down to hardware), and so that extreme portability could be achieved. Those aims are absolutely still a part of the long-term vision of the project, but after discussions with [Juan Benet](https://www.linkedin.com/in/jbenetcs) and [Tej Chajed](https://www.chajed.io/) it was realized the project would be more realistic if it first sought to serve the needs of an existing language community. Rust is the obvious choice!

With this realization the new project roadmap has these essential milestones:

### Build a proof assistant in Rust.

A proof assistant is just a programming language with a type system powerful enough to represent pure logic, perhaps with some convenience features added on top to make it easier to practically use. This is what "Magmide" will actually be, a proof assistant written in Rust, designed from the beginning to be high-performing, highly modular and reusable from other projects, with support for and emphasis of Rust as the language of proof tactics and metaprogramming.

So Rust will be to Magmide what [OCaml is to Coq](https://github.com/coq/coq). This means that Magmide will be the "Logic" language in the above diagram.

### Formalize Rust inside Magmide.

A proof assistant is powerful enough to formally specify all the rules of any programming language less logically powerful than it, so just how [researchers have defined semantics for many languages in Coq](https://softwarefoundations.cis.upenn.edu/plf-current/Preface.html), so too could we define the semantics of Rust in Magmide.

Doing this will *mostly* involve following in the lead of the various [RustBelt projects](https://plv.mpi-sws.org/rustbelt/) (and so would need to also translate Iris into Magmide). However it will be somewhat more difficult in our case, since we'll need to define the semantics more precisely in order to achieve the next milestone.

### Allow Magmide to formally certify Rust!

If Magmide is implemented in Rust, and the formal semantics of Rust are transcribed in Magmide, then it's possible to ingest *real* Rust code and formally reason about it in Magmide!

[Reflective proofs](http://adam.chlipala.net/cpdt/html/Reflection.html) are ones in which a *computable function* is used to certify some input data has some properties. To do this you need to be able to prove that certain properties of the *certifying function* demonstrate properties of the *input data*. This technique allows the proof assistant to merely run a function at proof-checking time rather than checking a possibly massive proof object.

This kind of recursive self-analysis will be extremely powerful, especially to [hopefully dramatically improve the performance of many proof search/checking scenarios](https://gmalecha.github.io/reflections/2017/speeding-up-proofs-with-computational-reflection) (more discussion about performance below).

To achieve recursive self-analysis we will:

- Implement the "Host reflection" rule in Magmide. This means writing a special rule into the proof checker that accepts a proposition as proven if: given an *AST* of a Rust function and a normal Magmide proof that this AST is a "certifier", it compiles and successfully runs over whatever inputs are conditions of the proposition in question.
- Implement the systems that can actually ingest real rust ASTs in whatever way is necessary for the Host reflection rule.
- Design and implement whatever syntactic affordances make it clean and ergonomic to make proof assertions about real Rust. *Handwaving goes here!* This could happen in a multitude of different ways, and could be incrementally improved over time.
- Figure out the [Trackable Effects](https://github.com/magmide/magmide#gradually-verifiable) system. This seems important to really make Rust fully formalizable, since effects are such a critical part of real system correctness.

---

After the above milestones are achieved, we will have officially achieved the base goals of the Magmide project! From there we'd be able to incrementally improve performance and usability, and also take on further challenges:

- Circle back to extending the formal foundations all the way to the hardware! This would involve verifying LLVM or building some new LLVM analogue, as well as the specific [architecture backends](https://en.wikipedia.org/wiki/LLVM#Backends).
- Build a formally verified Rust compiler! If we can formally verify Rust code, then we can incrementally verify the compiler itself.
- Formally verify the Magmide proof checker using a trusted theory base, much like was done in the [metacoq project](https://metacoq.github.io/).

# Interlude on proof assistant performance

One of the main reasons proof assistants and formal verification in general aren't mainstream is because existing proof assistants are *slow*. It isn't uncommon for large academic formalizations to take *many hours* to complete proof checking. This obviously can't scale to industrial codebases.

This performance problem is largely a consequence of lack of priority. Almost all proof assistants were designed and built by academics for their own purposes, and industrial use is largely considered a bonus. Good work is certainly done to improve performance, but few projects concern themselves with that from the beginning. There is some low-hanging fruit to be had here, such as using [incremental compilation](https://blog.rust-lang.org/2016/09/08/incremental.html). Overall though, mere compiler design probably isn't the biggest problem.

It seems pretty obvious that the *most* concerning problem is the poor performance of proof searching tactics. In languages such as Coq, proof tactics perform poorly for a few reasons:

- The [Coq Ltac language is a separate interpreted language](https://coq.inria.fr/refman/proof-engine/ltac2.html#ltac2). Interpreted languages are slow! And such an ad-hoc language embedded into a larger system will never get the amount of performance attention it needs. Tactics don't actually have to be "correct" or "sound", they're just computations that *attempt* to find a proof term that seems like it will correctly proof-check to solve some goal. This means they can be written in any language we want.
- Tactics often function by *searching* using various heuristics to find proof terms, and these searches by their very nature can sometimes take a long time!

Magmide intends to attack these performance problems in these ways:

- Using and emphasizing a high-performance language for proof tactics. Rust is an amazing language, and it seems like a perfect choice, especially since using Rust allows [binding to basically any other language](https://www.hobofan.com/rust-interop/). We could allow people to bring whatever tools they want to bear on proof search!
- Proof *search* is often slower than proof *checking*. Once proof search has successfully found a correct proof term, it is wasteful and slow to run that search again instead of merely caching the proof term. Intelligently implemented incremental compilation can absolutely prevent many of these wasteful repeat proof searches.
- Emphasizing [reflective proofs](http://adam.chlipala.net/cpdt/html/Reflection.html) for whatever situations allow it, as discussed above. I have a hunch many of the most common industrial use cases will be amenable to reflective proof. For example, just imagine if the Rust borrow checker was sufficiently verified to be a certifier!

Taken all together these improvements make a convincing case for Magmide as a foundation for a fully verified software ecosystem, and the first proof assistant to go mainstream among industrial engineers.

# Other notable design choices

## Corruption Panics

Magmide will formalizes some kind of `panic` effect that can be used to mark programs, making it possible for ambitious projects to prove that they *cannot* panic. However realistic low-level software must contend with the possibility of *hardware* failure that has created data corruption. It should be possible to write code that asserts the maintenance of invariants despite possible hardware failure.

Excitingly the need to check possible hardware failure doesn't have to mean we must tolerate ubiquitous `panic` trackable effects on all our code. If we introduce a separate idea of a *corruption* panic, an effect requiring a proof that, *assuming consistency of the hardware axioms*, the `panic` is impossible, we can write highly defensive software without giving up proof of panic freedom under normal hardware operation.

## Assumption Panics

Similarly to corruption panics, it should be possible to prove some panics will only occur if some *logical* assumption isn't true. This is different than corruption panics since those deal with *hardware* assumptions.

This is a reasonable thing to include because programs will sometimes want to take advantage of some conjectured theorem and aren't capable or don't have the resources to prove it true. If a program author is willing to risk the possibility of a panic if some conjecture isn't true then they should be able to do so, and have those panics signaled differently than other panics.

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

## Incremental compilation as widely as possible

[Incremental compilation](https://blog.rust-lang.org/2016/09/08/incremental.html) is a critical technique to ensure most compilation/type checking runs are reasonably fast. This is a very common technique in normal programming languages, but it [doesn't seem to have been implemented widely in proof assistants](https://proofassistants.stackexchange.com/questions/335/what-is-the-state-of-recompilation-avoidance-in-proof-assistants).

In proof assistants that heavily use automated tactics one of the most expensive parts of proof checking is actually running the automated tactics to discover proofs, since those tactics often have to walk a very large search space before they successfully find the right proof terms. Although bare metal tactics/metaprogramming and the computational reflection discussed in the above section will mitigate some of this cost, it still makes sense to avoid rerunning tactics or rechecking proofs if none of their dependencies have changed.

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

Although in a dependent type theory a subset type is absolutely a strictly different type than a normal constructed value, we can make life easier by providing syntax to define and quickly pull values in and out of subset types. I call these cheap representations of subset types "asserted types".

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

This same syntax makes sense to declare trait requirements on types as well:

```
def my_function<T & Orderable>(t: T):
  ...
```

Asserted types are simply a broader variant of [liquid types](https://goto.ucsd.edu/~rjhala/liquid/liquid_types.pdf), so it should be possible to infer annotations and invariants in many situations, as is done in ["Flux: Liquid Types for Rust"](https://arxiv.org/abs/2207.04034).

## Cargo-like tooling

There's no reason to not make the tooling awesome!

## Metaprogramming instead of custom Notation

Coq's [Notation system](https://coq.inria.fr/refman/user-extensions/syntax-extensions.html) is extremely convoluted. It essentially allows creating arbitrary custom parsers within Coq. While this may seem like a good thing, it's a bad thing. Reasoning about these custom parsing and scoping rules is extremely difficult, and easy to get wrong. It adds a huge amount of work to maintain the system in Coq, and learn the rules for users.

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

what's the difference between a bit array defined Logic Magmide but computationally represented in the smart packed format, and a real bit array? there's no difference at all, at least between a particular concrete one.
 -->
<!--
However there are some subtleties we have to contend with since Magmide is so inherently intended for verification of *real* computational programs.
The kernel has to be actually *implemented* in some real computational language, and we'd prefer it was a maximally performant one. Also, metaprogramming of all kinds, whether manipulating Logic terms or anything else, also has to be implemented in a real computational language. These might as well be the same language. This language needs to be one that can be run on *development* machines, the ones that will compile whatever final artifacts. Let's define the term Host to refer to this aspect.

So the final compiler will be a binary artifact runnable on some collection of host architectures. This artifact will have a few components:

parser, capable of parsing Magmide, metaprogramming constructs, and any other constructs we choose to include in the shipped language syntax, all into Host data structures.
proof checking kernel, which accepts some Host data structure representing Logic terms.
metaprogramming checker/runner. the compiler has builtin definitions and models of Host, so it can take AST structures representing Host and check them (Host likely includes syntax to make assertions about state, which are implicitly predicates over binary arrays), render/assemble them to some place in memory or a file, and jump to them to execute them (possibly having provided arguments by fulfilling whatever calling convention)


the magmide compiler is a program that can operate in any specific machine of a universe of machines that have been modeled at the time of the compiler being compiled. this universe of machines has been modeled with some kind of with input/output capabilities and probably some concepts of operating system services such a filesystem. so Host can include functions to write to files, and can expose functions for core concepts such as rendering compilation artifacts (probably accepting custom AST/assertions/checkers/renders etc)
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
