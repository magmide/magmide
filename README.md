# **WARNING! :warning: :construction: Rok is purely a research project at this point, and isn't ready to be used! :construction: :warning:**

The following file is an introduction/tutorial intended for normal software engineers rather than experts in formal verification. **It is written as if the project were complete and production ready!** This is just to help me understand the project objectives and hammer out the interface. Feedback and contributions are welcome!

If you want to be convinced Rok would solve an important problem and has the right design to tractably do so, please read [What is Rok and Why is it Important?]()

If you want a technical description of the intended internal design of the Rok compiler/language intended for formal verification researchers, please read [The Technical Design of Rok]().

# Rok

> Correct, Fast, Productive: pick three.

Rok is a metaprogrammable dependently-typed language with an integrated abstract assembly language with trackable effects. This means it's the first and only language that brings together these capabilities:

- Fully Verifiable: Rok has an embedded dependently-typed proof checker much like [Coq]() or [Lean](). This means any logical property provable within the [Calculus of Constructions]() can be stated and proven in Rok, including the correctness of programs.
- Bare Metal Performance: Rok's internal library includes types and theorems formalizing [Von Neumann computation]() and assembly language execution, allowing it to be used to write and verify programs at the lowest level of software abstraction. This means even the most daring and high performance programs can be written, proven correct, and compiled in the same tool.
- Infinitely Flexible: Rok has extremely powerful and yet simple metaprogramming, allowing manipulation of proofs, functions, and data at compile time. Write verified proof tactics, plugins, and even embedded higher-level programming languages within Rok.

This combination of capabilities opens up possibilities we've only dared to imagine. Our limits in designing software have mostly been defined by the immense difficulty of safely and correctly composing code together, but using Rok any code can be arbitrarily composed. The basic assumptions of software architecture can be entirely reexamined and we can finally let our imaginations lead the way.

## Who is Rok for?

Rok has the absurdly ambitious goal of being a new universal substrate for all software! Since Rok is an *abstract* assembly language, it can theoretically compile correct programs for even the most obscure Von Neumann environments. The long term goal is for Rok to be used for embedded devices, normal application software, web programs, etc.

## Basics of Compute Rok

First let's get all the stuff that isn't unique about Rok out of the way. Rok has both a "Computational" language and a "Logical" language baked in. The Computational language is what we use to write programs that will actually run on some machine, and the Logical language is used to logically model data and prove things about programs.

The Computational language is technically defined as a raw assembly language, but since programming in assembly is extremely tedious, the default way to write computational code is with `core`, a language a lot like Rust.

```rok
// single line comments use double-slash
//
  comments can be indented
  so you can write them
  across as many lines
  as you like!

  `core` is whitespace sensitive,
  so you indentation is used to structure the program
  instead of curly braces

// the main function is the entry point to your program
fn main;
  // immutable variables are declared with let:
  let a = 1
  // a = 2 <-- compiler error!
  // variables can be redeclared:
  let a = 2

  // types are inferred, but you can provide them:
  let b: u8 = 255

  // mutable variables are declared with mut:
  mut c = 2
  c = 1
  // and they can be redeclared:
  mut c = 3
  let c = 2

  // booleans
  let b: bool = true

  // standard signed and unsigned integers
  let unsigned_8_bits: u8 = 0
  let unsigned_8_bits: u8 = 0

  // floating point numbers
  let float_32_bits: f32 = 0.0
  let float_64_bits: f64 = 0.0

  // arrays
  // slices
  // tuples

  // core is literally just a "portable assembly language",
  // so it doesn't have growable lists or strings by default!
  // think of core in the same way as `no_std` in rust
  // we hope rust itself will someday be reimplemented and formally verified using rok!

// the type system is very similar to rust
// you can declare type aliases:
alias byte; u8

// you can declare new nominal types as structs:
type User;
  id: usize
  age: u8
  active: bool
type Point; x: f64, y: f64

// or unit
type Token
type Signal

// or tuples
type Point; f64, f64
type Pair;
  i32
  i32

// or discriminated unions
type Event;
  | PageLoad
  | PageUnload
  | KeyPress; char
  | Paste; [char]
  | Click; x: i64, y: i64
// on which you can use the match command
fn use_union event: Event;
  match event;
    PageLoad;
    PageUnload;
    Click x, y;
    _; ()

  // the is operator is like "if let" in rust
  if event is KeyPress character;
    print character
  // and you can use it without destructuring?
  if event is Paste;
    print event.1

// and they can be generic
type Pair T, U; T, U
type NonEmpty T;
  first: T
  rest: [T]
```

But the entire point of Rok is that you can prove your program is correct! How do we do that?

The most common and simplest way we can make provable assertions about our programs is by enhancing our types with *subset predicates*. If we want to guarantee that a piece of data will always meet some criteria, we can make assertions about it with the `&` operator. Then, any time we assign a value to that type, we have to fulfill a *proof obligation* that the value meets all the assertions of the type. More on proofs in a second.

```
// this type will just be represented as a normal usize
// but we can't assign 0 to it
alias NonZero; usize & > 0

// we can add as many assertions as we like
// even using generic values in them
alias Between min max; usize & >= min & <= max

// the & operator essentially takes a single argument function,
// so we can use the lambda operator
alias Above min; usize & |> v; v > min

// or we can use the "hole" _ to indicate the value in question
alias Above min; usize & _ > min

// this works for tuples and structs too
// the "dot" . is implied to act on the value,
// and fields can refer to each other
alias Range; i32, i32 & > .1

type Person;
  age: u8
  // here the value of is_adult
  // has to line up with .age >= 18
  is_adult: bool & == .age >= 18
  // this pattern of requiring a bool
  // to exactly line up with some assertion
  // is common enough to get an alias
  is_adult: bool.exact (.age >= 18)
```

So how do we actually prove that our program actually follows these data assertions? Can the compiler figure it out by itself? In many simple situations it actually can! But it's literally impossible for it to do so in absolutely all situations (if it could, the compiler would be capable of solving any logical proof in the universe!).

To really understand how this all works, we have to get into the Logical side of Rok, and talk about `Ideal`, `Prop`, and The Calculus of Constructions.

## Logical Rok

First let's start with the `Ideal` type family. `Ideal` types are defined to represent *abstract*, *logical* data. They aren't intended to be represented on real computers, and their only purpose is to help us define logical concepts and relate them to our real computable data. Alongside the `Ideal` type family is a whole separate programming language, one that's *pure* and *functional*. Why pure and functional? Simply, pure and functional languages relate directly to mathematical type theory (mathematical type theory is nothing but a pure and functional language!). It's much easier to define abstract concepts and prove things about them in pure and functional settings than the messy imperative way real computers work. Otherwise we'd have to deal with distracting details about memory layout, bit representation, allocation, etc. The "programs" we write in this pure functional language aren't actually intended to be run! They just define abstract algorithms that model real computation, so we only care about them for their type-checking behavior and not their real behavior.

The type system of logical Rok is shaped a lot like computational Rok to make things convenient. But the big difference between types in logical Rok and computational rok is how they handle type recursion.

```
// in computational Rok types must be representable in bits and have a finite and knowable size,
// meaning that they can't reference themselves without some kind of pointer indirection
type NumLinkedList T;
  item: T
  next: *(NumLinkedList T)?

// but in logical rok there's no such restriction, since these types are abstract and imaginary
idl List T;
  item: T
  next: List T
```


Logical Rok only really needs three things to prove basically all of mathematics and therefore model computation and prove programs correct:

- Inductive types, which live in one of two different type "sorts":
  - `Ideal`, the sort for "data" (even if it's abstract imaginary data).
  - `Prop`, the sort for "propositions", basically assertions about data.
- Function types.


So how can we prove things in a programming language? How does that make any sense? You'll be surprised to hear that you already write proofs all the time!

Think about when you define a data type, such as `type Num; u64`. Any time you construct a value of `Num` by calling the `Num` constructor with a `u64` value (`Num 8`), you're *proving* that some `Num` exists. You haven't proven something very *interesting*, but you've proven something nonetheless. It's even possible to define types that *can't possibly* be constructed, such as an empty union: `type Empty; types.union []`. When you try to actually create a value of `Empty`, you can't possibly do so, meaning that this type is impossible or "False".

In the same way, when you define a function, you're creating a *proof* that the input types of the function can somehow be transformed into the output type of the function. For example this dumb little function: `|> n: u8; n == 0` has type `u8 -> bool`, so the function *proves* that a `u8` can always be transformed into a `bool`. In this way, the `->` in function types can be understood as *both* a computational transformation *and* the implication operator from logic (if this is true then that is true, `P -> Q`). The only problem with `u8 -> bool` is that it isn't a proof of anything very interesting! It's really easy to transform a `u8` into a `bool` (`|> _; true`, `|> _; false`, `|> n; n == 9`). The simple type of `bool` gives us basically no information.

But if we enhance our language with *dependent types*, we can start doing really interesting stuff. Let's start with a function whose *type* proves that its input is equal to 5. We've already introduced asserted types, so let's define our own type to represent that idea, and a function that uses it

```
type equal_5 number;
  | yes & (number == 5)
  | no & (number != 5)

fn equal_to_5 number: u8 -> equal_5 number;
  return if number == 5; give yes; give no
```

Pretty simple! The abilty to *dependently* reference the input `number` in the output type makes this work, and because the assertions we're making are so simple the compiler is able to prove they're consistent without any extra work from us. We don't even have to define our own `equal_5` type, since `bool` is already generic over these kinds of assertions, along with a few other standard library types like `Optional` and `Fallible` that are commonly used to assert something about data.

```
// bool can take a true assertion and a false assertion
fn equal_to_5 number: u8 -> bool (number == 5) (number != 5);
  return number == 5

// we can also use the alias for this concept
fn equal_to_5 number: u8 -> bool.exact (number == 5);
  return number == 5
```

But something about the above assertions like `number == 5` and `number != 5` might bother you. If proofs are *just data*, then where do `==` and `!=` come from? Are they primitive in the language? Are they just data as well?

Indeed they are! But specifically, they're data that live in the `Prop` sort. `Prop` is the sort defined to hold logical assertions, and the rules about how its types are defined make it specially suited to that task.

Let's define a few of our own `Prop` types to get a feel for how it works.

```
// in the computational types, unit or `()` is the "zero size" type, a type that holds no data
alias MyUnit = ()
type NominalUnit

// we can define a prop version as well!
prop PropUnit
// this type is "trivial", since it holds no information and can always be constructed
// in the standard library this type is called "always", and in Coq it's called "True"
alias MyAlways = always

// we already saw an example of a computational type that can't be constructed
type Empty; types.union []
// and of course we can do the same in the prop sort
prop PropEmpty; types.union []
// this type is impossible to construct, which might seem pointless at first, but we'll see how it can be extremely useful later
// in the standard library its called "never", and in Coq it's called "False"
alias MyNever = never
```

```
// since we're providing default assertions,
// the normal form of bool only asserts the useless `always`
type bool when_true = always, when_false = always;
  | true & when_true
  | false & when_false

// you'll notice we don't bother with an assertion for T
// since the user can just provide a asserted type themselves
type Optional T, when_none = always;
  | Some; T
  | None & when_none

// same thing here
type Fallible T, E;
  | Ok; T
  | Err; E
```




The key insight is in understanding *The Curry-Howard Correspondence* and the concept of *Proofs as Data*. These are a little mind-bending at first, but let's go through it.

A good way to understand this is to see *normal* programming in a different light.


```

```



In real programming languages we cheat by allowing the programmer to throw exceptions or crash the program if they run into a situation


Basically, any type that lives in the `Prop` sort is *by definition* a type that represents a truth value, a logical claim.

Proofs are *all* defined by constructors for data, it's just data that lives in a special type sort, specifically the type sort `Prop`. First we define some type that defines data representing some logical claim, and then when we want to actually *prove* such a claim, we just have to *construct* a value of that type!

It's important to notice though that this wouldn't be very useful if the type system of our language wasn't *dependent*, meaning that the type of one value can refer to any other separate value in scope. When we put propositions-as-data together with dependent types, we have a proof checker.

This is the key insight. When we make any kind of logical claim, we have to define *out of nowhere* what the definition of that claim is. Then, when we want to provide a

So for example, if we wanted to create

```
prop MyTrue
// that's it! all we have to do to




```


```
// we can define new ideal types in much the same way we define new computational types,
// only using the `idl` keyword instead of `type`

// all types declared with idl are nominal
idl MyUnit

// we can also reuse the alias keyword for logical types
alias MyUnit; logical.unit


```


















## Abstract assembly language

Here's an example of a Rok program in the "core" assembly language that is general enough to compile to basically any architecture.

Rok itself ships with a few different layers of computational language:

- Thinking about computation in general.
- Thinking about a specific collection of generalizable instructions in an unknown machine. This means you're reasoning about specific calling conventions.
- Thinking about blocks with "function arguments"

- `asm_zero`: a truly representational abstract assembly language, used to define the "common core" of all supported architectures
- `asm_one`: the next level of abstraction, with type definitions and sugars, and llvm style function along with call/ret instructions. must instantiate with a calling convention
- `core`: a c-like language with normal functions, match/if/for/while/loop/piping structures, functions for malloc/free, but no ownership/lifetime stuff. must instantiate with a calling convention and definitions for malloc/free in the desired environment
- `system_core`: same c-like language, but with assumptions of "system" calls for thread spawn/join, io, async, etc


There can be a `call` instruction that takes a label or address and together with a `ret` instruction abstracts away the details of a calling convention. We assume it does whatever is necessary under the calling convention to set the return address and push arguments to wherever they go.


https://cs61.seas.harvard.edu/site/2018/Asm1/
all labels and global static data are accessed relative to the current instruction pointer (or at least they should be to produce a safe position independent executable). so when assembling to machine code, the distance between an instruction accessing something and that thing is computed

https://cs61.seas.harvard.edu/site/2018/Asm2/
A `push X` instruction pushes the variable X onto the stack, which changes the stack pointer (either up or down depending on the stack convention, and it will mostly do this the same amount since X must fit into a word??) and moves `X` into that location

so `push` (`pop` is opposite)

```
add 8, %rsp // could be sub if stack grows downwards
mov X, (%rsp)
```



```
define i32 @add1(i32 %a, i32 %b) {
entry:
  %tmp1 = add i32 %a, %b
  ret i32 %tmp1
}

define i32 @add2(i32 %a, i32 %b) {
entry:
  %tmp1 = icmp eq i32 %a, 0
  br i1 %tmp1, label %done, label %recurse

recurse:
  %tmp2 = sub i32 %a, 1
  %tmp3 = add i32 %b, 1
  %tmp4 = call i32 @add2(i32 %tmp2, i32 %tmp3)
  ret i32 %tmp4

done:
  ret i32 %b
}
```


- The logical inductives/theorems/functions that define von neumann computation and instruction assembly, as well as concurrent separation logic. This layer is the most abstract and could be instantiated with any specific von neumann machine, even an abstract one.
- `core.asm`. A collection of instruction types that should be generalizable to any machine. At
- `core`.




```
use core

core.program@
  main:



```


perhaps given all arguments then conclusion is a better syntax for implications, for readability



## How does Rok work?

The logical language where proofs are conducted is in concert with the concrete language where computation is done. The computational language defines the instructions that perform type(proof)-checking and manipulate proof terms. But then proof terms justify the computational types of the concrete language, and are used to define the instructions that are then assembled into real programs.

The Rok compiler is a program, whose source is written in the Rok abstract assembly language (but of course any part of it can be *actually* written in some embedded language and then unfolded metaprogramatically to the abstract assembly language)
This program includes definitions for the basic ast of Rok. This ast is almost entirely the (path-based) module system, and all the logical stuff (coq equivalents). The abstract assembly language is then entirely defined within this logical language, and metaprogrammatically converted

So you could possibly say that the "object" language is the logical proof one, and the "meta" language is the concrete computational one. However the "object" language has an unusual link back to the "meta" language, since the meta language is defined and proven in terms of the object language.

```
                    represents and
                      manipulates
    +------------------------------------------+
    |                     |                    |
    |                     |                    |
    v                     |                    |
Logic Rok                 +-------------> Compute Rok
    |                                          ^
    |                                          |
    |                                          |
    +------------------------------------------+
                   logically defines
                      and verifies
```


The only things the compiler needs to function are:

- the `use` keyword
- ability to parse `use` keywords and the basic metaprogrammatic capture syntax *and nothing else*. all the other stuff can just be captured with the capture primitives and then processed with libraries. however it's silly to have that extra level of indirection for the "base" languages. the logical language and "preferred" computational language can both be "primitive" from the perspective of the parser, even if they aren't truly primitive from a logical perspective.
- libraries to perform more fine-grained parsing of the logical language and do type-checking etc.
- a backend to assemble/render instructions
- definitions of types/instructions enough to do all of those above things


The final language will have the logical subset and a rust-like high-level computational subset that aligns nicely with the logical language but is imperative and stateful.


## Module system

```
// use a module whose location has been specified in the manifest
// the manifest is essentially sugar for a handful of macros
use lang{logic, compute}

// the libraries 'lang', 'core', and 'std' are spoken for. perhaps though we can allow people to specify external packages with these names, we'll just give a warning that they're shadowing builtin modules

// use a local module
// files/directories/internal modules are all accessed with .
// `__mod.rk` can act as an "module entry" for a directory, you can't shadow child files or directories
// the `mod` keyword can create modules inside a file, you can't shadow sibling files or directories
// `_file.rk` means that module is private, but since this is a verified language this is just a hint to not show the module in tooling, any true invariants should be fully specified with `&`
use .local.nested{thing, further{nested.more, stuff}}

// can do indented instead
use .local.nested
  thing
  further{nested.more, stuff}
  whatever
    stuff.thingy

// goes up to the project root
use ~local.whatever

// the module system allows full qualification of libraries, even to git repositories
// the format 'name/something' defaults to namespaced libraries on the main package manager
// a full git url obviously refers to that repo
use person/lib.whatever

// the above could be equivalent to:
let person_lib = lang.pull_lib$(git: "https://github.com/person/lib")
use person_lib.whatever
```


```
use lang.{ logic, compute }

// all inductive definitions use the `ind` keyword
// the different kinds of types are included by default and automatically desugared to be the more "pure" versions of themselves

// a union-like inductive
ind Day
  | monday | tuesday | wednesday | thursday
  | friday | saturday | sunday

// a record-like inductive
ind Date
  year: logic.Nat
  month: logic.Nat & between(1, 12)
  day: logic.Nat

// a tuple-like inductive
ind IpAddress; logic.Byte, logic.Byte, logic.Byte, logic.Byte

// the same as above but with a helper macro
ind IpAddress; logic.tuple_repeat(logic.Byte, 4)

// a unit-like inductive
ind Unit

rec next_weekday day
  // bring all the constructors of Day into scope
  use Day.*
  match day
    monday; tuesday, tuesday; wednesday, wednesday; thursday, thursday; friday
    friday; monday, saturday; monday, sunday; monday


let next_weekday_computable = compute.logic_computable(next_weekday)
let DayComputable = compute.type(next_weekday_computable).args[0].type

dbg next_weekday_computable(DayComputable.monday)
// outputs "Day.tuesday"


// what if we were define the above types and function in the computable language?
// it's as simple as changing "ind" to "type", "rec" to "fn", and ensuring all types are computable
// all of these "creation" keywords are ultimately just some kind of sugar for a "let"

type Day
  | monday | tuesday | wednesday | thursday
  | friday | saturday | sunday

type Date
  year: u16
  month: u8 & between(1, 12)
  day: u8

type Name; first: str, last: str

type Pair U, T; U, T

type IpAddress; u8, u8, u8, u8

type IpAddress; compute.tuple_repeat(u8, 4)

type Unit

fn next_weekday day
  use Day.*
  // a match implicitly takes discriminee, arms, proof of completeness
  match day
    monday; tuesday, tuesday; wednesday, wednesday; thursday, thursday; friday
    friday; monday, saturday; monday, sunday; monday

// now no need to convert it first
dbg next_weekday(Day.monday)
// outputs "Day.tuesday"
```

In general, `;` is an inline delimiter between tuples, and `,` is an inline delimiter between tuple elements. Since basically every positional item in a programming language is a tuple (or the tuple equivalent record), the alteration of these two can delimit everything. Note these are only *inline* delimiters, indents are the equivalent of `;` and newlines are the equivalent of `,`.
Why `;`? Because `:` is for type specification.

`==` is for equality, and maps to the two different kinds of equality if it's used in a logical or computational context.


### trait system in rokrs
don't need an orphan rule, just need explicit impl import and usage. the default impl is the bare one defined alongside the type, and either you always have to manually include/specify a different impl or its a semver violation to add a bare impl alongside a type that previously didn't have one



### example: converting a "logical" inductive type into an actual computable type

### example: adding an option to a computable discriminated union

### example: proving termination of a

## The embedded `core` language


## Metaprogramming

Known strings given to a function
Keyword macros





Instead of defining an extremely complicated set of macro definition rules, metaprogramming in Rok chooses to give three very simple "syntactic entrypoints", and then just expose as much of the compiler query api as possible.

There are three ways to "capture" program text and have it processed at compile time:

### Inline

Any inline segment of program text can be captured in single quotes and processed with a function, similar to [javascript tagged templates](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Template_literals#tagged_templates).

```
let query = sql$'select * from t'
```

Here the `sql` function would receive the raw text `select * from t` and information about what location in the program this occurs in, and could then parse and transform it.

### Block

An indented block of program text can be captured with the `|'` operator:

```
let program = py|'
  for i in range(10):
    n = i ** 2
    print(n)
```

Here the `py` function would


This basic


### Import

A `use` clause can refer to any kind of file, and using a metaprogramming function process the text of that file.

```
use query from sql'./path/to/file'
```



## Getting started

Rok has been heavily inspired by Rust and its commitment to ergonomic tooling and straightforward documentation.

```bash
# install rok and its tools
curl --proto '=https' --tlsv1.2 -sSf https://sh.rokup.dev | sh

# create a new project
rok new hello-world
cd hello-world

rok check [entry]
rok run [entry]

# targets in rok are really just definitions of other "machines", including their environmental assumptions
rok target add
```

## A basic program



## Writing proofs


