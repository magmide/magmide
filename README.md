# **WARNING! :warning: :construction: Rok is purely a research project at this point, and isn't ready to be used! :construction: :warning:**

**The following documentation is written as if the project were complete and production ready. This is just to help me understand the project objectives and hammer out the interface. Feedback and contributions are welcome!**

# Rok

> Correct, Fast, Productive: pick three.

Rok is a dependently-typed, metaprogrammable, abstract assembly language with token effects. This means it's the first and only language that brings together these capabilities:

- Fully Verifiable: Rok has an embedded dependently-typed proof checker much like [Coq]() or [Lean](). This means any logical property provable within the [Calculus of Constructions]() can be stated and proven in Rok, including the correctness of programs.
- Bare Metal Performance: Rok's internal library includes types and theorems formalizing [Von Neumann computation]() and assembly language execution, allowing it to be used to write and verify programs at the lowest level of software abstraction. This means even the most daring and high performance programs can be written, proven correct, and compiled in the same tool.
- Infinitely Flexible: Rok has extremely powerful and yet simple metaprogramming, allowing manipulation of proofs, functions, and data at compile time. Write verified proof tactics, plugins, and even embedded higher-level programming languages within Rok.

This combination of capabilities opens up possibilities we've only dared to imagine. Our limits in designing software have mostly been defined by the immense difficulty of safely and correctly composing code together, but using Rok any code can be arbitrarily composed. The basic assumptions of software architecture can be entirely reexamined and we can finally let our imaginations lead the way.

## Who is Rok for?

Rok has the absurdly ambitious goal of being a new universal substrate for all software! Since Rok is an *abstract* assembly language, it can theoretically compile correct programs for even the most obscure Von Neumann environments. The long term goal is for Rok to be used for embedded devices, normal application software, web programs, etc.

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
                 and proves properties
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


