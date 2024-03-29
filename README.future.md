# Magmide

> Correct, Fast, Productive: pick three.

Magmide is the first language built from the ground up to allow software engineers to productively write extremely high performance software for any computational environment, logically prove the software correct, and run/compile that code all within the same tool.

The goal of the project is to spread the so-far purely academic knowledge of software verification and formal logic to a broad audience. It should be normal for engineers to create programs that are truly correct, safe, secure, robust, and performant.

This file is a "by example" style reference for the features and interface of Magmide. It doesn't try to explain any of the underlying concepts, just document decisions, so you might want to read one of these other resources:

- If you want to be convinced the goal of this project is both possible and necessary, please read [What is Magmide and Why is it Important?]()
- If you want to learn about software verification and formal logic using Magmide, please read [Intro to Verification and Logic with Magmide]().
- If you want to contribute and need the nitty-gritty technical details and current roadmap, please read [The Technical Design of Magmide]().

## Install and Use

Magmide is heavily inspired by Rust and its commitment to ergonomic tooling and straightforward documentation.

```bash
# install magmide and its tools
curl --proto '=https' --tlsv1.2 -sSf https://sh.magmide.dev | sh

# create a new project
magmide new hello-world
cd hello-world

magmide check <entry>
magmide run
magmide build
```

## Syntax

Here's what we can do

calling is just placing things next to each other with no commas. an *explicit* comma-separated list is always a tuple, which is why function arguments are always specified that way
piping style calling uses `>functionname`. it seems that because of precedence and indentation rules which expressions are function names is always inferable?
this works inline too, so `data>functionname` or `data >infix something`
`>> arg arg2; expr` defines an anonymous function and immediately calls it in piping style. `>>;` is then the equivalent of your old `do` idea
`--` is the "bumper" for an indented expression
the sections of keywords are delimited by semicolons
nested function calls are just indented since function calling is
`/` is the *keyword continuation operator*, so all keywords, even possibly multi-line ones, can be defined metaprogramatically within the language

```
if yo; --
  function_name arg arg
  >whatevs
  >another thing
  >> something; yo different something
  >> hm; abb >hm diff
/elif yoyo; whatevs
/else; dude

if yo; yoyo /else; dude

let thingy = if some >whatevs hmm; dude /else; yo
```

piping custom keywords can be done with a leading `;`? and standalone statement style ones are something else like `$`?
custom keywords are called with a leading `;`? so something like `;route_get yoyo something; whatevs /err; dude`

calling macros/known functions is indicated with something like a `~` or just the backtick thing? which means it can be done

include the "backpassing" idea? or simplify it by somehow creating an "implicit callback defining pipe operator?" such as `>>>`?






Magmide is whitespace/indentation sensitive.
Anywhere a `;` can be used an opening indent can be used *additionally*.
Anywhere a `,` can be used a newline can be used *instead*.
The `:` operator is always used in some way to indicate type-like assertions.
Precedence is decided using nesting with parentheses or indentation and never operator power.
"Wrapping" delimiters are avoided.
"Pipeability" is strongly valued.
Operators are rarely used to represent actions that could be defined within the language, and instead prioritize adding new capabilities.

```
// defining computational types
data Unit
data Tuple;


data Macro (S=undefined);
  | Block; BlockMacroFn
  | Function; FunctionMacroFn
  | Decorator; DecoratorMacroFn
  | Import; ImportMacroFn(S)


alias SourceChannel S; Dict<S> -> void

fn non_existent_err macroName: str; str, str;
  return "Macro non-existent", "The macro "${macroName}" doesn't exist.

fn incorrect_type_err
  macroName: str
  macroType: str
  expectedType: str
;
  str
  str
;
  return "Macro type mismatch", "The macro "${macroName}" is a ${macroType} type, but here it's being used as a ${expectedType} type."

data CompileContext S;
  macros: Dict(Macro(S))
  fileContext: FileContext
  sourceChannel: SourceChannel(S)
  handleScript: { path: str source: str } -> void
  readFile: str -> str | undefined
  joinPath: ..str -> str
  subsume: @T -> SpanResult<T> -> Result<T, void>
  Err: (ts.TextRange, str, str) -> Result<any, void>
  macroCtx: MacroContext

data MacroContext;
  Ok: @T, (T, SpanWarning[]?) -> SpanResult<T>
  TsNodeErr: (ts.TextRange, str, ..str) -> SpanResult<any>
  Err: (fileName: str, title: str, ..str) -> SpanResult<any>
  tsNodeWarn: (node: ts.TextRange, str, ..str[]) -> void
  warn: (str, str, ..str[]) -> void
  subsume: @T, SpanResult T -> Result T, void


data u8; bitarray(8)

ideal Day;
  | monday | tuesday | wednesday | thursday
  | friday | saturday | sunday

  use Day.*

  rec next_weekday day: Day; match day;
    monday; tuesday, tuesday; wednesday, wednesday; thursday, thursday; friday
    friday; monday, saturday; monday, sunday; monday

ideal Bool;
  | true
  | false

  use Bool.*

  rec negate b: Bool :: bool;
    match b;
      true; false
      false; true

  rec and b1: bool, b2: bool :: bool;
    match b1;
      true; b2
      false; false

  rec or b1: bool, b2: bool :: bool;
    match b1;
      true; true
      false; b2

  impl core.testable;
    rec test b: Bool :: bool;
      match b; true; testable.true, false; testable.false

  rec negate_using_test b: Bool :: bool;
    test b;
      false
      true


ideal IndexList<A: ideal> :: nat;
  | Nil :: IndexList(0)
  | Cons :: @n A IndexList(n) -> IndexList(n;next)

  rec append n1, ls1: IndexList(n1), n2, ls2: IndexList(n2) :: IndexList(n1 ;add n2);
    match ls1;
      Nil; ls2
      Cons(_, x, ls1'); Cons(x, append(ls1', ls2))

prop even :: nat;
  | zero: even(0)
  | add_two: @n, even(n) -> even(n;next;next)

  use even.*
  thm four_is: even(4); prf;
    + add_two; + add_two; + zero

  thm four_is__next: even(4); prf;
    + (add_two 2 (add_two 0 zero))

  thm plus_four: @n, even n -> even (4 ;add n); prf;
    => n; >>; => Hn;
    + add_two; + add_two; + Hn

  thm inversion:
    @n: nat, even n -> (n = 0) ;or (exists m; n = m;next;next ;and even m)
  ; prf;
    => n [| n' E']
      left; _
      --
        right; exists n'; split
        _; + E'

```



## Metaprogramming

## Interactive Tactic Mode



## Module system

```
// use a module whose location has been specified in the manifest
// the manifest is essentially sugar for a handful of macros
use lang{logic, compute}

// the libraries 'lang', 'core', and 'std' are spoken for. perhaps though we can allow people to specify external packages with these names, we'll just give a warning that they're shadowing builtin modules

// use a local module
// files/directories/internal modules are all accessed with .
// `__mod.mg` can act as an "module entry" for a directory, you can't shadow child files or directories
// the `mod` keyword can create modules inside a file, you can't shadow sibling files or directories
// `_file.mg` means that module is private, but since this is a verified language this is just a hint to not show the module in tooling, any true invariants should be fully specified with `&`
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


### trait system in host magmide
don't need an orphan rule, just need explicit impl import and usage. the default impl is the bare one defined alongside the type, and either you always have to manually include/specify a different impl or its a semver violation to add a bare impl alongside a type that previously didn't have one



### example: converting a "logical" inductive type into an actual computable type

### example: adding an option to a computable discriminated union

### example: proving termination of a

## The embedded `core` language


## Testing

talk about quickcheck and working up to a proof

## Metaprogramming

Known strings given to a function
Keyword macros

