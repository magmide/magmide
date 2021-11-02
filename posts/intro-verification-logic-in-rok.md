<!-- examples tell *how*, words explain *why* -->

Hello!

If you're reading this, you must be curious about how it could be possible to write truly *provably correct* programs, ones that you can have the same confidence in as proven theories of mathematics or logic. You likely want to learn how to write verified software yourself, and don't have time to wade through unnecessarily clunky academic jargon or stitch together knowledge scattered in dozens of obscure journal papers.

You're in the right place! Rok has been designed from the ground up to be usable and respect your time, to enable you to gain this incredibly powerful and revolutionary skill.

I hope you're excited! I powerfully believe verified software will bring in the next era of computing, one in which we don't have to settle for broken, insecure, or unpredictable software.

Here's the road ahead:

First we'll take a glimpse at some Rok programs, both toys and more useful ones, just to get an idea of what's possible and how the language feels. We'll take a surface level tour of Compute Rok, the procedural portion of the language we'll use to actually write programs.

Then we'll dive into Logic Rok, the pure and functional part that is used to make and prove logical claims:

- We'll talk about why it's necessary to use a pure and functional language at all (I promise I'm not a clojure fanboy or something).
- How to code in Logic Rok, what it feels like to write pure functional algorithms and how it's different than normal programming.
- A short overview of formal logic, and some comparisons to normal programming.
- Type Theory, The Calculus of Constructions, and the Curry-Howard Correspondence, the big important ideas that make it possible for a programming language to represent proofs.
- How to actually make and prove logical claims (it's getting good!), along with some helpful rules of thumb.

Now with a working knowledge of how to use Logic Rok, we can use it to verify our real Compute Rok programs!

- Separation Logic, the logical method that helps us reason about ownership, sharing, mutation, and destruction of finite computational resources.
- Writing proofs about Compute Rok functions and data structures.
- Logical modeling, or proving some kind of alignment between a pure functional structure and a real computational one.
- Testing as a gradual path to proofs, using randomized conjecture-based testing.
- Trackable effects, the system that allows you to prove your program is free from unexpected side-effects such as memory unsafety, infinite loops, panics, and just about anything else.

And then finally all the deeper features that make Rok truly powerful:

- Metaprogramming in Rok, the capabilities that allow you to write your own compile-time logic.
- Some basic programming language and type-system theory.
- A short overview of basic computer architecture, including assembly language concepts.
- The lower assembly language layers of Compute Rok, and how to "drop down" into them.
- The abstract machine system, and how Rok can be used to write and prove programs for any computational environment.
- A deeper look at Iris and Resource Algebras, the complex higher-order Separation Logic that makes Trackable Effects and lots of other things possible.

Throughout all of these sections, we'll do our best to not only help you understand all these concepts, but introduce you to the way academics talk about them. We'll do so in a no-nonsense way, but we think it's a good idea to make sure you can jump into the original research if you want and not have to relearn all the "formal" names for concepts you already understand.

Let's get to it!

## Example Programs and a Tour of Compute Rok

<!--
  - hello world
  - the code and proofs for a verified implementation of something small, like a verified growable list or arbitrary size integer, probably including but hand-waving the purely logical model. this will use asserted types
  - a Compute Rok metaprogramming tease, something cool like the surface level use of a sql-like api to operate on raw data structures
-->

## Logic Rok, How to Prove Things in a Programming Language

### Why pure and functional?

There are quite a few pure and functional languages, such as [haskell]() and [clojure]() and [lisp]() and [racket]() and [elm](). What makes them different? Functional languages enforce two properties, with varying degress of strictness:

- All data is immutable. There is no ability to mutate data structures, only create new structures based on them. Although most functional languages have some [cheating escape hatches]() for when it's *really* necessary to mutate something.
- All functions are pure, meaning that if you pass the exact same inputs into them, you always receive the exact same inputs. This means you can't perform "impure" actions such as mutate a variable that wasn't passed into the function (remember, you can't mutate *anything*!), or create side effects such as reaching out to the surrounding system by doing things like file or network operations. Since programs that couldn't interface with the surrounding system *at all* would be completely worthless, functional languages have special runtime functions that allow you to interact with the system by passing them pure functions. But they all return some kind of "side effect monad", a concept we don't need to talk about here!

Now, those two properties have some nice consequences. They mean that you can't accidentally change or destroy data some other part of the program was depending on, or get surprised about the complex ways different parts of your program interact with each other, or not realize some function was actually doing expensive network operations at a time you didn't expect.

But the especially important consequence of purity and immutability is that a program is *simple*, at least from a logical perspective. Every function always outputs predictable results based only on inputs, no complex and difficult to reason about webs of global mutable state are possible, the language operates as if it were simply math or logic, where everything has a precise definition that can be formally reasoned about.

There's just one big obvious problem: **all that purity and immutability is a lie!**

When a computer is running, the *only thing* it's doing is mutating data. Your computer's memory and processor registers are all just mutable variables that are constantly being updated. Purity and immutability are useful abstractions, but they only go abstraction deep. Without mutation and impurity, computation can be nothing more than merely theoretical.

**However,** this isn't actually a problem if we *are* just talking about something purely theoretical! We'll see in the coming sections how proof assistants like Rok don't need to *run* programs to prove things, they just need to *type check* them, meaning it *doesn't matter* if the programs can't actually be run.

This means that a pure and functional language is the perfect fit for a proof assistant. All that matters for a proof is that we're able to express theoretical ideas in a way that's clear and precise and can be formally reasoned about. We don't have to care about performance or data representation or any of the details of real computation. Soon we'll even see that type theory, the logical framework powerful enough to form the foundations of all of mathematics and computer science, is itself basically just a pure functional language!

In a much later section we'll also discover that it *is* actually possible to prove things about imperative mutating code, and even that mutating code can be shown to perfectly correspond with purely theoretical code. This is one of the most important contributions of Rok, that it integrates purely logical and realistically computable code and allows them to usefully interact.

But before all that, we have to build up some foundations.

### Coding in Logic Rok

The thing that makes Logic Rok and other proof assistant languages special is *dependent types*, but we can't really understand those yet. First let's just go over the basic features of Logic Rok, the features it shares with basically every other functional language like haskell.

First, we'll define a datatype, a discriminated union (called an `enum` in Rust) that's shaped just like our old friend `boolean`. This type lives in the `Ideal` sort and so is purely theoretical.

TODO

Pretty simple. Logic Rok comes with a default boolean called `bool`, but we'll use our own for a second.

Now let's define a function for `Boolean`. In normal imperative languages the body of a function is a series of *statements*, commands that mutate state as you go through the function. But in pure functional languages we can't mutate anything, so the body of a function is *only one expression*. Let's define the basic `negate`, `and`, `or`, and `xor` functions:

TODO

Some of these use `let` to give some expression a name that's used in subsequent lines, and the last expression is the final return value of the function. While this may seem at first to be a use of mutable state and against the rules, the way the evaluation rules of these languages are defined means these `let`s are technically a part of the final expression that are just evaluated first and replaced afterwards. Don't worry about it too much!

Both Logic and Compute Rok have an awesome trait system, and the `if` operator in both uses a trait called `Testable` that relates a type back to `bool`. Let's make our `Boolean` testable by implementing this trait, and then use `if` to redefine the functions:

TODO

We can also define types in the shape of a record (called `struct` in Rust):

TODO

Or tuples:

TODO

Or ["unit"](https://en.wikipedia.org/wiki/Unit_type) for types that can only have one possible value:

TODO

And of course the different *variants* (the academic term) of a discriminated union can be shaped like any of those types:

TODO things like option and result and color and ipaddress etc

We can also create an *empty* type, a type that's impossible to actually construct!

TODO

This is a discriminated union with *zero* variants, so if we try to choose some "constructor" to build this type, we can never actually find one and so will never be able to. You may wonder why we'd ever bother to define a type we can't actually construct, but I promise we'll discover a very powerful use for this type later.

Before we move on it's a good idea to just notice a few ways these different varieties of types relate to each other:

- Tuples and records aren't really that different, since a record is just a tuple with convenient syntax sugar names we can use to refer to the fields. But any record or tuple type could be refactored into the other shape and the program would do the exact same thing.

  TODO

- The basic unit and record and tuple types are essentially also discriminated unions, they just only have one variant! Deep inside Rok all types are actually represented that way, which is why an "empty" type is possible.

  TODO

- The `true` and `false` in `Boolean` are both just the unit type, but they're given distinct names and *defined* as being different from each other by the discriminated union they live in. The same is true for `None` in `Option` and the colors in `Rgb` and `Color`.

Now we get to the thing that makes `Ideal` types special, their ability to simply represent recursive types:

TODO nat

This type encodes natural numbers (or unsigned integers) in the weird recursive style of the [Peano axioms](https://en.wikipedia.org/wiki/Natural_number#Peano_axioms), where `0` is of course `zero`, `1` is `successor(zero)`, `2` is `successor(successor(zero))`, and so on. Remember, `successor` isn't a *function* that increments a value, it's a *type constructor* that *wraps* children values. Don't worry, you won't have to actually write them that way in practice, since the Rok compiler will coerce normally numbers into `nat` when it makes sense to.

You may wonder why we'd represent them this way? Wouldn't this be incredibly inefficient? Whatever happened to bytes?

And you'd be right! In a real program this way of encoding numbers would be an absolute disaster. But Peano naturals are perfect for proving properties of numbers since the definition is so simple, precise, and doesn't depend on any other types. Our real programs will never use this idealized representation, but it's extremely useful when we're proving things about bits and arrays and a whole lot more. We'll see exactly how when we finally get to proofs, so for now let's not worry about it and just write some functions for these numbers:

TODO nat operations add, subtract, multiply, remainder divide, is_even

Another extremely useful recursive type we'll use constantly is pure functional `List`, which is generic:

TODO

Basically every pure functional language uses the terms [`nil` and `cons`](https://en.wikipedia.org/wiki/Cons) when defining basic lists (`Cons` is short for "*cons*tructing memory objects"), so since they're so prevalent we've decided to stick with them here. `Nil` is just a "nothing" or empty list, and `Cons` pushes a value to the head of a child list, in basically the same way as a linked list. This means `[]` would be represented as `Nil`, `[1]` as `Cons{ item=1, rest=nil }`, `[1, 2]` as `Cons{ item=1, rest=Cons{ item=1, rest=Nil } }`, etc. Again you won't have to write them that way, the normal list syntax basically every language uses (`[1, 2, 3]`) will get coerced when it makes sense.

Just like with `nat`, we won't almost ever actually represent lists this way in real programs, but this definition is perfect for proving things about any kind of ordered sequence of items.

Here are a few functions for `list`:

TODO

Now that we're basically familiar with how to code in Logic Rok, we can start understanding how to use it to prove things!

### A Crash Course in Logic

If you ever took a discrete mathematics or formal logic class in school, you likely already know everything in this section. It isn't very complicated, but let's review quickly to make sure we're on the same page.

A **proposition** is a claim that can be true or false (academics often use the symbols `⊤` and `⊥` for true and false). Some examples are:

- `I am right-handed`
- `It is nighttime`
- `I have three cookies`

We can assign these claims to a variable, to make it shorter to refer to them (`:=` means "is defined as"):

- `P := I am right-handed`
- `Q := It is nighttime`
- `R := I have three cookies`

Then we can combine these variables together into bigger propositions using [logical connectives](https://en.wikipedia.org/wiki/Logical_connective):

- The `not` rule reverses or "negates" (the academic term) the truth value of a proposition. It's usually written with the symbol `¬`, but we'll use `~`. So if `A := ~P` then `A` is true when `P` isn't true.
- The `and` rule requires two variables to both be true for the whole "conjunction" (the academic term) to be true. It's usually written with the `∧` symbol (think of it as being "strict" or "closed", since `and` is more "demanding" and points downward), but we'll use `&`. So if `A := P & Q` then `A` is true only when both `P` and `Q` are both true.
- The `or` rule requires only one of two variables to be true for the whole "disjunction" (the academic term) to be true. It's usually written with the `∨` symbol (think of it as a "loose" or "open" link, since `or` is less "demanding" and points upward), but we'll use `|`. So if `A := P | Q` then `A` is true when either `P` or `Q` are true.

All these connectives can have a "truth table" written for them, which tells us if the overall expression is true based on the truth of the sub expressions.

TODO truth tables for not, and, or

The `implication` rule is has an especially important place in the type theory we'll get into in later chapters. It's usually written with the `→` symbol or just `->`, and it's easy to think why it's shaped like an arrow: the truth value of the left variable "points to" the truth value of the right variable. So for example, if `A := P -> Q`, then `A` is true if whenever `P` is true `Q` is also true. It's also not an accident that `->` represents both implication and the type of functions (`str -> bool`), but we'll get to that later.

TODO truth table

Very importantly, notice how an implication is only false in one situation, when the left variable is true and the right is false. This means that if the left variable is *false* then the implication is always true, or if the right variable is *true* then the implication is always true. Basically you can think of implications like an assumption and some conclusion that should always follow from that conclusion: if the assumption isn't true, then it doesn't matter what the conclusion is!

The `iff` or "if and only if" rule is easier to grasp. Written with `↔` or `<->` it basically requires the two truth values to be in sync with each other. If `A := P <-> Q` then if `P` is true or false then `Q` has to be the same thing.

TODO truth table

And of course, we can combine these connectives in arbitrarily nested structures!

TODO truth table showing some compound structures

Notice how the connectives can be restated in terms of each other? Like how `P <-> Q` is equivalent to `(P -> Q) & (Q -> P)`? Or `Q` is equivalent to `(P -> Q) & P`? There are lots of these equivalences, which all form basic *tautologies* (formulas that are always true) that can be used when proving things.

TODO list of boolean rules

This basic form of propositional logic is obviously somewhere at the heart of computing, from binary bits to boolean values. We're all familiar with operators like `!` and `&&` and `||` in common programming languages like rust and java and javascript, and they just represent these rules as computations on boolean values.

But simple truth values and connectives aren't really enough to prove anything interesting. We don't just want to compute basic formulas from true or false values, we want to be able to prove facts about *things*, from numbers all the way to complex programs. With the simple rules we've been talking about, we can only stick arbitrary human sentences onto variables and then tell the computer if they're true or not. We need something more powerful!

First we need **predicates**, which are just functions that accept inputs and return propositions about them. So if we can write a predicate in this general shape: `predicate_name(input1, input2, ...) := some proposition about inputs`, then these are all predicates:

- `And(proposition1, proposition2) := proposition1 & proposition2`
- `Equal(data1, data2) := data1 == data2` (`data1` is equal to `data2`)
- `Even(number) := number is even` (I'm cheating here, since this is still just some arbitrary sentence. Let's ignore it for now 😊)

We're also going to need these two ideas:

- The "for all" rule (or *universal quantification*), saying that "for all values" some predicate is true when you input the values. Academics use the `∀` symbol for "for all", but I'll just write `forall`:
  - `forall number, Even(number) -> Even(number + 2)` (forall values `number`, if `number` is even then that implies `number + 2` is also even)
  - `forall data1 data2 data3, data1 == data2 & data2 == data3 -> data1 == data3` (forall values `data1` `data2` `data3`, if `data1` is equal to `data2` and `data2` is equal to `data3`, then that implies `data1` is equal to `data3`)

- The "exists" rule, (or *existential quantification*), saying that "there exists" a value where some predicate is true when you input the values. Academics use the `∃` symbol for "there exists", but I'll just write `exists`:
  - `exists number, Even(number)` (there exists a `number` such that `number` is even)
  - `exists data1 data2, data1 == data2` (there exists a `data1` and `data2` such that they are equal to each other)

<!-- TODO need an explanation of why quantification is a reasonable term to use, probably something along the lines that to "quantify" something is to give it a name it can be referred to by -->

The `forall` rule seems especially powerful! It would be extremely useful to prove that something is true about a potentially infinite "universe" of values. But how do we actually prove something like that in a programming language? We obviously can't just run all those infinite values through some function and test if returns true, especially since the whole point of using a purely theoretical programming language was that we don't actually have to run programs in order to prove things.

The crucial trick is to represent our propositions and predicates as *types* instead of data! Let's see how it works.

### Type Theory, the Calculus of Constructions, and the Curry-Howard Correspondence

A reasonable place to start is by figuring out how to represent the basic ideas of true and false in Logic Rok.

We might try just defining them as a discriminated union, our old friend `boolean`:

TODO

But if we walk much further down this path, we won't get anywhere. We'll end up having to actually compute and compare booleans in all our "proofs", since `true` and `false` are only different *values*, not different *types*.

This is a good place to reveal something really important but fairly surprising: if you're a programmer, *then you already prove things whenever you program!* How is that true?

<!-- Specifically we're talking about the `exists` rule, and every type defines its own family of values to prove exist. -->
Think about some random datatype such as `u64`. Any time you construct a value of `u64`, you're *proving* that some `u64` exists, or that the `u64` type is *inhabited* (the academic term). The mere act of providing a value of `u64` that actually typechecks as a `u64` very directly proves that it's possible to do so. Put another way, we can say that every concrete `u64` value provides *evidence* of `u64`, evidence that proves the "proposition" `u64`. It's a very different way of looking at what a datatype means, but it's true! The only problem with a proof of `u64` is that it isn't a very "interesting" or "useful" piece of evidence: but it's a piece of evidence nonetheless.

<!-- Specifically we're talking about the `exists` rule, but just that every type defines its own family of values to prove exist. -->

In the same way, when you define a function, you're creating a *proof* that the input types of the function can somehow be transformed into the output type of the function. For example this function:

```
fn n_equals_zero n: u8;
  return n == 0
```

has type `u8 -> bool`, so the function *proves* that if we're given a `u8` we can always produce a `bool`. In this way the `->` represents *both* the real computation that will happen *and* the implication operator `P -> Q`! The reason implication and functions are equivalent is exactly because datatypes and propositions are equivalent. Think of this example:

- the implication `P -> Q` has been proven
- so if `P` can be proven
- then `Q` can also be proven

TODO truth table

To convert this into the language of types and programs, we just have to change "implication" to "function", "proven" to "constructed", and `P` and `Q` to some types:

- the function `u8 -> bool` has been constructed
- so if `u8` can be constructed
- then `bool` can also be constructed

Pretty cool huh!

This simple idea is called the [Curry-Howard Correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence), named after the researchers who discovered it. This is the main idea that allows programs to literally represent proofs.

The only problem with `u8 -> bool` is that, yet again, it isn't a proof of anything very interesting! The type of this function doesn't actually enforce that the `bool` is even *related* to the `u8` we were given. All these other functions also have the type `u8 -> bool` and yet do completely different things!

```
fn always_true _: u8;
  return true

fn always_false _: u8;
  return false

fn n_equals_nine n: u8;
  return n == 9
```

The simple type of `bool` only gives us information about one value, and can't encode *relationships between* values.

But if we enhance our language with *dependent types*, we can start doing really interesting stuff. Let's start with a function whose *type* proves if its input is equal to 5. We've already introduced asserted types, so let's define our own type to represent that idea (this isn't the right way to do this, we'll improve it in a second). Let's also write a function that uses it.






It's even possible to define types that *can't possibly* be constructed, such as an empty union: `type Empty; |`. When you try to actually create a value of `Empty`, you can't possibly do so, meaning that this type is impossible or "False".


But what about this definition of `True`?

TODO












Representing propositions as datatypes and theorems as functions means that we don't have to *run* the code to "compute" the truth value of variables. We only have to *type check* the code to make sure the types are all consistent with each other. If the type of function asserts that it can change input propositions into some output proposition, and the body of the function successfully typechecks by demonstrating steps that do in fact break a piece of propositional data apart and transform it to create a piece of propositional data with a different type, then the very existence of that function proves that the input propositions all *imply* the output proposition.

### Proofs using Tactics

## Verified Compute Rok

### Separation Logic

### Separation Logic in Use

### Logical Modeling

### Testing and Conjecture Checking

### Trackable Effects
















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
  so indentation is used to structure the program

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
data User;
  id: usize
  age: u8
  active: bool
data Point; x: f64, y: f64

// or unit
data Token
data Signal

// or tuples
data Point; f64, f64
data Pair;
  i32
  i32

// or discriminated unions
data Event;
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
data Pair T, U; T, U
data NonEmpty T;
  first: T
  rest: [T]
```

But the entire point of Rok is that you can prove your program is correct! How do we do that?



The most common and simplest way we can make provable assertions about our programs is by making our types *asserted types*. If we want to guarantee that a piece of data will always meet some criteria, we can make assertions about it with the `&` operator. Then, any time we assign a value to that type, we have to fulfill a *proof obligation* that the value meets all the assertions of the type. More on proofs in a second.

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
// "^" can be used to refer to the parent datatype
// so fields of a type can refer to other fields
alias Range; i32, i32 & > ^.1

data Person;
  age: u8
  // here the value of is_adult
  // has to line up with .age >= 18
  is_adult: bool & == ^.age >= 18
  // this pattern of requiring a bool
  // to exactly line up with some assertion
  // is common enough to get an alias
  is_adult: bool.exact (^.age >= 18)
```

So how do we actually prove that our program actually follows these data assertions? Can the compiler figure it out by itself? In many simple situations it actually can! But it's literally impossible for it to do so in absolutely all situations (if it could, the compiler would be capable of solving any logical proof in the universe!).

To really understand how this all works, we have to get into the Logical side of Rok, and talk about `Ideal`, `Prop`, and The Calculus of Constructions.

## Logical Rok

First let's start with the `Ideal` type family. `Ideal` types are defined to represent *abstract*, *logical* data. They aren't intended to be encoded by real computers, and their only purpose is to help us define logical concepts prove things about them. To go with the `Ideal` type family is a whole separate programming language, one that's *pure* and *functional*. Why pure and functional? Simply, pure and functional languages relate directly to mathematical type theory (mathematical type theory is nothing but a pure and functional language!). It's much easier to define abstract concepts and prove things about them in pure and functional settings than the messy imperative way real computers work. Otherwise we'd have to deal with distracting details about memory layout, bit representation, allocation, etc. The "programs" we write in this pure functional language aren't actually intended to be run! They just define abstract algorithms, so we only care about them for their type-checking behavior and not their real behavior.

The type system of logical Rok is shaped a lot like computational Rok to make things convenient. But the big difference between types in logical Rok and computational rok is how they handle type recursion.

```
// in computational Rok types must be representable in bits and have a finite and knowable size,
// meaning they can't reference themselves without some kind of pointer indirection
data NumLinkedList T;
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




```
data equal_5 number;
  | yes & (number == 5)
  | no & (number != 5)

fn is_equal_5 number: u8 -> equal_5 number;
  if number == 5; return yes
  else; return no
```

Pretty simple! The ability to *dependently* reference the input `number` in the output type makes this work. And in this case, because the assertions we're making are so simple, the compiler is able to prove they're consistent without any extra work from us. The compiler would complain if we tried to create a function that *wasn't* obviously consistent:

```
fn is_equal_5 number: u8 -> equal_5 number;
  if number == 6; return yes
  else; return no
// compiler error!
```

But we don't have to define our own `equal_5` type, we can just use `bool`, which can already generically accept assertions. The same is also true for a few other standard library types like `Optional` and `Fallible` that are commonly used to assert something about data.

```
// bool can take a true assertion and a false assertion
fn is_equal_5 number: u8 -> bool (number == 5) (number != 5);
  return number == 5

// we can also use the alias for this concept
fn is_equal_5 number: u8 -> bool.exact (number == 5);
  return number == 5
```

But something about the above assertions like `number == 5` and `number != 5` might bother you. If proofs are *just data*, then where do `==` and `!=` come from? Are they primitive in the language? Or are they just data as well?

They are actually just data! But specifically, they're data that live in the `Prop` sort. `Prop` is the sort defined to hold logical assertions, and the rules about how it can be used make it suited for that task.

Let's define a few of our own `Prop` types to get a feel for how it works.

```
// in the computational types, unit or `()` is the "zero size" type,
// a type that holds no data
alias UnitAlias; ()
data MyUnit

// we can define a prop version as well!
prop PropUnit
// this type is "trivial", since it holds no information and can always be constructed
// in the standard library this type is called "always", and in Coq it's called "True"
alias AlwaysAlias; always

// we already saw an example of a computational type that can't be constructed
data Empty; |
// and of course we can do the same in the prop sort
prop PropEmpty; |
// this type is impossible to construct, which might seem pointless at first, but we'll see how it can be extremely useful later
// in the standard library it's called "never", and in Coq it's called "False"
alias NeverAlias; never
```

Okay we have prop types representing either trivial propositions or impossible ones. Now let's define ones to encode the ideas of logical "or", "and", "not", "exists", "forall", and equality.

```
// logical "and", the proposition that asserts the truth of two child propositions,
// is just a tuple! a tuple that holds the two child propositions as data elements
// we have to present a proof of both propositions in order to prove their "conjunction",
// which is the academic term for "and"
prop MyAnd P: prop, Q: prop; P, Q

// then we use this constructor just like any other
def true_and_true: MyAnd always always = MyAnd always always

// we could of course also structure it as a record,
// but the names aren't really useful (which is why we invented tuples right?)
prop MyAnd P: prop, Q: prop;
  left: P
  right: Q

// logical "or", the proposition that asserts the truth of either one child proposition or another,
// is just a union!
// we only have to present a proof for one of the propositions in order to prove their "disjunction",
// which is the academic term for "or"
prop MyOr P: prop, Q: prop;
  | left; P
  | right; Q

def true_or_true_left: MyOr always always = MyOr.left always
def true_or_true_right: MyOr always always = MyOr.right always

// logical "not" is a little more interesting. what's the best way to assert some proposition *isn't* true? should we say it's equal to "never"? that doesn't really make sense, since you'll see in a moment that "equality" is just an idea we're going to define ourselves. instead we just want to prove that this proposition behaves the same way as "false", in the way that it's impossible to actually construct a value of it.
// The most elegant way is to say that if you *were* able to construct a value of this proposition, we would *also* be able to construct a value of "false"! So "not" is just a function that transforms some proposition value into "false".
// notice that we don't need to create a new type for this, since MyNot is just a function
alias MyNot P: prop; P -> False
```

Equality is interesting. Depending on exactly what you're doing, you could define what it means for things to be "equal":

- Two byte-encoded values are equal if their bitwise `xor` is equal to 0.
- Two values are equal if any function you pass them to will behave exactly the same with either one.
- A value is only equal with exactly itself.

In Logical rok, since all values are "ideal" and not intended to actually ever exist, the simplest definition is actually that last one: a value is only equal with exactly itself.

```
prop MyEquality {T: Ideal} -- T, T;
  @t -> MyEquality t t
```







Logical "forall" is the most interesting one, since it's the only one that's actually defined as a primitive in the language. We've actually been using it already! You might be surprised to learn that the function arrow `->` is just the same as "forall"! It's just a looser version of it.

In type theory, if we want to provide a proof that "forall objects in some set, some property holds", we just have to provide a *function* that takes as input one of those objects and returns a proof (which is just a piece of data) that it has that property. And of course it can take more than one input, any of which can be proof objects themselves.

So how do you actually write a "forall" type? Since `forall` is such an important concept, its rok syntax very concisely uses `@`. Here's how you would write the type for the `is_equal_5` function we wrote earlier: `@ number: u8 -> bool.exact number == 5`. I prefer to read this as: "given any `number` which is a `u8`, I'll give you a `bool` which exactly equals whether `number` is equal to 5". For functions that take multiple "forall" variables as inputs (the academic term for accepting a forall variable as input is to "universally quantify" the variable, since a forall assertion proves something universal), you use commas instead of arrows between them: `@ n1, n2 -> bool.exact n1 == n2`.

Very importantly, in order for that function to *really* prove the assertion, it has to be infallible (it can't fail or crash on any input) and provably terminating (it can't infinitely loop on any input). It is allowed to require things about the input (for example a function can be written to only accept even integers rather than all integers), but it has to handle every value it makes an assertion about.





```
// since we're providing default assertions,
// the normal form of bool only asserts the useless `always`
type bool when_true = always, when_false = always;
  | true & when_true
  | false & when_false

// you'll notice we don't bother with an assertion for T
// since the user can just provide an asserted type themselves
type Optional T, when_none = always;
  | Some; T
  | None & when_none

// same thing here
type Fallible T, E;
  | Ok; T
  | Err; E
```


Understanding indexed types
In a language with normal generics, if there are multiple functions or constructors in the type that all use a generic variable then when those functions or constructors are actually used all the instances of those generic variables to have to be equal. You can get that exact same behavior in rok, but you can *also* get more "dependent" versions of generic variables which are allowed to be different.
This is useful in many situations, but it's best to start with two examples.

normal polymorphic lists, to understand the normal situation, and how it would be annoying or inconsistent to allow different values of the generic variable. forcing them on the left side basically allows us to elide any mention of them and still keep the requirement of them aligning

length indexed lists
attestations of zero or one-ness
even numbers


in the case of the `even` predicate, the different constructors all provide evidence of the same proposition `even`, but they do so for different numbers.






The key insight is in understanding *The Curry-Howard Correspondence* and the concept of *Proofs as Data*. These are a little mind-bending at first, but let's go through it.

A good way to understand this is to see *normal* programming in a different light.


Basically, any type that lives in the `Prop` sort is *by definition* a type that represents a truth value, a logical claim.

Proofs are *all* defined by constructors for data, it's just data that lives in a special type sort, specifically the type sort `Prop`. First we define some type that defines data representing some logical claim, and then when we want to actually *prove* such a claim, we just have to *construct* a value of that type!

It's important to notice though that this wouldn't be very useful if the type system of our language wasn't *dependent*, meaning that the type of one value can refer to any other separate value in scope. When we put propositions-as-data together with dependent types, we have a proof checker.

This is the key insight. When we make any kind of logical claim, we have to define *out of nowhere* what the definition of that claim is.
















Theorem proving

In normal programming, we usually follow a pattern of writing out code, then checking it, and then filling in the gaps, and we don't really need any kind of truly interactive system to help us as we go.

But writing proofs, even though it's technically the exact same as just writing code, isn't as easy to do in that way. When we're trying to solve a proof it's difficult to keep in mind all the facts and variables we've assumed existed at that particular stage, and we often have to move forward step by step.

This is why theorem proving is most often done with *interactive tactics*. Instead of writing out all or most of the code as we might for a purely computational function, we instead enter an interactive session with the compiler, where it shows us what we have available to us and what we have left to prove.

In `rok`, we do this using the `rok tacticmode` command, or with a variety of editor plugins that use `tacticmode` under the hood. Say we want to prove something about numbers, maybe that addition of natural numbers is symmetric. First we write out our definition of that theorem:

```
thm addition_is_symmetric: @ (x, y): nat -> x == y <-> y == x;
```

then give the command `rok tacticmode addition_is_symmetric` (or use the equivalent start command of our editor), and rok will find that definition, parse and type check any definitions it depends on, and enter interactive tactic mode. It shows the *context*, or the variables this definition takes as inputs, and the *goal*, which is basically the type of the thing we're trying to prove. Remember, a theorem is a thing whose final output lives in the `Prop` sort, whether that be a piece of data that lives in `Prop` or a function that returns something in `Prop`. So when we "prove" a theorem we're really just constructing a piece of code!

To really make clear that theorems are just code, let's actually write out a theorem manually!

Or let's define a *computational* function using tactics.

















## Abstract assembly language

Here's an example of a Rok program in the "core" assembly language that is general enough to compile to basically any architecture.

Rok itself ships with a few different layers of computational language:

- Thinking about computation in general.
- Thinking about a specific collection of generalizable instructions in an unknown machine. This means you're reasoning about specific calling conventions.
- Thinking about blocks with "function arguments"

- `asm_zero`: a truly representational abstract assembly language, used to define the "common core" of all supported architectures
- `asm_one`: the next level of abstraction, with type definitions and sugars, llvm style functions along with call/ret instructions. must instantiate with a calling convention
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
