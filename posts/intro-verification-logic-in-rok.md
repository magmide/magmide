This introduction will teach you how to use Rok to build truly provably correct software, by going through these topics:

- A quick look at Rok's syntax style, Compute Rok, and roughly what it will look like to write functions that are provably correct.
- An in depth look at Logical Rok, proof objects, and the Curry-Howard Correspondence.
- A crash course in proving, proof tactics, and type theoretical logic.
- A full treatment of using `core` Compute Rok and Logical Rok together, including trackable effects.
- A guide to metaprogramming in Rok.
- A deeper look at the lower levels of Compute Rok, such as the `asm` layers, and instantiating lower levels with custom environments or calling conventions.





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


So how can we prove things in a programming language? How does that make any sense? You'll be surprised to hear that you already write proofs all the time!

Think about when you define a data type, such as `type Num; u64`. Any time you construct a value of `Num` by calling the `Num` constructor with a `u64` value (`Num 8`), you're *proving* that some `Num` exists. You haven't proven something very *interesting*, but you've proven something nonetheless. It's even possible to define types that *can't possibly* be constructed, such as an empty union: `type Empty; |`. When you try to actually create a value of `Empty`, you can't possibly do so, meaning that this type is impossible or "False".

In the same way, when you define a function, you're creating a *proof* that the input types of the function can somehow be transformed into the output type of the function. For example this dumb little function:

```
fn n_equals_zero n: u8;
  return n == 0
```

has type `u8 -> bool`, so the function *proves* that if we're given a `u8` we can always produce a `bool`. In this way, the `->` in function types can be understood as *both* a computational transformation *and* the implication operator from logic (if this is true then that is true, `P -> Q`).

The only problem with `u8 -> bool` is that it isn't a proof of anything very interesting! The type of this function doesn't actually enforce that the `bool` is even *related* to the `u8` we were given. All these functions also have the type `u8 -> bool` and yet do completely different things!

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
