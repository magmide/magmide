You'll probably have to chew on these big ideas over time, so I've tried my best to make them short and easy to read through quickly. That way it should be easy to come back and reread them as you need to.


First a few chapters on basic ideas I just want to make sure we're on the same page about:

- basic type system ideas, basically a tour of the Rust type system
- pure functional languages and lambda calculi, what they are and why they're good for proving things
- boolean logic (propositional calculus), using coq functions as truth tables
- predicate logic (first-order logic). here I just talk about the ideas we want to be able to encode (`forall`, `exists`, predicates), and don't relate them to coq.

now we're going to get into the meat of it, the stuff that's special about coq, so first I'll just introduce all the big ideas we're going to cover with short explanations so you know they're coming

- dependent types, not really getting into how to use them yet, just showing that they exist.
- type theory, just talking about the ideas, again not really bothering with anything concrete.
- calculus of constructions, which is just a particular type theory that allows us to define inductive types. inductive types and forall-style function types are the only primitives in the type system. the computation rules do the rest and are pretty simple rules about unfolding function calls and stuff. this chapter is where we actually start doing real interesting coq examples. we only worry about `Type` level stuff and inductive types though. start with true/false, then implication, then how implication is the same as forall, then and/or
- curry-howard, and talk of the prop universe and how propositions are types and proofs are values. also talking about interactive mode and how it works.
- indexed types

https://coq.inria.fr/refman/language/core/conversion.html

that's the entire big idea section! with that we're ready to just get into the language

- reflexivity
- rewriting
- exists proofs
- automation
- destruction proofs
- proving negations
- induction over data structures
- induction over propositions
- inversion
- coinduction (very short, mostly just refer to outside sources)

then the more "reference by example" that will slowly be filled in





# What is logic?

*Logic is made up!* Logic isn't "real" in any strict sense of the word. In logic, a "theory" is just some completely arbitrary collection of *rules* for defining and manipulating imaginary structures, and academic logicians just study different kinds of theories and what they're capable of doing. Anyone in the world could make up any system of rules they wanted, and then call that system a "theory".

However some sets of rules are more *useful* than others! The reason we bother with logic is because it helps us think through difficult problems we want to solve, so theories are more useful the more they actually "line up" with the real world. If we're able to come up with a set of clear and strict rules we can always follow to reliably make predictions about the real world and real problems, then that set of rules is helping us be more aligned with reality. It acts as a crutch we can use to deal with complex problems.

In order to really "line up" with the real world, a logical theory must be "consistent" by never telling us things that aren't true. For example if our theories of counting and arithmetic said that `2 + 2 = 5`, then they wouldn't be very useful, because in the real world when we grab two objects in one hand, another two in our other hand, and then put them together and count them, we always get `4` rather than `5`. If you wanted to you could define a number system that made `2 + 2 = 5`! It just wouldn't be very useful.

Of course if you ask an academic logician they could talk your ear off about consistency and and proof theory and incompleteness and all the other meta-theoretical stuff academic logicians care about. I'm obviously simplifying things here, but that's because I don't really think it helps us much to spin our wheels thinking about these big questions when thinkers over the centuries have already given us excellent practical answers. When you write computer programs you don't bother to worry about how the electrons are moving around in your machine's transistors or what subatomic fields are allowing them to do so, that's all just abstracted. Let's do the same thing here.


<!-- As I've been reading about logic and math while trying to understand formal verification, I've been frustrated at how fuzzy and vague a lot of it is. I think mathematicians have a bad habit of asking ultimately unproductive questions just because they're interesting, and letting themselves get [nerd-sniped]() trying to figure out absolutely everything.

In practical engineering, we're always looking for abstractions, simplifications we can use to ignore details that don't matter for the problem we're trying to solve right now. In my opinion, these mind-bending questions about what logic "really is" or where it comes from aren't that useful, and we'll get stuck spinning on them forever if we let ourselves. So I just want to quickly get these questions out of the way so we don't have to talk about them anymore while still making sure you know you *can* if you want to.

So, the answer to the question, "what is logic?"

For our purposes, we're just going to put "logic" and "consistency" beneath abstractions and say "we don't care!" We don't need to deeply understand that stuff to make progress. But it's helpful to know exactly where that abstraction level is! Instead of looking at that layer like it's mysterious, we're just postponing looking at it for now. And honestly, this area is kind of a mess. It seems just about every professor of logic has written a bunch of things about what logic and type theory and such are, and mostly everyone just says the same few things over and over again but using different words. Again, don't worry about it too much. If you want to dive down the rabbit hole, here are some resources you might enjoy.

When going over different logical ideas, it might be tempting to ask questions like "why should I trust this system of rules?" "what makes this system of rules better than this other system of rules?" "what makes this system of rules trustworthy or useful?"

javascript -> browser -> c/rust -> assembly -> hardware -> physics
magma -> calculus of constructions -> type theory -> logic -> proof theory -> forever!!!

To prove we can make up our own rules, let's make our own theory of numbers! We'll define a system of rules, with exactly these rules:

- There is a constant `zero` (remember, we can choose any name we want! the meaning of this constant completely depends on what we arbitrarily decide we're allowed to do with it!)
- There is a constant `next`. `next` is like a function that can "wrap" either `zero` or any existing wrapping of `next`s. So we can write these "wrappings" like this: `next(zero)` or `next(next(zero))` etc. (remember, we could choose any "syntax" we want, such as `zero.next` or `(next zero)`).

With these two basic rules we can count! `0` is `zero`, `1` is `next(zero)`, etc. But without any more rules we can't do much else, for example we can't create an `add` function that can put together two of these "numbers". But we could choose to add many different new rules in order to make our theory of numbers "strong" enough to represent the idea of addition.

you'll notice that we've defined an *inconsistent* theory here! This is one way we could try to understand what it really *means* for a theory to be inconsistent, *that we can't actually follow all the rules all the time*, or that if we try to follow all the rules we won't know what to actually do in some situations. Basically, a theory is inconsistent if it doesn't have enough rules for us to always know what to do in every situation. we can make the above theory consistent by either removing things (remove `red` and all rules that explictly mention it) or adding things (just arbitrarily decide that `green` `yo` `red` is `green`). you'll notice that an inconsistent theory is just one where there isn't enough detail in the theory to always follow the rules.

https://plato.stanford.edu/entries/russell-paradox/

a paradox is just a situation that *seems* to be allowed by a theory but actually isn't specified enough to know what to do, since it implies questions we can't answer
-->


# What are propositional/predicate/first order/higher order logic?

Academic logicians have categorized different logical systems by how "powerful" they are. Basically
https://en.wikipedia.org/wiki/First-order_logic

- Propositional: basic ideas about true/false, and different truth table operations on those values.
- Predicate/first-order logic: creating functions

# What are dependent types?

Think of a function that is supposed to take an integer and return a boolean representing whether or not that integer is equal to `1`. In Rust we might write that function like this:

```rust
fn is_one(n: usize) -> bool {
  n == 1
}
```

The type of that function is `(usize) -> bool`, representing the fact that the function takes a single `usize` argument and returns a `bool`.

But notice that the *type* `(usize) -> bool` can apply to *many* different functions, all of which do different things:

```rust
fn is_one(n: usize) -> bool {
  n == 1
}
fn is_zero(n: usize) -> bool {
  n == 0
}
fn always_true(_: usize) -> bool {
  true
}
fn always_false(_: usize) -> bool {
  false
}
// ... many other possible functions
```

What if we want our type system to be able to *guarantee* that the boolean returned by our function did in fact perfectly correspond to the integer passed in being equal to `1`? Dependent types allow us to do that, because they are *types* that can reference *values*. Here's a Coq function that returns what's called a "subset type" doing exactly what we want (don't worry about understanding this code right now):

```v
From stdpp Require Import tactics.

Program Definition is_one n: {b | b = true <-> n = 1} :=
  match n with
  | 1 => true
  | _ => false
  end
.
Solve All Obligations with naive_solver.
```

In Coq's dependent type system, any *value* used earlier in a type can be referenced in any type afterward. For example the type of `is_one` uses the `forall` keyword to introduce the name `n` that is referenced in the return type: `forall (n: nat), {b: bool | b = true <-> n = 1}`. Again, don't worry about the details yet, we'll go over that in detail later.

<!-- Coq makes this a bit more difficult than we might prefer, but with a helper tactic from the [`stdpp` library](https://gitlab.mpi-sws.org/iris/stdpp) we don't have to think about -->

# What is induction?

# What is Type Theory?

To understand type theory, it is actually helpful to understand what came *before* type theory: set theory.

Type theory is just a way of defining what kinds of values can exist, and what operations can be performed on those values. That's really it! "Type theory" is actually a big umbrella term that contains a few *specific* type theories, but they all share one basic idea: every *term* in the logic has such as variables or functions has some *type* defining what operations are allowed for that term. also type theories define "rewriting rules", basically computation rules, about how some term can be "computed" or "evaluated" or "reduced" to transform it into a different term. Usually these rewriting rules are designed so that the terms only get "simpler", or get closer and closer to being pure values that can't be reduced any further. Academics call these irreducible terms "normal forms".

types vs terms vs values

https://en.wikipedia.org/wiki/Type_theory#Basic_concepts

https://en.wikipedia.org/wiki/Inductive_type



# What are pure functional languages?

# What is the Lambda Calculus?

# What is the Curry-Howard Correspondence?

https://en.wikipedia.org/wiki/Intuitionistic_type_theory

Types can be seen as propositions and terms as proofs. In this way of reading a typing, a function type {\displaystyle \alpha \rightarrow \beta }\alpha \rightarrow \beta  is viewed as an implication, i.e. as the proposition, that {\displaystyle \beta }\beta  follows from {\displaystyle \alpha }\alpha .
https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence

# What is the Calculus of Constructions?

https://en.wikipedia.org/wiki/Calculus_of_constructions

# What are Hoare Triples?

Hoare Triples were invented by [Tony Hoare](), and are a very simple method for making logical assertions about the behavior of programs.

Essentially, a "triple" is:

- A piece of a program, or a *term* that we're making assertions about. Depending on the kind of language, it could be a function, a series of statements, an expression, etc.
- A *precondition* that we assume to be true before the term is evaluated.
- A *postcondition* that we claim will be true after the term is evaluated.

We "assert" a triple by proving that if the precondition is true before you evaluate the term then the postcondition will always be true. This makes the precondition a *requirement* for anyone evaluating the term if they want the postcondition.

The pre/post conditions are usually written in double brackets (`{{ some assertion }}`) and put before and after the term. Here's a really basic example:

```
{{ n = 0 }}
while (n < 5) {
  n = n + 1
}
{{ n = 5 }}
```

We can write triples that aren't true, we just won't be able to prove them!

```
{{ n = 0 }}
while (n < 5) {
  n = n + 1
}
{{ n = 6 }} // wrong!
```

There's lots of theory about properties of Hoare triples, but they get really interesting when combined with Separation Logic.

# What is Separation Logic?

When we're writing a real computer program, all the values we pass around "live" somehwere in the machine, either a cpu register or memory. When we pass values to other parts of the program, we need to somehow tell that other part where our values are, either by copying them to some different place or just giving a reference to where the value is stored. This means we don't really "give" the value, we just put it somewhere we know the other part will be looking for it.

When we're writing a real computer program, all the values being passed around actually "live" somewhere in the machine, either in a register or memory. Let's make up

```
```


This means they could be "destroyed" by writing different values into their spot. This is a very important quality of a program that has to be respected in order to get the program right, since carelessly writing values to different spots in the machine could destroy values other parts of the program are relying on.

For a long time formal verification theories didn't do a good job of acknowledging this, which is why they typically only worked with pure functional systems where no value could be mutated. Doing so made it easy to pretend the real computational values were actually purely imaginary logical values, but this made it impractical to prove things about real high performance programs.

Separation logic was invented as a solution to this problem. It's a system that makes it possible to encode "destructibility" or "ownership" into values, so they can finally reason about real locations in a machine.

Let's go through how it works. If we have some assertion in a normal logic, such as `A & B`, we're allowed to "duplicate" parts of our assertion as long as doing so doesn't change its meaning. For example, if `A & B` is true, then so is `A & (A & B)` or `(A & B) & (A & B)`. However you can probably guess that this kind of duplication isn't actually consistent if the assertions are talking about values that live in some spot of the machine.

Separation logic introduces a concept called the "separating conjunction", that basically claims *ownership* of some assertion, and requires us to "give up" an assertion if we want to share it with someone else.

So we can work out examples, let's make up a notation to encode our assertions about memory locations: we'll decide that something like `[10] => 50` says that memory address `10` holds the value `50`.

The all-important separating conjunction is almost always written with the `*` symbol, and is usually read aloud as "and separately". So `[1] => 1 * [2] => 2` would be read as "memory address `1` holds `1` *and separately* memory address `2` holds `2`".

Here's the really important part: the separating conjunction is *defined* so that it isn't allowed to combine multiple assertions about a single location under any circumstances. For example `[1] => 1 * [1] => 1` isn't allowed, even though the two assertions say the same thing!

This means that if we want to call a function and share knowledge of some memory location we've been writing to, we have to *give up* our assertion of that memory location while the function is working with it, and we can't just make a copy for ourselves. This is the killer feature of separation logic: it encodes the idea of destructible resources with some very simple rules.

---

academic to engineer translation dictionary





---

By the time we're done, you'll understand these ideas
Dependent types, which allow types to reference values and so represent any logical claim about any value
Curry Howard equivalence, which discovered that a computer program can literally represent a logical proof
Type theory, the system that can act as a foundation for all logic and math, and is the thing that inspired programming in the first place
Calculus of constructions, the particular kind of type theory used by coq
Proof objects, the essential realization that proofs are just data, because logical claims are just types
Separation logic, the variant of logic that deals with finite resources instead of duplicable assertions

Basic type system ideas, they can skip if they know rust
Boolean logic, they can skip if they know about truth tables and de morgans law
Type theory by way of set theory, talking about the in operator and quantification and implication





















in my view, there are two major areas of learning you have to do to use Coq

- The big picture theoretical ideas such as Type Theory, The Calculus of Constructions, The Curry-Howard Equivalence, and induction. Some of these are genuinely mind-bending and difficult to wrap your head around!
- The actual *skill* of proving things, which is equal parts art and science.

Most guides I've encountered discuss both in an intermingled style, and seem to order their examples based on how big or complicated they are versus how difficult they are to understand. Basically all of them encourage you to open the guide in an editor environment capable of stepping through the proof tactics so that you can see how the proofs work as you read along.
In my experience trying to learn Coq, I routinely got hung up on the *concepts*, and found it difficult to really understand the proofs even if I could step through them. And similarly as I've tried to actually use Coq I've found it annoying to have to dig through a whole textbook to just find some tactic explanation or syntax example.

For these reasons this guide goes a different direction.

- The first part isn't really intended to be stepped through in an editor. It uses lots of examples, but it focuses on explaining the big ideas in a distilled and focused way. This part of the guide you can just read through and ponder. You'll likely have to sleep on many of the concepts to really get them.
- The second part is more of a workshop in practical proving. It doesn't have any big ideas to share, but just talks about different proof strategies, goes through detailed examples, and goes over how many common tactics actually work. This is absolutely intended to be hands-on and done in an editor.
- The third part is just a "by example" style reference, intended to be a resource you use while you're working on real projects. Coq is a *huge* language with tons of tactics and concepts, so the reference doesn't attempt to be truly complete, but we can work toward that goal together.

This guide is for you if you're attracted to the idea of writing provably correct software. Even if you don't have any particular projects in mind that you think could be verified, learning these ideas will massively level up your understanding of logic and computer science, and will completely change how you think about software.

> If a language doesn't change the way you think about programming it isn't worth learning
somebody


# basic type system concepts (which are secretly type theory ideas)

# pure functional languages

Coq is a pure functional language
some basic examples of functions
note how we're defining types with the `Inductive` keyword. don't worry about why `Inductive` makes sense for now, we'll talk about that a lot later. for reasons we'll talk about later we won't define any of
we only have to know how a type will be represented as bits if we actually *run* code that uses that type. if the code is merely *type checked* then the types can remain truly imaginary


haskell isn't *truly* pure and functional, it has little holes intentionally built into the language so that it can actually be used to run real computer programs. how it does that isn't relevant for us right now, so I won't go into it.
but Coq *really is* absolutely pure, which is why *on its own* it can't really be used for real computation. the language itself has no way of interacting with an operating system, or printing to consoles, or a way to be defined in terms of bits and machine instructions. the real purpose of the language is only really to be type checked and not run
but we can do these two things:

- use a language interpreter to "run" the language. this is extremely slow and of course can't always happen if we're doing things with possibly infinite data or whatever
- *extract* the language to a different one like ocaml or haskell. this is kinda gross in a way, since we're assuming that this process preserves all our correctness stuff and the target language can even do the things we want. but for many purposes it's perfectly acceptable.


you may be surprised to find out that Coq only has three truly primitive aspects:

- ability to define inductive types
- ability to pattern match on inductive types
- ability to define functions

the type system only has two basic primitives:

- functions
- inductive types

That's it! Everything else, all operators and even the definition of equality (`=`) are all defined within the language.




in logical languages when we define types we're defining something "out of thin air". we're defining arbitrary rules that we think will be useful because they line up with something in the real world. that's not the case for types in real programming languages, since those types are just abstractions around different ways of packaging and interpreting digital bits.

even numbers aren't really *real*, and when we count "things" we're really just thinking about billions of atoms that happen to be close enough together and stuck to each other enough that we can pick up one part of the "thing" and have the rest of the "thing" come along for the ride. everything is just atoms all the way down, but the concept of numbers is a useful abstraction we can apply to our world when we're thinking about the world in terms of these "things", these chunks of stuff that are bound together enough to act as a unit.

# basic boolean logic

# predicate logic?

# The Curry-Howard correspondence, how code can prove things

# set theory, and why it was superseded by type theory

# inductive types and proof objects

# coding with interactive tactics

# the difference between "logical" types and "computational" types


https://www.youtube.com/watch?v=56IIrBZy9Rc&ab_channel=BroadInstitute
https://www.youtube.com/watch?v=5e7UdWzITyQ&ab_channel=BroadInstitute
https://www.youtube.com/watch?v=OlkYNDRo2YE&ab_channel=BroadInstitute

https://x80.org/collacoq/


https://github.com/jscert/jscert

---


Is propositional logic required to reason about consistency? What underpins propositional logic?

I've been reading around about consistency and various paradoxes discovered in different logical systems (such as [Russell's paradox](https://plato.stanford.edu/entries/russell-paradox/)), and I'm being trying to figure out what it really *means* for something to be inconsistent. All the resources I can find on the topic just appeal back to basic propositional calculus by saying something about it being possible to derive some variant of `false` in the logic, but for some reason that's unsatisfying to me. If we need some ideas of true/false/contradiction in order to even do *metatheory*, then does that make the propositional calculus some kind of axiomatic bedrock for all of logic? Where's the "bottom" of our logical systems? Do we have one? Do different metatheorists simply disagree or use different systems?

To me it seems a true paradox like Russell's is worrying not because it's possible to derive a contradiction (is it possible to?), but because there are some situations *where we simply don't know what to do*. It seems these are merely problems of underspecification rather than inconsistency.

For example here's a dumb little logic that introduces an inconsistency, but only because we're specifying it in such informal language:

- There are constants `green`, `blue`.
- There is an operation `yo` which can take two of the above constants and output another one of the above constants.
  - `yo(x, x)` outputs x (`yo(green, green) -> green`, `yo(blue, blue) -> blue`).
  - If `green` is input to `yo`, the result must be `green`.
  - If `blue` is the second argument to `yo`, the result must be `blue`.

To me it doesn't make sense to say this logic is inconsistent, it just seems "poorly typed". If we were forced to actually encode our `yo` operation as a fully explicit list of input pairs along with output, there would be duplicates or gaps in the list depending on how we chose to ignore the problems in the logic. In coq we can't even get such a logic to type-check if we don't arbitrarily resolve the inconsistency:

```v
Inductive constant: Type := green | blue.
Definition yo c1 c2 :=
  match c1, c2 with
  (* these rules make sense *)
  | green, green => green
  | blue, blue => blue
  | blue, green => green
  (* here we have to just resolve the problems by choosing which rule "wins" *)
  | green, blue => blue
  end.

Notation valid_yo f := (
  (forall t, f t t = t)
  /\ (forall t, f green t = green)
  /\ (forall t, f t green = green)
  /\ (forall t, f t blue = blue)
).

Theorem valid_yo_impossible:
  forall yo, valid_yo yo -> False.
Proof.
  intros ? (_ & green_left & _ & blue_right).
  specialize (green_left blue).
  specialize (blue_right green).
  rewrite green_left in blue_right.
  discriminate.
Qed.
```

Could this potentially offer us an intuitive explanation of why strongly normalizing logics such as the calculus of constructions are consistent? Since their very structure demands operations to be fully explicit and complete and type-checkable it makes it impossible to even represent truly "inconsistent" terms? Is determinisic reduction the
