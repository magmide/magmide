```
(*https://www.cs.cmu.edu/~fp/papers/mfps89.pdf*)

Inductive MyEq {T: Type}: T -> T -> Prop :=
  | EqSelf: forall t, MyEq t t.

Definition MyEq_inductive_manual
  (T: Type) (P: T -> T -> Prop)
  (f: forall t: T, P t t) (l r: T)
  (m: MyEq l r)
: P l r :=
  match m in (MyEq l r) return (P l r) with
  | EqSelf t => f t
  end.


Inductive MyAnd (P Q: Prop): Prop :=
  | my_and: P -> Q -> MyAnd P Q.

Definition MyAnd_inductive_manual
  (P Q R: Prop) (f: P -> Q -> R) (evidence: MyAnd P Q)
: R :=
  match evidence with
  | my_and _ _ p q => f p q
  end.


Inductive MyOr (P Q: Prop): Prop :=
  | my_or_left: P -> MyOr P Q
  | my_or_right: Q -> MyOr P Q.

Definition MyOr_inductive_manual
(P Q R: Prop) (f_left: P -> R) (f_right: Q -> R) (evidence: MyOr P Q)
: R :=
  match evidence with
  | my_or_left _ _ l => f_left l
  | my_or_right _ _ r => f_right r
  end.


Inductive MyBool: Type :=
  | my_true
  | my_false.

Definition MyBool_inductive_manual
  (P: MyBool -> Prop) (P_my_true: P my_true) (P_my_false: P my_false)
: forall (b: MyBool), P b :=
  fun b =>
    match b with
    | my_true => P_my_true
    | my_false => P_my_false
    end.

Definition my_eq_manual: MyEq my_true my_true := EqSelf my_true.

Fail Definition my_eq_manual_bad: MyEq my_true my_false := EqSelf my_true.
Fail Definition my_eq_manual_bad: MyEq my_true my_false := EqSelf my_false.
Fail Definition my_eq_manual_bad: MyEq my_false my_true := EqSelf my_true.
Fail Definition my_eq_manual_bad: MyEq my_false my_true := EqSelf my_false.

Inductive MyFalse: Prop := .

Definition my_true_not_false_manaul: (MyEq my_true my_false) -> MyFalse :=
  fun wrong_eq => match wrong_eq with
  | EqSelf t =>
  end

Definition MyNot (P: Prop) := P -> MyFalse.

Definition my_not_false_manual: MyNot MyFalse :=
  fun my_false => match my_false with end.

Definition my_ex_falso_quodlibet: forall (P: Prop), MyFalse -> P :=
  fun (P: Prop) (my_false: MyFalse) => match my_false return P with end.

Definition my_true_not_false_manaul: MyNot (MyEq my_true my_false) :=
  fun wrong_eq =>
    match wrong_eq in (MyEq l r)
    return
      match l with
      | my_true =>
        match r with
        | my_true => True
        | my_false => MyFalse
        end
      | my_false => True
      end
    with
    | EqSelf t => match t as t with
      | my_true => I
      | my_false => I
      end
    end.

Print my_true_not_false_manaul.
```










https://arxiv.org/pdf/2105.12077.pdf



https://github.com/coq/coq/wiki/TheoryBehindCoq


need to look at xcap paper and other references in the bedrock paper

https://plv.csail.mit.edu/blog/iris-intro.html#iris-intro
https://plv.csail.mit.edu/blog/alectryon.html#alectryon











Verified hardware simulators are easy with magmide

Engineers want tools that can give them stronger guarantees about safety robustness and performance, but that tool has to be tractably usable and respect their time

This idea exists in incentive no man's land. Academics won't think about it or care about it because it merely applies existing work, so they'll trudge along in their tenure track and keep publishing post hoc verifications of existing systems. Engineers won't think about or care about it because it can't make money quickly or be made into a service or even very quickly be used to improve some service
This is an idea that carries basically zero short term benefits, but incalculable long term ones, mainly in the way it could shift the culture of software and even mathematics and logic if successful.
This project is hoping and gambling that it itself won't even be the truly exciting innovation, but some other project that builds upon it, and that wouldn't have happened otherwise. I'm merely hoping to be the pair of shoulders someone else stands on, and I hope the paradigm shift this project creates is merely assumed to be obvious, that they'll think we were insane to write programs and not prove them correct




https://mattkimber.co.uk/avoiding-growth-by-accretion/
Most effects aren't really effects but environmental capabilities, although sometimes those capabilities come with effects



Traits, shapes, and the next level of type inference

Discriminated unions and procedural macros make dynamically typed languages pointless, and they've existed for eighty years. So what gives?

What's better than a standard? An automatically checkable and enforceable standard


https://project-oak.github.io/rust-verification-tools/2021/09/01/retrospective.html
we have to go all the way. anything less than the capabilities given by a full proof checker proving theories on the literal environment abstractions isn't going to be good enough, will always have bugs and hard edges and cases that can't be done. but those full capabilties can *contain* other more "ad hoc" things like fuzzers, quickcheck libraries, test generators, etc. we must build upon a magmide!





stop trying to make functional programming happen, it isn't going to happen

## project values

- **Correctness**: this project should be a flexible toolkit capable of verifying and compiling any software for any architecture or environment. It should make it as easy as possible to model the abstractions presented by any hardware or host system with full and complete fidelity.
- **Clarity**: this project should be accessible to as many people as possible, because it doesn't matter how powerful a tool is if no one can understand it. To guide us in this pursuit we have a few maxims: speak plainly and don't use jargon when simpler words could be just as precise; don't use a term unless you've given some path for the reader to understand it, if a topic has prerequisites point readers toward them; assume your reader is capable but busy; use fully descriptive words, not vague abbreviations and symbols.
- **Practicality**: a tool must be usable, both in terms of the demands it makes and its design. This tool is intended to be used by busy people building real things with real stakes.
- **Performance**: often those programs which absolutely must be fast are also those which absolutely must be correct. Infrastructural software is constantly depended on, and must perform well.

These values inherently reinforce one another. As we gain more ability to guarantee correctness, we can make programs faster and solve more problems. As our tools become faster, they become more usable. Guaranteeing correctness saves others time and headache dealing with our bugs. As we improve clarity, more people gather to help improve the project, making it even better in every way.

secondary values, simplicity before consistency before completeness.

cultural values, code of conduct, we're accepting and open and humble.


```
In the spirit of Richard Gabriel, the Pony philosophy is neither "the-right-thing" nor "worse-is-better". It is "get-stuff-done".

Correctness
Incorrectness is simply not allowed. It's pointless to try to get stuff done if you can't guarantee the result is correct.

Performance
Runtime speed is more important than everything except correctness. If performance must be sacrificed for correctness, try to come up with a new way to do things. The faster the program can get stuff done, the better. This is more important than anything except a correct result.

Simplicity
Simplicity can be sacrificed for performance. It is more important for the interface to be simple than the implementation. The faster the programmer can get stuff done, the better. It's ok to make things a bit harder on the programmer to improve performance, but it's more important to make things easier on the programmer than it is to make things easier on the language/runtime.

Consistency
Consistency can be sacrificed for simplicity or performance. Don't let excessive consistency get in the way of getting stuff done.

Completeness
It's nice to cover as many things as possible, but completeness can be sacrificed for anything else. It's better to get some stuff done now than wait until everything can get done later.

The "get-stuff-done" approach has the same attitude towards correctness and simplicity as "the-right-thing", but the same attitude towards consistency and completeness as "worse-is-better". It also adds performance as a new principle, treating it as the second most important thing (after correctness).

https://www.ponylang.io/discover/#what-is-pony
```

Overall the difference between "the-right-thing" and "worse-is-better" can be understood as the difference between upfront and marginal costs. Doing something right the first time is an upfront cost, and once paid decreases marginal costs *forever*.
The main problem in software, and the reason "worse-is-better" has been winning in an environment of growth-focused viral capitalism, was that it was basically impossible in practice to actually do something the right way! Since our languages haven't ever supported automatic verification we could only hope to weakly attempt to understand what correct even meant and then actually implement it. This meant the cost to chase the truly right thing was unacceptably uncertain.

Magmide promises neither performance nor correctness nor consistency nor completeness, but instead promises the one thing that underlies all of those qualities: knowledge. Complete and total formal knowledge about the program you're writing.
Magmide is simply a raw exposure of the basic elements of computing, in both the real sense of actual machine instructions and the ideal sense of formal logic. These basic elements can be combined in whatever way someone desires, even in the "worse-is-better" way! The main contribution of Magmide is that the tradeoffs one makes can be made *and flagged*. Nothing is done without knowledge.


If you can prove it you can do it


Nested environments! the tradeoffs made while designing the operating system can directly inform the proof obligations and effects of nested environments

Possible Ways to Improve Automated Proof Checking

checking assertions from the bottom up and in reverse instruction order, keeping track as we go of what assertions we're concerned with and only pulling along propositions with a known transformation path to those assertions.















https://dl.acm.org/doi/abs/10.1145/3453483.3454084
https://ocamlpro.github.io/verification_for_dummies/
https://arxiv.org/abs/2110.01098





In most of these heap-enabled lambda calculi "allocation" just assumes an infinite heap and requires an owned points-to connective in order to read.
In the real assembly language, you can always read, but doing so when you don't have any idea what the value you're reading just gets you a machine word of unknown shape, something like uninit or poison. How can I think about this in Magmide? Are there ever programs that intentionally read garbage? That's essentially always random input. Probably there's just a non-determinism token-effect you want.

My hunch about why my approach is going to prove more robust then continuation-passing-style is because it doesn't seem cps can really directly understand programs as mere data, or would need special primitives to handle it, whereas in my approach it's given, which makes sense since again we're merely directly modeling what the machine actually does.

yeah, lambda rust is amazing, but it's very tightly coupled to the way rust is implemented for host operating system programs. I don't think it's flexible enough to handle arbitrary machine/instruction definitions. it also can't handle irreducible control flow graphs, which absolutely could be created either with `goto` programs or by compiler optimizations that we want to be able to formally justify.

with incremental verification it probably makes sense to allow possible data races (they don't result in a stuck state) but token flag them
the interesting thing is that certain kinds of token problems, such as memory unsafety, data races, overflow, non-termination, actually invalidate the truth of triples! a program doesn't have enough certainty to guarantee *anything* if it isn't basically safe.



Someone needs to do for formal verification what rust has been doing for systems programming

Think about sections that are irrevocably exiting, such as sequential sections capped by an always exiting instruction either branch or jump always out or falling through to next, and you can prove that such sections and concatenations of them always in a well founded way exit the section and relate that to steps relation, and then all you need for sections that are self recursive is a well founded relation and a proof that for all steps that self recurse that only stay within the section that have a triple making progress then the section will always exit in a well founded way
You can probably generalize this to whole programs if the steps relation is just parameterized by the section not the program

Metaprogramatically embedded dsl




https://www.youtube.com/watch?v=ybrQvs4x0Ps



https://arxiv.org/abs/2007.00752
> In this work, we perform a large-scale empirical study to explore how software developers are using Unsafe Rust in real-world Rust libraries and applications. Our results indicate that software engineers use the keyword unsafe in less than 30% of Rust libraries, but more than half cannot be entirely statically checked by the Rust compiler because of Unsafe Rust hidden somewhere in a library's call chain. We conclude that although the use of the keyword unsafe is limited, the propagation of unsafeness offers a challenge to the claim of Rust as a memory-safe language. Furthermore, we recommend changes to the Rust compiler and to the central Rust repository's interface to help Rust software developers be aware of when their Rust code is unsafe.



http://www.fstar-lang.org/tutorial/

```
Lexicographic orderings
F* also provides a convenience to enhance the well-founded ordering << to lexicographic combinations of <<. That is, given two lists of terms v₁, ..., vₙ and u₁, ..., uₙ, F* accepts that the following lexicographic ordering:

v₁ << u₁ \/ (v₁ == u₁ /\ (v₂ << u₂ \/ (v₂ == u₂ /\ ( ... vₙ << uₙ))))
is also well-founded. In fact, it is possible to prove in F* that this ordering is well-founded, provided << is itself well-founded.

Lexicographic ordering are common enough that F* provides special support to make it convenient to use them. In particular, the notation:

%[v₁; v₂; ...; vₙ] << %[u₁; u₂; ...; uₙ]
is shorthand for:

v₁ << u₁ \/ (v₁ == u₁ /\ (v₂ << u₂ \/ (v₂ == u₂ /\ ( ... vₙ << uₙ))))
Let’s have a look at lexicographic orderings at work in proving that the classic ackermann function terminates on all inputs.

let rec ackermann (m n:nat)
  : Tot nat (decreases %[m;n])
  = if m=0 then n + 1
    else if n = 0 then ackermann (m - 1) 1
    else ackermann (m - 1) (ackermann m (n - 1))
The decreases %[m;n] syntax tells F* to use the lexicographic ordering on the pair of arguments m, n as the measure to prove this function terminating.




Mutual recursion
F* also supports mutual recursion and the same check of proving that a measure of the arguments decreases on each (mutually) recursive call applies.

For example, one can write the following code to define a binary tree that stores an integer at each internal node—the keyword and allows defining several types that depend mutually on each other.

To increment all the integers in the tree, we can write the mutually recursive functions, again using and to define incr_tree and incr_node to depend mutually on each other. F* is able to prove that these functions terminate, just by using the default measure as usual.

type tree =
  | Terminal : tree
  | Internal : node -> tree

and node = {
  left : tree;
  data : int;
  right : tree
}

let rec incr_tree (x:tree)
  : tree
  = match x with
    | Terminal -> Terminal
    | Internal node -> Internal (incr_node node)

and incr_node (n:node)
  : node
  = {
      left = incr_tree n.left;
      data = n.data + 1;
      right = incr_tree n.right
    }

Note
Sometimes, a little trick with lexicographic orderings can help prove mutually recursive functions correct. We include it here as a tip, you can probably skip it on a first read.

let rec foo (l:list int)
  : Tot int (decreases %[l;0])
  = match l with
    | [] -> 0
    | x :: xs -> bar xs
and bar (l:list int)
  : Tot int (decreases %[l;1])
  = foo l

What’s happening here is that when foo l calls bar, the argument xs is legitimately a sub-term of l. However, bar l simply calls back foo l, without decreasing the argument. The reason this terminates, however, is that bar can freely call back foo, since foo will only ever call bar again with a smaller argument. You can convince F* of this by writing the decreases clauses shown, i.e., when bar calls foo, l doesn’t change, but the second component of the lexicographic rdering does decrease, i.e., 0 << 1.
```

```
bool is_even(unsigned int n) {
  if (n == 0) return true;
  else return is_odd(n - 1);
}

bool is_odd(unsigned int n) {
  if (n == 0) return false;
  else return is_even(n - 1);
}
```






https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf
https://gitlab.mpi-sws.org/iris/tutorial-popl21
https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/heap_lang.md
https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/proof_mode.md




I like the idea of having a `by` operator that can be used to justify passing a variable as some type with the accompanying proof script. so for example you could say `return x by crush`, or more complicated things such as `return x by (something; something)`. whatever level of automatic crushing should the system do by default? should there be a cheap crusher that's always used even without a `by`, and `by _` means "use a more expensive crusher"? or does no `by` mean to defer to a proof block? it makes sense to me for no `by` to imply simply deferring (trying to pass something as a type we can quickly verify it can't possibly be is just a type error), whereas `by _` means "use the crusher configured at this scope", and something like file/module/section/function/block level crushers can be configured
a small and easy to use operator for embedding the proof language into the computational language would probably go a long way to making Magmide popular and easy to understand.

it would probably be nice to have some shorthand for "extending" the proof value of functions and type aliases. something like `fn_name ;theorem` or something that implies adding the assumptions of the thing and the thing itself into the context of the proof, and adds the new proof for further use.


look at koka lang
what magmide can add is *unannotated* effects. polymorphic effects in a language like koka seem (at first glance) to require annotation, whereas in magmide they are simply implied by the `&` combination of assertions that is inherent to what a type is.
a problem with effectual control flow is that we almost never actually *care* about control flow differences. effects in koka seem to me to be too obsessed with "purity" in the pedantic functional programming sense, rather than in the *logical correctness* sense. I don't terribly care if a subfunction causes yield effects or catches internal exceptions, I care about its performance and if it is correct or not. magmide is concerned with *correctness* effects, as in whether a function "poisons" the program with possible divergence or crashes or other issues. if a sub function does *potentially* dangerous things but internally proves them and it doesn't impact performance in a way I need to be aware of, then I don't care. well, it looks like they *largely* understand that.
what I don't love though is how obsessed they are with effect handlers, to the extent they have `fun` and `val` variants **that are equivalent to just passing down a closure or value!** I guess it allows the effect giving functions to be used in more contexts than would be possible if they just required a function or value
value capabilities seem cool, but in a world where we can verify everything, a global variable is in fact totally acceptable. hmmm
here's my main takeaway from koka: I actually think it's pretty cool, but I think it's important to distinguish *control flow* effects from *correctness* effects. they have completely different purposes. in fact I'm hesitant to call what koka has effects at all, they're more like "contextual handlers" or something. maybe it's better just to call what *I'm* adding something else.

Honestly it's pretty cool what koka had implemented. But I'm not as excited about it for async, because async code isn't really an effect the more I think about it.
Async is a type level manifestation of a completely different mode of execution, in which execution is driven primarily by closures rather than by simple function execution. The program must be completely altered in terms of what data structures it produces and how they are processed
Algebraic effects don't save us! Just be because the async effect can theoretically be composed with any other effect type doesn't mean that's actually a good choice. Async is all about recapturing and efficiently using io downtime to do more cpu work. A program simply must be structured differently in order to actually achieve that goal, and designating
A function that actually awaits anything has now been effectively colored! It doesn't matter that other effects can exist alongside it, any calling function must either propogate the effect or handle it, which is exactly equivalent to how it works in rust
The thing that bothers me about the red blue complaint is that it is just ignoring the reality that async programs have to be structured differently if you want to gain the performance benefits. Async functions merely prod engineers to make the right choices given that constraint
They're of course free to do whatever they like, they can just block futures sequentially, or use the underlying blocking primitives, or use a language with transparent async, but they'll pick up the performance downsides in each case. But as they say you can choose to pick up one end of the stick but not the other
I'm feeling more and more that other abstractions handle some of these specific cases better, at least from the perspective of how easy they are to reason about
For example the fun and val versions of koka effects can be thought of as implicit arguments that can be separately passed in a different tuple of arguments. This is the same as giving a handler, but with stricter requirements about resumption which means we don't have to think about saving the stack. If some implicit arguments default to a global "effectful" function, then a call of that function with that default will itself have that effect
Magmide could do algebraic effects but monomorphize all the specific instances, making them zero cost. All of this can be justified using branching instructions
Functions could use a global "unsure" function equivalent to panic but that takes a symbol and a message and the default implicit value of this function is merely an instantiation of panic that ignores the symbol. Calling functions can provide something to replace the implicit panic and have it statically monomorphized




The term "gradual verification" is useful to sell people on what's unique about this project. Magmide is tractable for the same reasons something like typescript or mypy is tractable.




An exciting idea, of having the "language" be generic over a *machine*, which includes possibly none or many register (a bit array of known length) or memory location (also a bit array of known length, which accounts for architecture alignment) banks (a possibly infinite list), and a concrete instruction set. Then we can understand the "language" to just be a set of common tools and rules for describing machines.

Some nice things follow from this:

- "artifical" machines such as those supported by a runtime of some sort are easily described
- machines can have multiple register and memory banks of different sizes, and dependent types could allow us to have different access rules or restrictions or semantics for them each. metaprogramming can "unbundle" these banks into simple names if that makes sense.
- it becomes pretty simple to check if a machine is "abstract" or "concrete", by determining if all the sizes of register/memory banks are known or unknown (or possibly the correct thing is finite vs infinite?). with that information we can add alerts or something if the memory allocation function of an abstract machine isn't somehow fallible (in a concrete machine, failure to allocate is actually just a program failure! it has a more concrete meaning of having too much data of a specific kind. this concrete semantic failure in a concrete machine is what "bubbles up" to create an infinite but fallible allocation instruction in an abstract machine)






I'm starting to think that what I'm really designing is more a *logic* for typed assembly languages. it's not *quite* like llvm precisely, because to really correctly compile to each individual instruction set, those instruction sets have to be fully specified!
it seems I'm more moving toward a general logic with a *toolbox* of abstract instruction semantics, each of which can be tied concretely to actual applications. but the full instruction set of any architecture can be specified in full.
it really does point toward having a few different "families" of programs:

- embedded programs, in which the exact specifications are known up front
- os programs? ones here the instruction set can be known but things like memory sizes aren't?
- runtime programs, ones where some existing environment is already provided, often allowing looser assumptions

probably what we want is a "general core" of instructions we assume every machine has some equivalent for, which we can build the more "higher level" languages on top of. then to write a "backend" someone would fully specify the instruction set and tie the real instructions to the general core ones, at least if they wanted to be able to support the higher level languages








https://www.ralfj.de/blog/2020/12/14/provenance.html
john regehr office hours



- dependent type proof checker with purely logical `prop` and `set?` types
- definition of bits and bit arrays that are given special treatment
- definition of representation of logical types by bit arrays
- prop of a "machine representable" type. since we can represent props as bit arrays, these can be represented
- some syntactic metaprogramming commands, which can take basic syntactic structures like strings or tokens or identifiers and transform them into commands or other instructions
- some semantic metaprogramming commands, which can operate on variables or identifiers or whatever to extract compile time information about them such as their type

- abstract instructions that are able to operate on bit arrays (for now we take as given that these abstract instructions can be validly encoded as bit arrays with a known size, since llvm will actually do the work of translating them for now. in the future we'll absorb what llvm does by creating a system of concrete "hardware axioms" that represent the instruction set and memory layout etc of a real machine, and a mapping from the abstract instructions to these concrete ones. in the immediate future we'll also need "operating system" axioms, at least until there are operating systems built in bedrock that can simply be linked against)
- formalization of instruction behaviors, especially control flow, locations, and allocation, and investigations into the well-foundedness of recursive locations


---

Random theorizing about syntax:

```
fn debug value;
  match known(value).type;
    struct(fields) =>
      for key in fields;
        print("#{key}: #{value[key]}")
    nat(n) => print(n)
    bool(b) => print(b)
```

---

basically this project will have a few large steps:

first we'll define some really basic proof of concept of a theory of known types. this first version will basically just use the "computable terms are a subset of terms, and we only bother to typecheck terms once we've fully reduced them to computable terms". there are a million ways to go about doing this, so we'll just keep it really simple. we'll do this in a "simply typed lambda calculus" so it's easy to reason about.

we'd probably want to demonstrate that this pattern can handle literally any meta-programming-like pattern, including:

- generics
- bounded generics
- higher-kinded generics (demonstrate a monad type?)
- macros of all kinds

probably our definition of preservation and soundness etc would be a little more nuanced. we'd probably also require the assumption that the known functions reduced "correctly", something that would depend on the situation


all computable types as simply a bit array with some predicate over that bit array. with this we can define n-ary unions, tuples, structs, the "intersection" type that simply "ands" together predicate of the two types

then we can get more interesting by having "pre" typechecks. really what we would be doing there is just trying to allow people authoring higher order "known" functions to prove their functions correct, rather than simply relying on the "this known function will eventually reduce to some terms and *those* terms will be typechecked :shrug:". Basically we want these kinds of authors to have strong typing for their things as well, in a way that goes beyond just typechecking the actual "type value" structs that they happen to be manipulating
we can think about it this way: in languages like rust, macros just input/output token streams. from a meta-programming perspective, that's like a program just operating on bytestreams at both ends. we want people to be able to type their known functions just as well as all the *actual* functions. what this can allow us to do is typecheck a program, and know *even before we've reduced certain known functions* that those known functions aren't being used appropriately in their context, and won't reduce to terms that will typecheck. in a language that's formally verified, we can then even potentially do the (very scary) potentially very performance enhancing task of *not actually bothering to typecheck the outputs of these known functions*. if we've verified the pre-conditions of the known function, and we have a proof that the known function will always output terms having some particular type, we can just take that type as a given


after we've defined the semantics of types that consist *only* of bit arrays with a predicate, we can start actually defining the language semantics. the big things are n-ary unions and match statements, module paths and the dag, type definition syntax etc. but also the very interesting and potentially massive area of figuring out how we can prove that a loop (or family of co-recursive functions) will always terminate. since this language would have a rich proof system, doing that can actually be tractable and useful from the perspective of programmers.
lexicographic ordering of stack arguments ["Proving termination"](http://www.fstar-lang.org/tutorial/).

defining and proving correct a type inference algorithm


then we have all the cool little ideas:

- the "infecting" types of certain operations. we want infecters for code that potentially panics, diverges, accesses out of bounds memory (unsound), accesses uninitialized memory (unsafe?), or leaks any "primitive" resource (we could make this generic by having some kind of predicate that is "optional" but as a result of being optional infects the result type. so someone could write a library that has optional invariants about the caller needing to give back resources or something like that, and you can represent a program that doesn't maintain these invariants, but then your types will get infected. perhaps a more interesting way to do this is simply by understanding that any predicate over a type that *doesn't actually make any assertions about the type value's byte array* is like this?). it's probably also true that if we do this "infecting" correctly, we can notice programs where *it's certain* that some infected type consequence will happen, and we can warn programmers about it.

- a "loop" command that's different than the "while" command, in the sense that the program doesn't ask for any proof that a "loop" will always terminate, since it's assumed that it might not. we can still maybe have some finer-grained check that simply asks if a loop construct has any code after it, and if it does there has to be *some* way of breaking out of the loop (other than the process being forcefully terminated, such as by receiving some control signal), or else that code is all dead.

- with a tiny language that's so flexible, we can define and reason about a host of ergonomic sugars and optimizations.

- all the little syntax things you like, such as the "block string", the different ways of calling and chaining functions, the idea of allowing syntax transforming known functions (or "keywords") and of allowing these kinds of functions to be attached as "members" of types for maximum ergonomics and allowing things like custom "question mark" effectful operators.

- in our language we can define "stuckness" in a very different way, because even very bad things like panics or memory unsafe operations aren't *stuck*, they're just *infected*. this means that the entire range of valid machine code can be output by this language. this probably means the reasonable default return type of the `main` function of a program (the one that we will assume if they don't provide their own) should be `() | panic`, so we only assume in the common case that the program might be infected with the panic predicate but not any of the "unsoundness" ones.

- "logical" vs normal computable types. logical types would basically only be for logic and verification, and not have any actual output artifacts, which means that all the values inhabiting logical types have to be known at compile time, and we can cheat about how efficient they are to make it more convenient to write proofs about them

- wouldn't it be cool to connect proofs about this language to existing verification efforts around llvm?





for co-recursive functions: we can create graphs of dependencies between functions, and we can group them together based on how strongly connected they are. for example

here we mean that a and b both reference the other (and potentially themselves), so once we enter this group we might never leave
(a - b)

but if a and b point to some other function c, if c doesn't reference a or b (or any function that references a or b), then we'll never visit that group of a and b ever again, *but c might be co-recursive with some other family of functions*. however it's still useful in this situation to understand that we have in some important way *made progress in the recursion*.
it seems that the important idea of a co-recursive family of functions is that from any of the functions you could go through some arbitrary set of steps to reach any of the other functions.


if we unbundle both functions and the loops/conditionals into mere basic blocks like in llvm, then it's possible to do this graph analysis over the entire program in the same way. with some interesting new theories about what it means to make progress towards termination *in data* rather than *in control flow*, we can merge the two to understand and check if programs are certainly terminating.
we can also unbundle the idea of "making progress in data" to "making progress in predicates", since our types are basically only defined as predicates over bit arrays.






after all this, we really start to think about the proof checker, and how the proof aspect of the language interacts with the known functions.
the simplest thing to notice is that theorems are just known functions that transform some instantiation of a logical type (so all the values of the logical type are known at compile time) to a different type.
the more interesting thing to notice is that the same kind of really slick "tacticals" system that's included in coq can just be *fallible* functions that take props and try to produce proofs of them. this means that the "typecheck" function that the compiler actually uses when compiling code should be exposed to all functions (and therefore of course the known functions), and that it should return some kind of `Result` type. that way tacticals can just call it at will with the proofs they've been constructing, and return successfully if they find something the core typechecking algorithm is happy with.




---


read introduction to separation logic

the biggest way to make things more convenient for people is to have the *certified decision procedures* described by CPDT in the form of the type checking functions!!! that means that certain macros or subportions of the language that fit into some decidable type system can just have their type checking function proven and provided as the proof object!


rather than have many layers of "typed" compilers each emitting the language of the one below it as described in the foundational proof carrying code paper, we simply have *one* very base low level language with arbitrarily powerful metaprogramming and proof abilities! we can create the higher level compilers as embedded constructs in the low level language. we're building *up* instead of *down*.


https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/cs818A3-11.html
(here now: 3.12 More about Annotated Specifications)
https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/ch3.pdf

https://en.wikipedia.org/wiki/Bunched_logic
http://www.lsv.fr/~demri/OHearnPym99.pdf

https://arxiv.org/pdf/1903.00982.pdf
https://aaronweiss.us/pubs/popl19-src-oxide-slides.pdf

the real genius of rust is education! people can understand separation logic and formal verification if we teach them well!

a basic theory of binary-representable types would also of course be incredibly useful here.
it seems that carbon could be specified completely by defining the simple `bit` type, and the basic tuple/record, union, and intersection combinators (it seems that intersection types can/should only be used between named records, and to add arbitrary logical propositions to types? it might make sense to only use intersection (as in `&`) for propositions, and have special `merge` and `concat` etc type transformer known functions to do the other kinds of operations people typically think of as being "intersection". then `&` is simple and well-defined and can be used to put any propositions together? it might also function nicely as the syntactic form for declaring propositions, instead of `must`, so `type Nat = int & >= 0`)

logical propositions are so powerful that they could be the entire mode of specifying the base types! booleans are just a `byte` or whatever with props asserting that it can only hold certain values. traits are just props asserting that there exists an implementation in scope satisfying some shape. and of course arbitrary logical stuff can be done, including separation logic/ghost state type things.

a reason to include the same kind of constructive inductive propositions is because it provides two ways of attacking

a theory of "known" types that allows known functions to produce data structures representing these types is probably the most important first step. it seems you could prove that known types are general enough to provide the language with generics, all kinds of macros, and then dramatically expands the reach of usual static type systems by providing "type functions", which allow arbitrary derivations (you can easily do rust derived traits) and mapping, which allows for the kind of expressivity that typescript mapped and conditional types allows

a general truth to remember about the goals of carbon is to remember what really made rust successful. it didn't shy away from complexity, and it didn't water down what people were capable of achieving, but it did find clean abstractions for complex things, and *especially* it did an amazing job **teaching** people how those concepts work. an amazing next generation language is equal parts good language/abstraction design and pedagogy. if you give people a huge amount of power to build incredible things, *and* you do an excellent job teaching them both how to use and why they should use it, then you've got an amazing project on your hands.

also very important, and something that the academics have *miserably* failed to do (in addition to their language design and the teaching materials, both of which are usually absolutely dreadful), is building the *tooling* for the language. the tools (think `cargo`) and community infrastructure (think the crates system) are probably *more* important on average for the success of a language community than the language itself. people won't use even the most powerful language if it's an absolute godawful chore to accomplish even the smallest thing with it

another thing the academics don't realize and do wrong (especially in coq) is just their conventions for naming things! in Coq basic commands like `Theorem` are both inconveniently capitalized and fully spelled out, but important variable names that could hint to us about the semantic content of a variable are given one letter names! that's completely backwards from a usability standpoint, since commands are something we see constantly, can look up in a single manual, and can have syntax highlighters give us context for; whereas variable names are specific to a project or a function/type/proof. shortening `Theorem` to `th` is perfectly acceptable, and lets us cut down on syntax in a reasonable place so we aren't tempted to do so in unreasonable places. `forall` could/should be shortened to something like `fa` or even a single character like `@`. `@(x: X, y: Y)` could be the "forall tuple", equivalent to `forall (x: X) (y: Y)`

## building a proof checker!
https://cstheory.stackexchange.com/questions/5836/how-would-i-go-about-learning-the-underlying-theory-of-the-coq-proof-assistant
https://www.irif.fr/~sozeau/research/publications/drafts/Coq_Coq_Correct.pdf
https://github.com/coq/coq/tree/master/kernel

you should almost certainly do everything you can to understand how coq works at a basic level, and read some of the very earliest papers on proof checkers/assistants to understand their actual machinery. hopefully the very basics are simple, and most of the work is defining theories etc on top. hopefully the footprint of the actual checker is tiny, and it's the standard libraries and proof tactics and such that really create most of the weight

theory of known types
carbon (and various projects in carbon) (when thinking about the compiler and checking refinement/dependent types, it probably makes sense to use an SMT solver for only the parts that you can't come up with a solid algorithm for, like the basic type checking, or to only fall back on it when some simple naive algorithm fails to either prove or disprove)

https://www.cs.princeton.edu/~appel/papers/fpcc.pdf
https://www.google.com/books/edition/Program_Logics_for_Certified_Compilers/ABkmAwAAQBAJ?hl=en&gbpv=1&printsec=frontcover

https://www3.cs.stonybrook.edu/~bender/newpub/2015-BenderFiGi-SICOMP-topsort.pdf


https://hal.inria.fr/hal-01094195/document
https://coq.github.io/doc/V8.9.1/refman/language/cic.html
https://ncatlab.org/nlab/show/calculus+of+constructions
https://link.springer.com/content/pdf/10.1007%2F978-0-387-09680-3_24.pdf ????


https://softwarefoundations.cis.upenn.edu/lf-current/ProofObjects.html
has a little portion about type-checking and the trusted base, reassuring



"Given a type T, the type Πx : T, B will represent the type of dependent
functions which given a term t : T computes a term of type B[t/x] corresponding to proofs of
the logical proposition ∀x : T, B. Because types represent logical propositions, the language will
contain empty types corresponding to unprovable propositions.
Notations. We shall freely use the notation ∀x : A, B instead of Πx : A, B when B represents
a proposition."

theorems are just *dependently* typed functions! this means there's a nice "warning" when people construct propositions that don't use their universally quantified arguments, the propositions are vacuous or trivial and don't prove anything about the input.



a big reason unit tests are actually more annoying and slower in development is the need for fixture data! coming up with either some set of examples, or some fixture dataset, or some model that can generate random data in the right shape is itself a large amount of work that doesn't necessarily complement the actual problem at hand. however proving theorems about your implementation is completely complementary, the proofs lock together with the implementation exactly, and you can prove your whole program correct without ever running it! once someone's skilled with the tool, that workflow is massively efficient, since they never have to leave the "code/typecheck" loop.
also, proof automation is actually *much more general and easier* than automation of testing. with testing, you need to be able to generate arbitrarily specific models and have checking functions *that aren't the same as the unit under test*. doing that is a huge duplication of effort.



probably ought to learn about effect systems as well

an infecting proposition for a blocking operation in an async context is a good idea



https://www.cs.cmu.edu/~rwh/papers/dtal/icfp01.pdf
http://www.ats-lang.org/
looking at dml and xanadu might be good

a very plausible reason that projects like dependently-typed-assembly-language and xanadu and ats haven't worked, is that smart separation logic wasn't there yet, and those languages didn't have powerful enough metaprogramming!

in bedrock, the actual *language* can literally just be a powerful dependently typed assembly language along with the arbitrarily powerful meta-programming allowed by known types and some cool "keyword"-like primitives, but then the *programmer facing* language can have structs and functions and all the nice things we're used to but all defined with the meta-programming! the meta-programming is the thing that really allows us to package the hyper-powerful and granular dependent type system into a format that is still usable and can achieve mass adoption. in this way we can kinda call this language "machine scheme/lisp".


a mistake everyone's been making when integrating dependant/refinement types into "practical" languages is requiring that only first order logic be used, and therefore that the constraints are *always* automatically solvable. We can still keep those easy forms around just by checking if they're applicable and then using them, but some people need/want more power and we should just give it to them! they'll be on their own to provide proofs, but that's fine!
we're really making this tradeoff: would we rather have a bunch of languages that are easy to use but lack a bunch of power that makes us routinely create unsafe programs, or occasionally encounter a problem that's a huge pain in the ass to formalize correctness but we're still capable of doing so? I think we definitely want the second! And we can make abstractions to allow us to work in the first area for a subset of easily-shaped problems but still directly have "escape hatches" to the more powerful layer underneath. a full proof checker in a language gives us the exciting option to always include in our meta languages a direct escape hatch right down into the full language!




as a future thing, the whole system can be generic over some set of "hardware axioms" (the memory locations and instructions that are intrinsic to an architecture), along with functions describing how to map the "universal" instructions and operations into the hardware instructions. an "incomplete" mapping could be provided, and compiling programs that included unmapped universal instructions would result in a compiler error






this is interesting, he's making a lot of the same arguments I am
https://media.ccc.de/v/34c3-9105-coming_soon_machine-checked_mathematical_proofs_in_everyday_software_and_hardware_development
https://github.com/mit-plv/bedrock2

http://adam.chlipala.net/frap/frap_book.pdf
