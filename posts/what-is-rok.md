Rok is a metaprogrammable dependently-typed language with an integrated abstract assembly language with trackable effects. This means it's the first and only language that brings together these capabilities:

- Fully Verifiable: Rok has an embedded dependently-typed proof checker much like [Coq]() or [Lean](). This means any logical property provable within the [Calculus of Constructions]() can be stated and proven in Rok, including the correctness of programs.
- Bare Metal Performance: Rok's internal library includes types and theorems formalizing [Von Neumann computation]() and assembly language execution, allowing it to be used to write and verify programs at the lowest level of software abstraction. This means even the most daring and high performance programs can be written, proven correct, and compiled in the same tool.
- Infinitely Flexible: Rok has extremely powerful and yet simple metaprogramming, allowing manipulation of proofs, functions, and data at compile time. Write verified proof tactics, plugins, and even embedded higher-level programming languages within Rok.

This combination of capabilities opens up possibilities we've only dared to imagine. Our limits in designing software have mostly been defined by the immense difficulty of safely and correctly composing code together, but using Rok any code can be arbitrarily composed. The basic assumptions of software architecture can be entirely reexamined and we can finally let our imaginations lead the way.

## Who is Rok for?

Rok has the absurdly ambitious goal of being a new universal substrate for all software! Since Rok is an *abstract* assembly language, it can theoretically compile correct programs for even the most obscure Von Neumann environments. The long term goal is for Rok to be used for embedded devices, normal application software, web programs, etc.






















# What is Rok and why is it important?

Rok is a dependently typed, metaprogrammable proof checker with an integrated abstract assembly language with trackable effects

This post is intended for anyone in the software engineering space, meant to persuade you we desperately need something like Rok and that the design choices it makes are the right ones to achieve our goals. If you want a deep dive on the technical design of Rok, please read [The Technical Design of Rok](), and if you want to feel what it would be like to learn Rok once it's finished, please read [Introduction to Rok]().


Includes things that can be built, some of which I intend to build.


Verified hardware simulators are easy with rok

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
we have to go all the way. anything less than the capabilities given by a full proof checker proving theories on the literal environment abstractions isn't going to be good enough, will always have bugs and hard edges and cases that can't be done. but those full capabilties can *contain* other more "ad hoc" things like fuzzers, quickcheck libraries, test generators, etc. we must build upon a rok!





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

Rok promises neither performance nor correctness nor consistency nor completeness, but instead promises the one thing that underlies all of those qualities: knowledge. Complete and total formal knowledge about the program you're writing.
Rok is simply a raw exposure of the basic elements of computing, in both the real sense of actual machine instructions and the ideal sense of formal logic. These basic elements can be combined in whatever way someone desires, even in the "worse-is-better" way! The main contribution of Rok is that the tradeoffs one makes can be made *and flagged*. Nothing is done without knowledge.


If you can prove it you can do it


The big ideas I have are these:
metaprogramming! upwards recombination is much more powerful than downwards compilation. allows truly global interoperability (zero cost, fully verified FFI)
indented syntax blocks. I know, it wouldn't seem like it! but the simple idea of being able to pass a block of text that has literally any syntax you want, without having to define crazy Notations and operator precedences etc, and since the end of that block is only inferred from indentation, that means this language can have *way more* expressive embedded notations than Coq could. Coq's notation system is fancy and complicated, and that's exactly the problem.
infecting "tokens" or propositions. this is basically what allows us to instantiate Iris with just a single language that's generic over exact instructions and the machine. we basically define our language to be the most generic concept of a von neumann machine, and then the exact nature of the instructions and machine take it from there.



Nested environments! the tradeoffs made while designing the operating system can directly inform the proof obligations and effects of nested environments



Why isn't (X) good enough?

- Rust. Not actually safe, at least within the boundaries of the tool itself.
- LLVM. Not actually safe, which also means its optimizations can't be as aggressive. Focuses on downwards compilation rather than upwards metaprogrammatic recombination. Perhaps abstracts too much of the machine away in certain circumstances.

- Coq
because of metacoq and ml extraction, coq *technically* could be used to do everything in this project. however it's important to note that metacoq defines metaprogramming in coq without extraction, which means it will always perform quite poorly. rok by comparison defines its metaprograming in terms of *compute* rok rather than *theory* rok, so it can perform extremely well.
but to be truly honest, the real reason coq isn't good enough is because *it has a truly punishing user experience*. it's not good enough for coq to be *powerful*, it has to be *approachable* to meet the goal of making formal verification common in engineering practice
using myself as an example, I'm an extremely determined and curious person who has been hell-bent on understanding both it and the theory behind it, but since I'm not being led through it in an academic context where all the implicit knowledge is exposed through in-person mentors, it has been extremely challenging
coq has existed *since the 80s* and is still a very niche tool mostly only used by academics or former academics. rust by comparison doesn't offer anywhere close to the correctness-proving power, and has only been a mature language since 2015, but has achieved truly impressive adoption.
the most damning accusation I can make against coq is that it isn't even that broadly adopted *in academia*. why aren't almost all papers in mathematics, logic, philosophy, economics, and computer science not verified in coq? and yet approachable tools like python and julia and matlab are much more common? extreme logical power is useless if it can't be readily accessed

- Lean
I'm frankly not even sure what lean adds over coq. It certainly makes a few better minor design decisions, but it isn't really promising to change the game in any way, at least not sufficiently that it's worth tossing out all the existing work in coq.

- F*, Liquid Haskell
not fully dependently typed

Our lowest level of abstraction defines the limits of our control
Coq is least suited to those applications for which it is most necessary. High performance situations like operating systems, embedded systems, safety critical systems are almost always extremely time and resource constrained, and so must have both the greatest amount of performance and correctness.

This project is seeking to solve these problems by creating a Tool, and a Community. The Tool is largely a technical work, but one we will try to build as intuitively and elegantly as possible (in contrast to existing academic tools). The Community includes governance and education materials.

- vale
focused on cryptographic code, and it isn't a new proof assistant with the intent to make formal verification go mainstream, but instead a library in an existing proof assistant meant to help crypto researchers
however this project does in a way hint that the rok project is a good idea! it is also generic over different architectures and uses automatic verification condition generators

- ivy http://microsoft.github.io/ivy/language.html
only first order

- bedrock
Proprietary! It's essential systems like this aren't only controlled by corporations and governments.
http://adam.chlipala.net/papers/BedrockICFP13/BedrockICFP13.pdf
https://plv.csail.mit.edu/bedrock/
https://bedrocksystems.com/products/
The original purely research version of bedrock is yet another project that is promising for the rok project, since it shows that verified *macros* are possible and tractable. However it's still stuck in coq and therefore slow and obtuse.

need to look at xcap paper and other references in the bedrock paper



Existing research around formal methods and program verification, such as in the deepspec project, I believe focuses extremely foolishly on old software workflows and tools. C and LLVM, despite being extremely powerful tools that profoundly advanced computing in their time, are still necessarily "legacy" tools, and so only very clunkily fit into formal verification. Even Rust, as modern as it is, wasn't ever designed with formal verification in mind from the beginning, and inherited many possibly unhelpful assumptions, such as the operating system syscall model, LLVM itself, and the C++ memory model.

The ability to fully verify any program down to the metal completely unlocks the kinds of systems and abstractions we can build! The very act of building such a powerful tool removes all non-negotiable barriers in our way.

Formally verifying the correctness of legacy systems after the fact is necessarily much more difficult than developing new tools from first principles with verification in mind. The only reason I can think of for the post-hoc philosophy is one of terrified pragmatism, where researchers and engineers are too scared to rethink layers that "seem to be working". This seems foolish to me, since we don't *actually* have any confidence those old layers are actually correct. If you start from the bottom and produce fully verified foundations, and every layer you stack on top is itself verified, I conjecture you can move much faster than trying to avoid or work-around bugs in existing legacy foundations.

That work only matters once it has been applied in a way that benefits the world.

The goal behind this project is to answer the question: what would we design if we started from scratch? Rok really is an attempt to lay a completely new foundation for all of computing that could be used to entirely rethink how every layer of software infrastructure works, all the way down to the bare metal.

## Why Do We Need More Verification?

### Safety and Correctness

Software is important, and we would like to have more confidence when using it for more critical applications.

### Bug Rate, Rework, and Velocity

One of the most frustrating experiences when trying to build something is to discover bugs or obvious gaps in a lower layer. When software you implicitly trust fails for reasons entirely beyond your control, you lose a huge amount of time, and those gaps almost always transitively produce gaps in *your* layer as well, continuing the harmful ripple effect.

Even if the correctness of some piece of software isn't "critical", its correctness is still helpful. its users can simply enjoy its power without interruptions or frustration. The overall velocity of all engineering work can improve dramatically when all layers are made more robust.

In exactly the same way that [`null` was a billion dollar mistake](TODO), general software incorrectness has probably cost trillions of dollars in lost productivity and potential progress.

## Why Will Rok Be Able to find mainstream success?

Mostly because of the metaprogramming, and the focus on upward recombination over downward translation. The language *itself* doesn't have to achieve mainstream success to massively improve the quality of all downstream software, but merely some sub-language. Many engineers have never heard of LLVM, but they still implicitly rely on it every day. Rok would seek to do the same.

We don't have to take full formal verification fully mainstream, we just have to make it available for the handful of people willing to do the work. If a full theorem prover is sitting right below the high-level language you're currently working in, you don't have to bother with it most of the time, but you still have the option to do so when it makes sense.

And of course we have to be humble. It might not work! Hopefully at the very least

We shouldn't be scared to put the power of a full proof checker into a computation focused language. Not everyone has to use it! And those who do don't have to use it all the time!

- Make it possible: at this moment in time, it isn't really even *possible* to fully verify a truly bare metal program on an arbitrary architecture. This stage focuses on creating the basic Rok compiler
  - define rok semantics and theories in coq
  - use extracted ml to compile first runnable version, so rok has been bootstrapped out of coq
  - complete rok from within
- Make it productive: bring the project to maturity, with tolerable compiler performance, broad architecture and context support, ergonomic tooling and libraries, good proof methodology, and solid documentation.
- Make it common: do evangelism, write books to spread rok into different domains, use the tool to create verified infrastructure and new programming environments.

## Verification Leverage

Verification is obviously very difficult. Although I have some modest theories about ways to speed up/improve automatic theorem proving, and how to teach verification concepts in a more intuitive way that can thereby involve a larger body of engineers, we still can't avoid the fact that refining our abstractions and proving theorems is hard and will remain so.

But we don't have to make verification completely easy and approachable to still get massive improvements. We only have to make the labor of researchers and experts more *available* and *reusable*. Since Rok is inherently metaprogrammable and integrates programming and proving, developments in one area of research can quickly disseminate through the entire language diaspora. Research would be much less likely to remain trapped in the ivory tower, and could be usefully deployed in real software much more quickly.

## Environment Genericity


## Effect-Aware Tokens and Gradual Correctness

One of the main innovations of Rust was introducing an extremely strict safety-oriented type system, but simultaneously acknowledging its limitations by still allowing `unsafe` operations. By explicitly acknowledging when the type system can't verify the correctness of program behavior, engineers are much better able to focus on potential problem spots in code. Projects such as [RustBelt](TODO) can then do further work to either increase the sophistication of the type system to allow a larger domain of correct programs, or semantically prove the correctness of `unsafe` operations "on the side". Many other languages also have such "trapdoors" in their type systems, such as [various unsafe operations in Haskell](TODO), [unchecked type coercions in languagess like C or Java](TODO), or [the `any` type in TypeScript](TODO).

These various trapdoors allow what we could call gradual correctness or gradual typing, and are pragmatic compromises between what is tractably verifiable and what must be done to write useful software. But these trapdoors have a critical problem: their use is often difficult to audit, control, or reject. Each language community usually must develop specialized linters to detect these uses, and even once their use has been detected, the only way to accept them with confidence is with time-consuming and unreliable human audits or fuzz testing.

However with a full proof checker embedded in a language, we can design these trapdoors with much more robustness.

Each basic block can be given a set of "effect tokens", some of which can be environment-specific. Each of these effect tokens essentially has a "pure" version representing correct and safe execution, and some set of "impure" versions representing incorrect or unsafe execution. Different instructions can then consume a token, and depending on if proofs of correct behavior have been provided, either return the pure or impure version. Since these instructions *consume* and then *return* a token (we don't need an affine logic to enable them), a program that contains some impure program effect, no matter how transitively, will be alerted to the fact that this has occurred. Different projects can choose to tie program correctness (and the success of their automated build process) to freedom from certain program effects. However the opposite is also true, and projects can choose to ignore possibly undesirable effects if such admissions are acceptable.

**Everything is permitted, but everything is checked.**

### Memory Safety

### Memory Leaks

### Execution Safety

### Termination/Liveness

### Type Soundness

### Program Failure

### Maximum Time/Memory Complexity

### Non-Blocking Execution

### System Calls



## Possible Ways to Improve Automated Proof Checking

checking assertions from the bottom up and in reverse instruction order, keeping track as we go of what assertions we're concerned with and only pulling along propositions with a known transformation path to those assertions.



## Intended Applications

Obviously a language that allows robust verification of any useful program will be an obvious fit for critical software of all kinds, such as blockchains/smart contracts, cryptography, firmware, operating systems, language runtimes, financial/legal/medical applications, web servers, databases, etc. Check out [this blog post](TODO my personal essay describing my long journey and the half finished projects toward Rok)

But there are a few specific uses I'm personally excited to pursue once this language is functional.

high-level but statically lowered asynchronous actor-first borrow-checked language, ideal for application domains and high-level targets like webassembly and operating system environments. inspired by ponylang and its awareness of actor boundaries to allow aliasing in the presence of mutation
http://jtfmumm.com/blog/2016/03/06/safely-sharing-data-pony-reference-capabilities/
I like this:

```
Pony takes a different approach and outlaws infix precedence. Any expression where more than one infix operator is used must use parentheses to remove the ambiguity. If you fail to do this the compiler will complain.
```

metaprogrammable databases

verified tree-like reactivity frameworks. especially doable with smarter actor-graph-aware lifetime systems

semver enforcing package managers

safe foreign code execution without sandboxing

new operating system paradigms
when it's possible to check foreign code for safety, completely new ways of thinking about operating systems open up
capability-typed micro kernel

universal typed messaging format
