This project is seeking to solve these problems by creating a Tool, and a Community. The Tool is largely a technical work, but one we will try to build as intuitively and elegantly as possible (in contrast to existing academic tools). The Community includes governance and education materials.




Existing research around formal methods and program verification, such as in the deepspec project, I believe focuses extremely foolishly on old software workflows and tools. C and LLVM, despite being extremely powerful tools that profoundly advanced computing in their time, are still necessarily "legacy" tools, and so only very clunkily fit into formal verification. Even Rust, as modern as it is, wasn't ever designed with formal verification in mind from the beginning, and inherited many possibly unhelpful assumptions, such as the operating system syscall model, LLVM itself, and the C++ memory model.

Formally verifying the correctness of legacy systems after the fact is necessarily much more difficult than developing new tools from first principles with verification in mind. The only reason I can think of for the post-hoc philosophy is one of terrified pragmatism, where researchers and engineers are too scared to rethink layers that "seem to be working". This seems foolish to me, since we don't *actually* have any confidence those old layers are actually correct. If you start from the bottom and produce fully verified foundations, and every layer you stack on top is itself verified, I conjecture you can move much faster than trying to avoid or work-around bugs in existing legacy foundations.

That work only matters once it has been applied in a way that benefits the world.

The goal behind this project is to answer the question: what would we design if we started from scratch? Rok really is an attempt to lay a completely new foundation for all of computing that could be used to entirely rethink how every layer of software infrastructure works, all the way down to the raw metal.

## Why Do We Need More Verification?

### Safety and Correctness

Software is important, and we would like to have more confidence when using it for more critical applications.

### Bug Rate, Rework, and Velocity

One of the most frustrating experiences when trying to build something is to discover bugs or obvious gaps in a lower layer. When software you implicitly trusted fails for reasons entirely beyond your control, you lose a huge amount of time, and those gaps almost always transitively produce gaps in *your* layer as well, continuing the harmful ripple effect.

Even if the correctness of some piece of software isn't "critical", its correctness is still helpful, allowing all its users to simply enjoy its power without interruptions or frustration. The overall velocity of all engineering work can improve dramatically when all layers are made more robust.

In exactly the same way that [`null` was a billion dollar mistake](TODO), general software incorrectness has probably cost trillions of dollars in lost productivity and potential progress.

## Why Will Rok Be Able to find mainstream success?

Mostly because of the metaprogramming, and the focus on upward recombination over downward translation. The language *itself* doesn't have to achieve mainstream success to massively improve the quality of all downstream software, but merely some sub-language. Many engineers have never heard of LLVM, but they still implicitly rely on it every day. Rok would seek to do the same.

We don't have to take full formal verification fully mainstream, we just have to make it available for the handful of people willing to do the work. If a full theorem prover is sitting right below the high-level language you're currently working in, you don't have to bother with it most of the time, but you still have the option to do so when it makes sense.

And of course we have to be humble. It might not work! Hopefully at the very least

We shouldn't be scared to put the power of a full proof checker into a computation focused language. Not everyone has to use it! And those who do don't have to use it all the time!

## Verification Leverage

Verification is obviously very difficult. Although I have some modest theories about ways to speed up/improve automatic theorem proving, and how to teach verification concepts in a more intuitive way that can thereby involve a larger body of engineers, we still can't avoid the fact that refining our abstractions and proving theorems is hard and will remain so.

But we don't have to make verification completely easy and approachable to still get massive improvements. We only have to make the labor of researchers and experts more *available* and *reusable*. Since Rok is inherently metaprogrammable and integrates programming and proving, developments in one area of research can quickly disseminate through the entire language diaspora. Research would be much less likely to remain trapped in the ivory tower, and could be usefully deployed in real software much more quickly.

## Environment Genericity


## Effect-Aware Tokens and Gradual Correctness

One of the main innovations of Rust was introducing an extremely strict safety-oriented type system, but simultaneously acknowledging its limitations by still allowing `unsafe` operations. By explicitly acknowledging when the type system can't verify the correctnes of program behavior, engineers are much better able to focus on potential problem spots in code. Projects such as [RustBelt](TODO) can then do further work to either increase the sophistication of the type system to allow a larger domain of correct programs, or semantically prove the correctness of `unsafe` operations "on the side". Many other languages also have such "trapdoors" in their type systems, such as [various unsafe operations in Haskell](TODO), [unchecked type coercions in languagess like C or Java](TODO), or [the `any` type in TypeScript](TODO).

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

Obviously a language that allows robust verification of any useful program will be an obvious fit for critical software of all kinds, such as blockchains/smart contracts, cryptography, firmware, operating systems, language runtimes, financial/legal/medical applications, web servers, databases, etc. But there are a few specific uses I'm personally excited to pursue once this language is functional.

high-level but statically lowered asynchronous actor-first borrow-checked language, ideal for application domains and high-level targets like webassembly and operating system environments

metaprogrammable databases

verified tree-like reactivity frameworks

semver enforcing package managers

safe foreign code execution without sandboxing

new operating system paradigms
when it's possible to check foreign code for safety, completely new ways of thinking about operating systems open up

universal typed messaging format
