# **:construction: :construction: Magma is purely a research project at this point**

This repo is still very early and rough, it's mostly just notes, speculative writing, and exploratory theorem proving. All the files in this repo other than this readme are "mad scribblings" territory, so dive in at your own risk! In this file however I give a broad overview and answer a few possible questions. Enjoy!

---

The goal of this project is to: **create a programming language and surrounding education/tooling ecosystem capable of making formal verification and provably correct software mainstream and normal among working software engineers**.

Software is an increasingly critical component of our society, underpinning almost everything we do. It's also extremely vulnerable and unreliable. Software vulnerabilities and errors have likely caused humanity trillions of dollars in damage, social harm, waste, and lost growth opportunity in the digital age (I think [Tony Hoare's estimate](https://en.wikipedia.org/wiki/Tony_Hoare#Apologies_and_retractions) is way too conservative, especially if you include more than `null` errors). What would it look like if it was both possible and tractable for working software engineers to build and deploy software that was *provably correct*?

I strongly believe a world with such a capability would not only see a significant improvement in *magnitude* of social good produced by software, but a significant improvement in *kind* of social good. In the same way that Rust gave engineers much more capability to safely compose arbitrary pieces of software therefore enabling them to confidently build much more ambitious systems, a language that gives them the ability to automatically check arbitrary conditions will make safe composition and ambitious design arbitrarily easier to do correctly.

What kinds of ambitious software projects have been conceived but not pursued because getting them working would simply be too difficult? With machine checkable proofs in many more hands could we finally build *truly secure* operating systems, trustless networks, decentralized ledgers, or even electronic voting systems? How many people could be making previously unimagined contributions to computer science, mathematics, and even other logical fields such as economics and philosophy if only they had approachable tools to do so? Read [my blog post discussing my journey to this project and what I intend to build with it once its mature](https://blainehansen.me/post/my-path-to-magma/) if you're interested in a more personal view of these questions.

This is a huge goal, and a language capable of achieving it will need a strong design with the right capabilities. In my opinion in order to achieve this goal a language must be all of these things:

## Fully verifiable

In order to really deliver the kind of truly transformative correctness guarantees that will inspire working engineers to learn and use a difficult new language, it doesn't make sense to stop short and only give them an "easy mode" verification tool. It should be possible to formalize and attempt to prove any proposition humanity is capable of representing logically, not only those that a fully automated tool like an [SMT solver](https://liquid.kosmikus.org/01-intro.html) can figure out. A language with full logical expressiveness can still use convenient automation alongside manual proofs.

To achieve this goal, the language is fully **dependently typed** and uses the [Calculus of Constructions](https://en.wikipedia.org/wiki/Calculus_of_constructions) much like [Coq](https://en.wikipedia.org/wiki/Coq).

## Capable of bare metal performance

Software needs to perform well! Not all software has the same requirements, but often performance is intrinsically tied to correct execution. Very often the software that most importantly needs to be correct also most importantly needs to perform well. If the language is capable of truly bare metal performance, it can still choose to create easy abstractions that sacrifice performance where that makes sense.

To achieve this goal, the language includes in its core libraries a formalization of the basic principles of von neumann computation, allowing users to specify the axiomatic assumptions of any software execution environment, from concrete instruction set architectures, to any **abstract assembly language** such as LLVM capable of compiling to many targets, and even up to operating system userlands or bytecode environments such as webassembly. Making it possible to specify software at this level of fidelity ensures it is truly aligned with reality and isn't making unrealistic assumptions.

Verifying raw assembly code is much more difficult than verifying a mathematically pure language, but recent advancements such as the [Iris higher-order concurrent separation logic](https://iris-project.org/) have finally made this goal truly achievable.

## Gradually verifiable

Just because it's *possible* to fully verify all code, doesn't mean it should be *required*. It simply isn't practical to try to completely rewrite a legacy system in order to verify it. Successful languages with goals of increased rigor such as Rust and Typescript strategically use concessions in the language such as `unsafe` and `any` to allow more rigorous code to coexist with legacy code as it's incrementally replaced. The only problem is that these concessions introduce genuine soundness holes into the language, and it's often difficult or impossible to really understand how exposed your program is to these safety holes.

We can get both practical incremental adoption and complete understanding of the current safety of our program by leveraging work done by the [Iron obligation management logic](https://iris-project.org/pdfs/2019-popl-iron-final.pdf) built using Iris. We can use a concept of **trackable effects**, where a piece of some "token" has to be given up in order to perform a dangerous operation without justifying its safety with a proof. This "infects" the violating code block with an effect type that will bubble up through any parent blocks. Project teams can choose how strict they want the effects of their program to be, some choosing to fail compilation if a program isn't memory safe or could panic, and others tolerating some possible effects or writing proofs to assert that these effects only happen in certain well-defined circumstances. New kinds of trackable effects can even be defined and used, allowing different projects to introduce new kinds of safety and correctness tracking, such as ensuring asynchronous code doesn't block the executor, or a web app doesn't render raw untrusted input, or a server doesn't leak secrets.

Importantly, even if some piece of software chooses to ignore some negative effects, other projects will be automatically informed of those negative effects if they try to use that software. We can have a genuinely secure trustless software ecosystem!

## Deeply metaprogrammable

We can't write all software in assembly language! Including first-class support for powerful metaprogramming, alongside a [query-based compiler](https://ollef.github.io/blog/posts/query-based-compilers.html), will allow users of this language to build abstractions that "combine upward" into higher levels, while still allowing the possibility for those higher levels to "drop down" back into the lower levels. Being a proof assistant, these escape hatches don't have to be "unsafe", as higher level code can provide proofs to the lower level to justify its actions.

The metaprogramming can of course also be used directly in the dependently typed language, allowing compile-time manipulation of proofs, functions, and data. Verified proof tactics, macros, and higher-level embedded programming languages are all possible.

Importantly, this language is self-hosting, so metaprogramming functions benefit from the same bare metal performance and full verifiability.

## Practical and ergonomic

My experience using languages like Coq has been extremely painful, and the interface is "more knife than handle". I've been astounded how willing academics seem to be to use extremely clunky workflows and syntaxes just to avoid having to build better tools.

To achieve this goal, this project will learn heavily from `cargo` and other excellent projects. It should be possible to verify, interactively prove, query, compile, and run any magma code with a single tool.

## Taught effectively

Working engineers are resource constrained and don't have years of free time to wade through arcane and disconnected academic papers, or use haphazard or clunky tooling. Academics aren't incentivized to properly explain and expose their amazing work, and a massive amount of [research debt](https://distill.pub/2017/research-debt/) has accrued in many fields, including formal verification.

To achieve this goal, this project will enshrine the following values in regard to teaching materials:

- Speak to a person who wants to get something done and not a review committee evaulating academic merit.
- Put concrete examples front and center.
- Point the audience toward truly necessary prerequisites rather than assuming shared knowledge.
- Prefer graspable human words to represent ideas, never use opaque and unsearchable non-ascii symbols, and only use symbolic notations when it's both truly useful and properly explained.
- Prioritize the hard work of finding clear and distilled explanations.

# FAQ

## Is it technically possible to build a language like this?

Yes! None of the technical details of this idea are untested or novel. Dependently typed proof languages, higher-order separation logic, query-based compilers, introspective metaprogramming, and abstract assembly languages are all ideas that have been proven in other contexts. Magma would merely attempt to combine them into one unified and usable package.

## Will working engineers actually use it?

Maybe! We can't force people or guarantee it will be successful, but we can learn a lot from how Rust has been able to successfully teach quite complex type-theoretical ideas to an huge and excited audience. I think Rust has succeeded by:

- *Making big promises* in terms of how performant/robust/safe the final code will be.
- *Delivering* on those promises by making something awesome. I hope that since the entire project will have verification in mind from the start it will be easier to ship something excellent and robust with less churn than usual.
- *Respecting people's time* by making the teaching materials clear and distilled and the tooling simple and ergonomic.

All of those things are easier said than done! Fully achieving those goals will require work from a huge community of contributors.

## Is this language trying to replace Rust?

No! My perfect outcome of this project would be for it to sit *underneath* Rust, acting as a new verified toolchain that Rust could "drop into". The concepts and api of Rust are awesome and widely loved, so Magma would just try to give it a more solid foundation. Wouldn't it be cool to be able to *prove* that your use of `unsafe` wasn't actually unsafe??

## Why not just write this stuff in Coq?

Simply? Because Coq has made a lot of bad design decisions.

Metaprogramming is [technically possible in Coq](https://github.com/MetaCoq/metacoq), but it was grafted on many years into the project, and it feels like it. The language is extremely cluttered and obviously "designed by accretion". All the documentation and introductory books were clearly written by academics who have no interest in helping people with deadlines build something concrete. The Notation system just begs for unclear and profoundly confusing custom syntax, and is itself extremely overengineered. It's a pure functional language with a garbage collector, so it will never perform as well as a self-hosted bare metal compiler. And let's be honest, the name "Coq" is just terrible.

I don't intend to throw away all the awesome work done by the Coq project though, which is why the first bootstrapping compiler and initial theory will be written in Coq, and I intend to (someday) create some kind of backport to allow old Coq code to be read and used by Magma. But I'm unwilling to be bound to Coq's design.

This question is a lot like asking the Rust project creators "why not just write a specialized C compiler"? Because instead of making something *awesome* we'd have to drag around a bunch of bad decisions. Sometimes it's worth it to start again.

## Do you really think all engineers are going to write proofs for all their code?

No! And honestly, doing so would probably be a huge waste of time. Not all software has the same constraints, and it would be dumb to try to verify a recipe app with the same level of rigor as a crypography function.

But even a recipe app would benefit from the *foundations* it sits on being much more verified. I imagine something like a "verification pyramid" with excruciatingly verified software at the bottom, going up through less verified code all the way to throwaway scripts that aren't even tested. At the bottom even the tiniest details such as the possibility of integer overflow must be explicitly accounted for, and at the top we just do a basic and highly inferred type-check. Every layer can rely on the safety of abstractions underneath to not worry about certain kinds of error conditions and only verify what they feel they need to.

Basically, the less important a piece of software is and the easier it is to change, the less verified it needs to be.

## Won't writing verified software be way more expensive? Do you actually think this is worth it?

**Emphatically yes it is worth it.** As alluded to earlier, bmagmaen software is a massive drain on our society. Even if it were much more expensive to write verified software, it would still be worth it. Rust has already taught us that it's almost always worth it to [have the hangover first](https://www.youtube.com/watch?v=ylOpCXI2EMM&t=565s&ab_channel=Rust) rather than wastefully churn on a problem after you thought you could move on.

And of course, a big goal of the project is to make verification less expensive! Tooling, better education, better algorithms and abstractions can all decrease verification burden. If the project ever reaches maturity these kinds of improvements will likely be most of the continued effort for a long time.

Besides, many projects already write [absolutely gobs of unit tests](https://softwareengineering.stackexchange.com/questions/156883/what-is-a-normal-functional-lines-of-code-to-test-lines-of-code-ratio), and a proof is literally *infinitely* better than a unit test. At this point I'm actually hopeful that proofs will *decrease* the cost of writing software. We'll see.

## Do you think this language will make all software perfectly secure?

No! Although it's certainly [very exciting to see how truly secure verified software can be](https://www.quantamagazine.org/formal-verification-creates-hacker-proof-code-20160920/), there will always be a long tail of hacking risk. Not all code will be written in securable languages, not all engineers will have the diligence or the oversight to write secure code, people can make bad assumptions, and brilliant hackers might invent entirely new *types* of attack vectors that aren't considered by our safety specifications. However *any* verified software is better than *none*, and right now it's basically impossible for a security-conscious team to even attempt to prove their code secure. Hopefully the "verification pyramid" referred to earlier will enable almost all software to quickly reuse secure foundations provided by someone else.

And of course, social engineering and hardware tampering are never going away, no matter how perfect our software is.

## How far are you? What remains to be done?

Very early, and basically everything remains to be done! I've been playing with models of very simple assembly languages to get my arms around formalization of truly imperative execution. Especially interesting has been what it looks like to prove some specific assembly language program will always terminate, and to ergonomically discover paths in the control flow graph which require extra proof justification. I have some raw notes and thoughts about this in [`posts/toward-termination-vcgen.md`](./posts/toward-termination-vcgen.md). Basically I've been playing with the design for the foundational computational theory.

In [`posts/design-of-magma.md`](./posts/design-of-magma.md) I have some rough thoughts about what the project's major milestones would be. The obvious first milestone is to create a bootstrapping compiler capable of compiling the first self-hosted version. That will likely happen in Coq in some way, but I haven't deeply thought it through. There are several ways to go about it, and I don't think I am far enough to clearly see the best path.

## This is an exciting idea! How can I help?

Just reach out! Since things are so early there are many questions to be answered, and I welcome any useful help. Feedback and encouragement are also welcome.

If you would like to get up to speed with formal verification and Coq enough to contribute at this stage, you ought to read [Software Foundations](https://softwarefoundations.cis.upenn.edu/), [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/html/Cpdt.Intro.html), [this introduction to separation logic](http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/Marktoberdorf11LectureNotes.pdf), and sections 1, 2, and 3 of the [Iris from the ground up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf) paper. You might also find my unfinished [introduction to verification and logic in Magma](./posts/intro-verification-logic-in-magma.md) useful, even if it's still very rough.

Here's a broad map of all the mad scribblings in this repo:

- `theorems` contains exploratory Coq code, much of which is unfinished. This is where I've been playing with designs for the foundational computational theory.
- `posts` has a lot of speculative writing, mostly to help me nail down the goals and design of the project.
- `notes` has papers on relevant topics and notes I've made purely for my own learning.
- `notes.md` is a scratchpad for raw ideas, usually ripped right from my brain with very little editing.
- `README.future.md` is speculative writing about a "by example" introduction to the language. I've been toying with different syntax ideas there, and have unsurprisingly found those decisions to be the most difficult and annoying :cry:

Thank you! Hope to see you around!
