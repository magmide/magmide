# :construction: Magmide is purely a research project at this point :construction:

This repo is still very early and rough, it's mostly just notes, speculative writing, and exploratory theorem proving. Most of the files in this repo are just "mad scribblings" that I haven't refined enough to actually stand by!

In this file however I give a broad overview and answer a few possible questions. Enjoy!

---

The goal of this project is to: **create a programming language and surrounding education/tooling ecosystem capable of making formal verification and provably correct software mainstream among working software engineers**.

Software is an increasingly critical component of our society, underpinning almost everything we do. It's also extremely vulnerable and unreliable. Software vulnerabilities and errors have likely caused humanity [trillions of dollars](https://www.it-cisq.org/pdf/CPSQ-2020-report.pdf) in damage, [social harm](https://findstack.com/hacking-statistics/), waste, and [lost growth opportunity](https://raygun.com/blog/cost-of-software-errors/) in the digital age (it seems clear [Tony Hoare's estimate](https://en.wikipedia.org/wiki/Tony_Hoare#Apologies_and_retractions) is way too conservative, especially if you include more than `null` errors). What would it look like if it was both possible and tractable for working software engineers to build and deploy software that was *provably correct*?

I strongly believe a world with such a capability would not only see a significant improvement in *magnitude* of social good produced by software, but a significant improvement in *kind* of social good. In the same way that Rust gave engineers much more capability to safely compose pieces of software therefore enabling them to confidently build much more ambitious systems, a language that gives them the ability to automatically check arbitrary conditions will make safe composition and ambitious design arbitrarily easier to do correctly.

What kinds of ambitious software projects have been conceived but not pursued because getting them working would simply be too difficult? With machine checkable proofs in many more hands could we finally build *truly secure* operating systems, trustless networks, decentralized ledgers, or even electronic voting systems? How many people could be making previously unimagined contributions to computer science, mathematics, and even other logical fields such as economics and philosophy if only they had approachable tools to do so? I speculate about some possibilities at the end of this readme.

This is a huge goal, and a language capable of achieving it will need a strong design with the right capabilities. In my opinion in order to achieve this goal a language must be all of these things:

## Fully verifiable

In order to really deliver the kind of truly transformative correctness guarantees that will inspire working engineers to learn and use a difficult new language, it doesn't make sense to stop short and only give them an "easy mode" verification tool. It should be possible to formalize and attempt to prove any proposition humanity is capable of representing logically, not only those that a fully automated tool like an [SMT solver](https://liquid.kosmikus.org/01-intro.html) can figure out. A language with full logical expressiveness can still use convenient automation alongside manual proofs.

To achieve this goal, the language will be fully **dependently typed** and use the [Calculus of Constructions](https://en.wikipedia.org/wiki/Calculus_of_constructions) much like [Coq](https://en.wikipedia.org/wiki/Coq). I find [Adam Chlipala's "Why Coq?"](http://adam.chlipala.net/cpdt/html/Cpdt.Intro.html) arguments convincing in regard to this choice. Coq will also be used to bootstrap the first version of the compiler, allowing it to be self-verifying in addition to self-hosting. Read more about the design and bootstrapping plan in [`posts/design-of-magmide.md`](./posts/design-of-magmide.md).

The [metacoq](https://github.com/MetaCoq/metacoq) and ["Coq Coq Correct!"](https://www.irif.fr/~sozeau/research/publications/drafts/Coq_Coq_Correct.pdf) projects have already done the work of formalizing and verifying Coq using Coq, so they will be very helpful while implementing Magmide.

## Capable of bare metal performance

Software needs to perform well! Not all software has the same requirements, but often performance is intrinsically tied to correct execution. Very often the software that most importantly needs to be correct also most importantly needs to perform well. If the language is capable of truly bare metal performance, it can still choose to create easy abstractions that sacrifice performance where that makes sense.

To achieve this goal, the language will include in its core libraries a formalization of the basic principles of von Neumann computation, allowing users to specify the axiomatic assumptions of any software execution environment, from concrete instruction set architectures, to any **abstract assembly language** such as LLVM capable of compiling to many targets, and even up to operating system userlands or bytecode environments such as webassembly. Making it possible to specify software at this level of fidelity helps ensure it is aligned with reality and isn't making unrealistic assumptions.

Verifying raw assembly code is much more difficult than verifying a mathematically pure language, but recent advancements such as the [Iris higher-order concurrent separation logic](https://iris-project.org/) have finally made this goal truly achievable.

## Gradually verifiable

Just because it's *possible* to fully verify all code, doesn't mean it should be *required*. It simply isn't practical to try to completely rewrite a legacy system in order to verify it. Successful languages with goals of increased rigor such as Rust and Typescript strategically use concessions in the language such as `unsafe` and `any` to allow more rigorous code to coexist with legacy code as it's incrementally replaced. The only problem is that these concessions introduce genuine soundness gaps into the language, and it's often difficult or impossible to really understand how exposed your program is to these safety gaps.

We can get both practical incremental adoption and complete understanding of the current safety of our program by leveraging work done by the [Iron obligation management logic](https://iris-project.org/pdfs/2019-popl-iron-final.pdf) built using Iris. We can use a concept of **trackable effects**, where a piece of some "token" has to be given up in order to perform a dangerous operation without justifying its safety with a proof. This would "infect" the violating code block with an effect type that will bubble up through any parent blocks. Project teams could choose how strict they want the effects of their program to be, some choosing to fail compilation if a program isn't memory safe or could panic, others tolerating some possible effects or writing proofs to assert that these effects only happen in certain well-defined circumstances, or writing code that is provably capable of sandboxing effects so they don't propagate further.

New kinds of trackable effects could even be defined and used, allowing different projects to introduce new kinds of safety and correctness tracking, such as ensuring asynchronous code doesn't block the executor, or a web app doesn't render raw untrusted input, or a server doesn't leak secrets.

Importantly, even if some piece of software chooses to ignore some negative effects, other projects could be automatically informed of those negative effects if they try to use that software. We can have a genuinely secure trustless software ecosystem!

## Deeply metaprogrammable

We can't write all software in assembly language! Including first-class support for powerful metaprogramming, alongside a [query-based compiler](https://ollef.github.io/blog/posts/query-based-compilers.html), will allow users of this language to build abstractions that "combine upward" into higher levels, while still allowing the possibility for those higher levels to "drop down" back into the lower levels. Being a proof assistant, these escape hatches don't have to be "unsafe", as higher level code can provide proofs to the lower level to justify its actions.

The metaprogramming can of course also be used directly in the dependently typed language, allowing compile-time manipulation of proofs, functions, and data. Verified proof tactics, macros, and higher-level embedded programming languages are all possible. This is the layer where absolutely essential proof automation tactics similar to Coq's `auto` or [Adam Chlipala's `crush`](http://adam.chlipala.net/cpdt/html/Cpdt.Intro.html), or fast counter-example searchers such as `quickcheck` would be implemented.


Importantly, the language will be self-hosting, so metaprogramming functions will benefit from the same bare metal performance and full verifiability.

You can find rough notes about the current design thinking for the metaprogramming interface in [`posts/design-of-magmide.md`](./posts/design-of-magmide.md).

## Practical and ergonomic

My experience using languages like Coq has been extremely painful, and the interface is "more knife than handle". I've been astounded how willing academics seem to be to use extremely clunky workflows and syntaxes just to avoid having to build better tools.

To achieve this goal, this project will learn heavily from `cargo` and other excellent projects. It should be possible to verify, interactively prove, query, compile, and run any Magmide code with a single tool.

An important design choice that will likely make the tool easier to understand and use is the "Logic/Host" split [(discussed deeply in `posts/design-of-magmide.md`)](./posts/design-of-magmide.md) that clearly separates "imaginary" pure functional code from the "real" imperative computational code.

## Taught effectively

Working engineers are resource constrained and don't have years of free time to wade through arcane and disconnected academic papers. Academics aren't incentivized to properly explain and expose their amazing work, and a massive amount of [research debt](https://distill.pub/2017/research-debt/) has accrued in many fields, including formal verification.

To achieve this goal, this project will enshrine the following values in regard to teaching materials:

- Speak to a person who wants to get something done and not a review committee evaulating academic merit.
- Put concrete examples front and center.
- Point the audience toward truly necessary prerequisites rather than assuming shared knowledge.
- Prefer graspable human words to represent ideas, never use opaque and unsearchable non-ascii symbols, and only use symbolic notations when it's both truly useful and properly explained.
- Prioritize the hard work of finding clear and distilled explanations.


<!-- use cases

## just doing logic/mathematics, not intending to create runnable programs

although it would seem this use case doesn't need to be able to check/compile/run computable programs, the user might still use metaprogramming to manipulate proofs, or use libraries that do. before sending the Logic Magmide structures representing the code being worked on to the kernel, any metaprogrammatic constructs need to be unfolded, which means the Host Magmide programs that are implied by those metaprogrammatic constructs need to be checked/compiled/run.

the flow for codebases like this would be: parse into data structures, check/compile/run any meta programs using the built in Host Magmide algorithms, send fully unfolded Logic Magmide structures to the kernel

this means that the compiler needs to have built in notions of some known Host Magmide. the truly final version of Magmide can have the *syntax* of some layer/variant of Host Magmide built in rather than always nesting Host Magmide underneath metaprogrammatic entry points

## writing code intended to run on the same architecture as the host

here all we need is the same Host Magmide used within the compiler. the user doesn't have to do anything unusual, they just need to write Host Magmide that's somehow "marked" as the "main" entry point

of course prop predicates can be indexed by host types/values, so Host Magmide will include custom entry points/sugars for assertions about code state that assumes these indexed predicates. assertions about host values are just logical props but more specific versions of them.

so there's the *ideal* definition of a computable type, which is just a predicate about binary arrays
this ideal definition must itself be represented computationally, so in memory it will be shaped in whatever way we decide to represent inductive types (probably with some array of values with tags and index offsets to avoid having pointers to different parts of memory and improve cache locality)
then at the runtime of the target program, the real bits will just be formed according to how the predicate demanded they would be

## cross-compiling code for a different architecture, but written in Host Magmide

same as above, they just have to somehow signal what architecture(s) are intended

## compiling code using a completely different compute language, one incompatible with Host Magmide

in order to do this, the user has to specify ast datatypes for their language. they have to do this in Host Magmide, since these datatypes need to be computationally represented and manipulated.

they can optionally choose to create macros to convert some custom syntax into these ast datatypes, and if they do this these macros will be in Host Magmide.

they will almost certainly define logical specifications for their host architecture, the machine type, how their ast datatypes relate to these things, and probably (definitely?) purely imaginary logical datatypes that model the real computational ones, and all of this will be done in Logic Magmide. Logic Magmide terms aren't really intended to be "computed", only evaluated using the reduction rules with an interpreter inside (alongside?) the kernel.

they need to be able to render/assemble their program, and they have to provide a custom rendering function. this step is ultimately a meta one, since "compile time" refers to compilation of the target program! so compilation is really just running a metaprogram that happens to produce some artifact. looking back at the more "normal" use cases we can see that those are just the same thing, except the path at each step was more known. the only thing that really distinguishes this use case from the others is that the ast/specifications/renderer were all provided custom.

but the logical stuff is the thing that's confusing. should logic Prop types be indexable by Host datatypes?

remember, at the very bottom of all of this is just the Host Magmide *logic types*. logical inductive types are at the bottom of the tree. those types are just modeling a real computational machine state and making assertions about it.
when we make assertions about "host types", we aren't making assertions about *it*, but about the machine state it represents?

it's silly to get hung up on whether Host Magmide types/values can be asserted by the Prop universe, because of course they can! host types are just predicates over binary arrays, and host values are just binary arrays. to say that some host value is equal to another is the exact same as saying two ideal values are equal. in both cases they're *definitionally* equal in the strict coq convertibility sense. -->

# FAQ

## Is it technically possible to build a language like this?

Yes! None of the technical details of this idea are untested or novel. Dependently typed proof languages, higher-order separation logic, query-based compilers, introspective metaprogramming, and abstract assembly languages are all ideas that have been proven in other contexts. Magmide would merely attempt to combine them into one unified and practical package.

## Why use Coq to bootstrap the compiler?

The biggest reason is that Coq is the language [Iris](https://gitlab.mpi-sws.org/iris/iris/) is implemented in, and since that project will be a core component of Magmide it makes the most sense to be as compatible as possible. Iris will likely need to be ported to Magmide once it's bootstrapped, so it would be nice to avoid also porting it to the bootstrapping language.

## Is this design too ambitious? Is it just "everything and the kitchen sink"?

This design is indeed very ambitious and broad, but here's my claim: none of the major features could be removed or weakened and still allow the project to achieve its goals. Every major design feature has intentionally been "maxed out", and chosen to nicely interlock with the others in a way that covers the largest possible number of use cases. If these features weren't the strongest versions of themselves we would be leaving power on the table that we don't have to, and we'd just be wasting time before some other better design shows up in a few years. All these design features are tractable, so we shouldn't stop short. It should be necessary for truly mind-blowing breakthroughs in logic or computational theory to appear before we have to revisit this design.

There are only three major design features that hold up everything else:

- **Maxed out in logical power** by using the strongest type theory I can find. Without this the design wouldn't be able to handle lots of interesting/useful/necessary problems, and couldn't be adopted by many teams. It wouldn't be able to act as a true *foundation* for verified computing. It's important to note that this one design feature enables all the other features involving formal logic, such as the ability to formalize bare metal computation at a high level of abstractness and the use of trackable effects.
- **Maxed out in computational power** by self-hosting in a bare metal language. If the language were interpreted or garbage collected then it would always perform worse than is strictly possible. It would be silly for metaprogramming to be done in a different language than the intended target languages. If we're going to formalize bare metal computation, we might as well use it to build the tool itself!
- **Maxed out in expressive power** by making it deeply metaprogrammable from the beginning. Metaprogramming is basically a cheat code for language design, since it gives a language access to an infinite range of possible features without having to explicitly support them. It's the single best primitive to add in terms of implementation overhead versus expressiveness. Making the compiler query-based maxes out metaprogrammatic capability, since every bit of work done in the core compiler can be exposed for reuse.

The most reasonable criticism you can make of Magmide is that it's too ambitious, but we have to also consider the opposite: perhaps previous projects haven't been ambitious enough, and that's why formal verification is still niche! Software has been broken for too long, and we won't have truly solved the problem until it's possible and tractable for *all* software to be verified.

## If this is such a good idea why hasn't it happened yet?

Mostly because this idea exists in an "incentive no man's land".

Academics aren't incentivized to create something like this, because doing so is just "applied" research which tends not to be as prestigious. You don't get to write many groundbreaking papers by taking a bunch of existing ideas and putting them together nicely.

Software engineers aren't incentivized to create something like this, because a programming language is a pure public good and there aren't any truly viable business models that can support it while still remaining open. Even amazing public good ideas like the [interplanetary filesystem](https://en.wikipedia.org/wiki/InterPlanetary_File_System) could be productized by applying the protocol to markets of networked computers, but a programming language can't really pull off that kind of maneuver.

Although the software startup ecosystem does routinely build pure public goods such as databases and web frameworks, those projects tend to have an obvious and relatively short path to being useful in revenue-generating SaaS companies. The problems they solve are clear and visible enough that well-funded engineers can both recognize them and justify the time to fix them. In contrast the path to usefulness for a project like Magmide is absolutely not short, and despite promising immense benefits to both our industry and society as a whole, most engineers capable of building it can't clearly see those benefits behind the impenetrable fog of research debt.

<!-- The problem of not properly funding pure public goods is much bigger than just this project. We do a bad job of this in every industry and so our society has to tolerate a lot of missed opportunity and negative externalities. The costs of broken software are more often borne by society than the companies at fault since insurance and limited-liability structures and PR shenanigans and expensive lawyers can all help a company wriggle out of fully internalizing the cost of their mistakes. Profit-motivated actors are extremely short-sighted and don't have to care if they leave society better off, they just have to get marketshare. -->

We only got Rust because Mozilla has been investing in dedicated research for a long time, and it still doesn't seem to have really paid off for them in the way you might hope.

## Can engineers understand these complex academic ideas enough to use them?

**Yes.** My claim is that the core ideas of formal verification (dependent types, proof objects, higher order logic, separation logic) aren't actually that complicated, and if properly explained basically any working engineer can understand them. I've been working on better explanations in the (extremely rough and early) [`posts/intro-verification-logic-in-magmide.md`](./posts/intro-verification-logic-in-magmide.md) and [`posts/coq-for-engineers.md`](./posts/coq-for-engineers.md).

There are probably many reasons formal verification hasn't caught on in the mainstream (before powerful separation logics like Iris it might have been legitimately too difficult to be worth it!). But it certainly seems to me that [research debt](https://distill.pub/2017/research-debt/) has slowed things down immensely.

## Will working engineers actually use it?

Maybe! We can't force people or guarantee it will be successful, but we can learn a lot from how Rust has been able to successfully teach quite complex type-theoretical ideas to an huge and excited audience. I think Rust has succeeded by:

- *Making big promises* in terms of how performant/robust/safe the final code can be.
- *Delivering* on those promises by building something awesome. I hope that since the entire project will have verification in mind from the start it will be easier to ship something excellent and robust with less churn than usual.
- *Respecting people's time* by making the teaching materials clear and distilled and the tooling simple and ergonomic.

All of those things are easier said than done! Fully achieving those goals will require work from a huge community of contributors.

## Is this language trying to replace Rust?

No! My perfect outcome of this project would be for it to sit *underneath* Rust, acting as a new verified toolchain that Rust could "drop into". The concepts and api of Rust are awesome and widely loved, so Magmide would just try to give it a more solid foundation. Wouldn't it be cool to be able to *prove* that your use of `unsafe` wasn't actually unsafe??

## Why can't you just teach people how to use existing proof languages like Coq?

The short answer is that languages like Coq weren't designed with the intent of making formal verification mainstream, so they're all pretty mismatched to the task. If you want a deep answer to this question both for Coq and several other projects, check out [`posts/comparisons-with-other-projects.md`](./posts/comparisons-with-other-projects.md).

This question is a lot like asking the Rust project creators "why not just write better tooling and teaching materials for C"? Because instead of making something *awesome* we'd have to drag around a bunch of frustrating design decisions. Sometimes it's worth it to start fresh.

## Why will the metaprogramming be more usable than Coq's Notation system?

Coq's [Notation system](https://coq.inria.fr/refman/user-extensions/syntax-extensions.html) is extremely complex. It essentially allows creating arbitrary custom parsers within Coq. While this may seem like a good thing, it's a bad thing. Reasoning about these custom parsing and scoping rules is extremely difficult, and easy to get wrong. It adds a huge amount of work to maintain the system in Coq, and learn the rules for users.

It also makes it extremely easy to create custom symbolic notation that makes code much more difficult to learn and understand. Allowing custom symbolic notation is a bad design choice, since it blurs the line between the primitive notations defined by the language (which are reasonable to expect as prerequisite knowledge for all users) and custom notations. Although Coq makes it possible to query for notation definitions, this is again just more maintenance burden and complexity that still adds significant reading friction.

Magmide's metaprogramming system won't allow unsignified custom symbolic notation, and will require all metaprogrammatic concepts to be syntactically scoped within known identifiers. In Rust macros are always explicit with an annotation or a `macro_name!` syntax, and something similar will be true in Magmide. More information can be found [in the rough `posts/design-of-magmide.md` page](./posts/design-of-magmide.md).

## How would trackable effects compare with algebraic effects?

There's a ton of overlap between the algebraic effects used in a language like [Koka](https://koka-lang.github.io/koka/doc/index.html) and the trackable effects planned for Magmide. Trackable effects are actually general enough to *implement* algebraic effects, so there are some subtle differences.

On the surface level the actual theoretical structure is different. Algebraic effects are "created" by certain operations and then "wrap" the results of functions. Trackable effects are defined by *starting* with some token representing a "clean slate", and then pieces of that token are given up to perform possibly effectful operations, and only given back if a proof that the operation is in fact "safe" is given.

This design means that trackable effects can be used for *any* kind of program aspect, from signaling conditions that can't be "caught" or "intercepted" (such as leaking memory), to notifying callers of the presence of some polymorphic control flow entrypoint that can be "hijacked".

It's important to also note that the polymorphic control flow use cases of algebraic effects could be achieved with many different patterns that no one would strictly call "algebraic effects". For example a type system could simply treat all the implicitly "captured" global symbols as the default arguments of an implicit call signature of a function, allowing those captured global signals to be swapped out by callers (if a function uses a `print` function, you could detect that capture and supply a new `print` function without the function author needing to explicitly support that ability). Or you could simply use metaprogramming to ingest foreign code and replace existing structures. For this reason trackable effects would be more focused on effects related to correctness and safety rather than control flow, despite the relationships between the two.

## Do you really think all engineers are going to write proofs for all their code?

No! And honestly, doing so would probably be a huge waste of time. Not all software has the same constraints, and it would be dumb to to verify a recipe app as rigorously as a cryptography function.

But even a recipe app would benefit from the *foundations* it sits on being much more verified. I imagine something like a "verification pyramid", with excruciatingly verified software at the bottom, going up through less verified code all the way to throwaway scripts that aren't even tested. At the bottom even the tiniest details such as the possibility of integer overflow must be explicitly accounted for, and at the top we just do a basic and highly inferred type-check. Basically, the less important a piece of software is and the easier it is to change, the less verified it needs to be.

And of course because of metaprogramming focused on upward recombination, every layer can rely on the safety of abstractions underneath to not worry about certain kinds of error conditions and only verify what they feel they need to. The language *itself* doesn't have to achieve mainstream success to massively improve the quality of all downstream software, but merely some sub-language. Many engineers have never heard of LLVM, but they still implicitly rely on it every day. Magmide would seek to do the same.

We don't have to take full formal verification fully mainstream, we just have to make it available for the handful of people willing to do the work. If a full theorem prover is sitting right below the high-level language you're currently working in, you don't have to bother with it most of the time, but you still have the option to do so when it makes sense.

## Won't writing verified software be way more expensive? Do you actually think this is worth it?

**Emphatically yes it is worth it.** As alluded to earlier, broken software is a massive drain on our society. Even if it were much more expensive to write verified software, it would still be worth it. Rust has already taught us that it's almost always worth it to [have the hangover first](https://www.youtube.com/watch?v=ylOpCXI2EMM&t=565s&ab_channel=Rust) rather than wastefully churn on a problem after you thought you could move on.

Verification is obviously very difficult. Although I have some modest theories about ways to speed up/improve automatic theorem proving, and how to teach verification concepts in a more intuitive way that can thereby involve a larger body of engineers, we still can't avoid the fact that refining our abstractions and proving theorems is hard and will remain so.

But we don't have to make verification completely easy and approachable to still get massive improvements. We only have to make proof labor more *available* and *reusable*. Since Magmide will be inherently metaprogrammable and integrate programming and proving, developments in one project can quickly disseminate through the entire language community. Research would be much less likely to remain trapped in the ivory tower, and could be usefully deployed in real software much more quickly.

And of course, a big goal of the project is to make verification less expensive! Tooling, better education, better algorithms and abstractions can all decrease verification burden. If the project ever reaches maturity these kinds of improvements will likely be most of the continued effort for a long time.

Besides, many projects already write [absolutely gobs of unit tests](https://softwareengineering.stackexchange.com/questions/156883/what-is-a-normal-functional-lines-of-code-to-test-lines-of-code-ratio), and a proof is literally *infinitely* better than a unit test. At this point I'm actually hopeful that proofs will *decrease* the cost of writing software. We'll see.

## Do you think this language will make all software perfectly secure?

No! Although it's certainly [very exciting to see how truly secure verified software can be](https://www.quantamagazine.org/formal-verification-creates-hacker-proof-code-20160920/), there will always be a long tail of hacking risk. Not all code will be written in securable languages, not all engineers will have the diligence or the oversight to write secure code, people can make bad assumptions, and brilliant hackers might invent entirely new *types* of attack vectors that aren't considered by our safety specifications (although inventing new attack vectors is obviously way more difficult than just doing some web searches and running scripts, which is all a hacker has to do today).

However *any* verified software is better than *none*, and right now it's basically impossible for a security-conscious team to even attempt to prove their code secure. Hopefully the "verification pyramid" referred to earlier will enable almost all software to quickly reuse secure foundations provided by someone else.

And of course, social engineering and hardware tampering are never going away, no matter how perfect our software is.

## Is logically verifying code even useful if that code relies on possibly faulty software/hardware?

This is nuanced, but the answer is still yes!

First let's get something out of the way: software is *literally nothing more* than a mathematical/logical machine. It is one of the very few things in the world that can actually be perfect. Of course this perfection is in regard to an axiomatic model of a real machine rather than the true machine itself, but isn't it better to have an implementation that's provably correct according to a model rather than what we have now, an implementation that's obviously flawed according to that same model? Formal verification is really just the next level of type checking, and type checking is still incredibly useful despite also only relating to a model.

If you don't think a logical model can be accurate enough to model a real machine in sufficient detail, please check out these papers discussing [separation logic](http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/Marktoberdorf11LectureNotes.pdf), extremely high fidelity formalizations of the [x86](http://nickbenton.name/hlsl.pdf) and [arm](https://www.cl.cam.ac.uk/~mom22/arm-hoare-logic.pdf) instruction sets, and the [Iris concurrent higher order separation logic](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf). Academics have been busy doing amazing stuff, even if they haven't been sharing it very well.

If you think we'll constantly be tripping over problems in incorrectly implemented operating systems or web browsers, well you're missing the whole point of this project. These systems provide environments for other software yes, but they're still just software themselves. Even if they aren't perfectly reliable *now*, the entire ambition of this project is to *make* them reliable.

Hardware axioms, which model the abstractions provided by a concrete computer architecture are trickier though. Hardware faults and ambient problems of all kinds can absolutely cause unavoidable data corruption. Hardware is intentionally designed with layers of error correction and redundancy to avoid propagating corruption, but it still gets through sometimes. There's one big reason to press on with formal verification nonetheless: the possibility of corruption or failure can be included in our axioms!

Firmware and operating systems already include state consistency assertions and [error correction codes](https://en.wikipedia.org/wiki/Error_detection_and_correction), and it would be nice if those checks themselves could be verified. The entire idea of "trackable effects" is intended to allow environmental assumptions to be as high fidelity and stringent as possible without requiring every piece of software to actually care about all that detail. This means the lowest levels of our "verification pyramid" can fully include the possibility of corruption and carefully prove it can only cause a certain amount of damage in a few well-understood places. Then the higher levels of the pyramid can build on top of that much sturdier foundation.

Yes it's true that we can only go so far with formal verification, so we should always remain humble and remember that real machines in the real world fail for lots of reasons we can't control. But we can go much much farther with formal verification than we can with testing alone! Proving correctness against a mere model with possible caveats is incalculably more robust than doing the same thing we've been doing for decades.

## How far are you? What remains to be done?

Very early, and basically everything remains to be done! I've been playing with models of very simple assembly languages to get my arms around formalization of truly imperative execution. Especially interesting has been what it looks like to prove some specific assembly language program will always terminate, and to ergonomically discover paths in the control flow graph which require extra proof justification. I have some raw notes and thoughts about this in [`posts/toward-termination-vcgen.md`](./posts/toward-termination-vcgen.md). Basically I've been playing with the design for the foundational computational theory.

In [`posts/design-of-magmide.md`](./posts/design-of-magmide.md) I have some rough thoughts about what the project's major milestones would be. The obvious first milestone is to create a bootstrapping compiler capable of compiling the first self-hosted version.

Read [this blog post discussing my journey to this project](https://blainehansen.me/post/my-path-to-magmide/) if you're interested in a more personal view.

## Why will this project succeed where others haven't?

I can't be sure it will! That's why the plan is to keep soliciting help and contributions as I go, and focus diligently on just getting the project bootstrapped enough to be useful and inspire people to get involved. A successful language ecosystem requires a large number of very complex moving parts to all be excellent and interlock seamlessly. I don't think I'm going to pull that off alone, I just want to get the ball rolling.

In the words of Bryan Cantrill:

> "Engineers manage a duality, between arrogance and humility. ... The arrogance is what gets you to do it, and the humility is what gets you through."
> <br>\- Bryan Cantrill in [*Leadership without management: Scaling organizations by scaling engineers*](https://www.youtube.com/watch?v=1KeYzjILqDo&feature=emb_logo&ab_channel=OmniTI).

For now I simply *dare to hope* that a project like this is possible. Maybe it isn't! I'm determined to find out.

## This is an exciting idea! How can I help?

Just reach out! Since things are so early there are many questions to be answered, and I welcome any useful help. Feedback and encouragement are also welcome.

If you would like to get up to speed with formal verification and Coq enough to contribute at this stage, you ought to read [Software Foundations](https://softwarefoundations.cis.upenn.edu/), [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/html/Cpdt.Intro.html), [this introduction to separation logic](http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/Marktoberdorf11LectureNotes.pdf), and sections 1, 2, and 3 of the [Iris from the ground up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf) paper. You might also find my unfinished [introduction to verification and logic in Magmide](./posts/intro-verification-logic-in-magmide.md) useful, even if it's still very rough.

Here's a broad map of all the mad scribblings in this repo:

- `theorems` contains exploratory Coq code, much of which is unfinished. This is where I've been playing with designs for the foundational computational theory.
- `posts` has a lot of speculative writing, mostly to help me nail down the goals and design of the project.
- `notes` has papers on relevant topics and notes I've made purely for my own learning.
- `notes.md` is a scratchpad for raw ideas, usually ripped right from my brain with very little editing.
- `README.future.md` is speculative writing about a "by example" introduction to the language. I've been toying with different syntax ideas there, and have unsurprisingly found those decisions to be the most difficult and annoying :cry:

Thank you! Hope to see you around!

---

# What could we build with Magmide?

A proof checker with builtin support for metaprogramming and verification of assembly languages would allow us to build any logically representable software system imaginable. Here are some rough ideas I think are uniquely empowered by the blend of capabilities that would be afforded by Magmide. Not all of these ideas are *only* possible with full verification, but I feel they would get much more tractable.

## Truly eternal software

This is a general quality, one that could apply to any piece of software. With machine checked proofs, it's possible to write software *that never has to be rewritten or maintained*. Of course in practice we often want to add features or improve the interface or performance of a piece of software, and those kind of expected improvements can't be anticipated enough to prove them ahead of time.

But if the intended function of a piece of software is completely understood and won't significantly evolve, it's possible to get it right *once and for all*. Places where this would be a good idea are places where it's hard to get to the software, such as in many embedded systems like firmware, IOT applications, software in spacecraft, etc.

## Safe foreign code execution without sandboxing

If it's possible to prove a piece of code is well-behaved in arbitrary ways then it's possible to simply run foreign and untrusted code without any kind of sandboxing or resource limitations, as long as that foreign code provides a consistent proof object demonstrating it won't cause trouble.

What kind of performance improvements and increased flexibility could we gain if layers like operating systems, hypervisors, or even internet browsers only had to type check foreign code to know it was safe to execute with arbitrary system access? Of course we still might deem this too large a risk, but it's interesting to imagine.

## Verified critical systems

Many software applications are critical for safety of people and property. It would be nice if applications in aeronautics, medicine, industrial automation, cars, banking and finance, blockchains, and all the others were fully verified.

## Secure voting protocols

It isn't good enough for voting machines to be provably secure, the voting system itself must be cryptographically transparent and auditable. The [ideal requirements](https://en.wikipedia.org/wiki/End-to-end_auditable_voting_systems) are extremely complex, and would be very difficult to get right without machine checked proofs.

Voting is sufficiently high stakes that it's extremely important for a voting infrastructure to not simply be correct, but be *undeniably* correct. I imagine it will be much easier to assert the fairness and legitimacy of voting results if all the underlying code is much more than merely audited and tested.

## Universally applicable type systems

Things like the [Underlay](https://research.protocol.ai/talks/the-underlay-a-distributed-public-knowledge-graph/) or the [Intercranial Abstraction System](https://research.protocol.ai/talks/the-inter-cranial-abstraction-system-icas/) get much more exciting in a world with a standardized proof checker syntax to describe binary type formats. If a piece of data can be annotated with its precise logical format, including things like endianness and layout semantics, then many more pieces of software can automatically interoperate.

I'm particularly excited by the possibility of improving the universality of self-describing apis, ones that allow consumers to merely point at some endpoint and metaprogrammatically understand the protocol and type interface.

## Truly universal interoperability

All computer programs in our world operate on bits, and those bits are commonly interepreted as the same few types of values (numbers, strings, booleans, lists, structures of those things, standardized media types). In a world where all common computation environments are formalized and programs can be verified to correctly model common logical types in any of those common computation environments, then correct interoperation between those environments can also be verified!

It would be very exciting to know with deep rigorous certainty that a program can be compiled for a broad host of architectures and model the same logical behavior on all of them.

## Semver enforcing and truly secure package management

Since so much more knowledge of a package's api can be had with proof checking and trackable effects, we can have distributed package management systems that can enforce semver protocols at a much greater granularity and ensure unwanted program effects don't accidentally (or maliciously!) sneak into our dependency graphs.

## Invariant protection without data hiding

In many languages some idea of encapsulation or data hiding is supported by the language, to allow component authors to ensure outside components don't reach into data structures and break invariants. With proof checking available, it's possible to simply encode invariants directly alongside data, effectively making arbitrary invariants a part of the type system. When this is true data no longer has to be hidden at the type system level. We can still choose to make some data hidden from documentation, but doing so would simply be for clarity rather than necessity.

Removing the need for data hiding allows us to reconsider almost all common software architectures, since most are simply trying to enforce consistency with extra separation. Correct composition can be easy and flexible, so we can architect systems for greatest performance or clarity and remove unnecessary walls. For example strict microservice architectures might lose much of their usefulness.

## Flattened async executor micro-kernel operating system

The process model is a very good abstraction, but the main reason it's useful is because it creates hard boundaries around different programs to prevent them from corrupting each other's state. Related to the above point, what if we don't have to do that anymore? What if code from different sources could simply inhabit the same memory space without much intervention?

The Rust community has made some very innovative strides with their asynchronous executor implementations, and I am one person who believes the "async task" paradigm is an extremely natural way to think about system concurrency and separation. What if an async task executor could simply be the entire operating system, doing nothing but managing task scheduling and type checking new code to ensure it will be well-behaved? In this paradigm, the abstractions offered by the operating system can be moved into a *library* instead of being offered at runtime, and can use arbitrary capability types to enforce permissions or other requirements. Might such a system be both much more performant and simpler to reason about?

## Metaprogrammable multi-persistence database

Most databases are designed to run as an isolated service to ensure the persistence layer is always in a consistent state that can't accidentally be violated by user code. With proof invariants this isn't necessary, and databases can be implemented as mere libraries.

Immutable update logs have proven their value, and with proof checking it would be much easier to correctly build "mutable seeming" materialized views based on update commands. Databases could more easily save multiple materialized views at different scales in different formats.

## More advanced memory ownership models

Rust has inspired many engineers with the beautiful and powerful ideas of ownership and reference lifetimes, rooting out many tricky problems before they arise.

However the model is too simple for many obviously correct scenarios, such as mutation of a value from multiple places within the same thread, or pointers in complex data structures that still only point to ownership ancestors or strict siblings such as is the case in doubly-linked lists. More advanced invariants and arbitrary proofs can solve this problem.

## Reactivity systems that are provably free from leaks, deadlocks, and cycles

Reactive programming models have become ubiquitous in most user interface ecosystems, but in order to make sense they often rely on the tacit assumption that user code doesn't introduce resource leaks or deadlocks or infinite cycles between reactive tasks. Verification can step in here, and produce algorithms that enforce tree-like structures for arbitrary code.
