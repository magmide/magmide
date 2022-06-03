# Comparisons with other projects

An important question to ask of any project is: "How is the project different than X?" or more probingly: "Why build this new project instead of just using X? Why can't X address your needs?" This page attempts to thorougly answer that question.

Many comparisons with other projects aren't actually that interesting, since the projects don't even have the same goals, or the comparison project isn't "maxed out" in one of Magmide's design pillars [(logical/computational/expressive power)](./posts/design-of-magmide.md).

Many of these projects are essentially attempts to allow users to verify code in a fully automated way. Although full automation is nice, I ultimately don't think it's productive to hide the underlying logical ideas from users, instead of just putting in the work to explain them properly. If a tool allows manual proofs alongside metaprogramming capabilities then it can still have full automation in many domains, whereas if a tool can only prove a certain subset of claims automatically then it's forever limited to that subset.

- Rust/LLVM: Not maxed out in logical power, can't prove correctness.
- [Liquid Haskell](https://liquid.kosmikus.org/01-intro.html): Not maxed out in logical power since it only has refinement types and not a full type theory. Not maxed out in computational power since Haskell doesn't easily allow bare metal operations.
- [Ivy](http://microsoft.github.io/ivy/language.html): Only a first order logic, so not maxed out in logical power. However the idea of separating pure functions and imperative procedures was part of the inspiration for the Logic/Host Magmide separation.
- [TLA+](https://en.wikipedia.org/wiki/TLA%2B): Not based on dependent type theory, so not maxed out in logical power. Not maxed out in computational power, since the language itself is only intended for specification writing rather than combined code/proofs.
- Isabelle/HOL, ACL2, PVS, Twelf: Not maxed out in logical power, [missing either dependent types, higher order logic, or general `Prop` types](http://adam.chlipala.net/cpdt/html/Cpdt.Intro.html).
- [Dafny](https://dafny-lang.github.io/dafny/): Not maxed out in computational power, since it only exposes a fairly high level imperative language. It seems like they've tried too hard to create an "easy mode" tool.
- [Rodin tool/B-method](https://en.wikipedia.org/wiki/Rodin_tool): Only seems to be first order, so not maxed out in logical power. Also doesn't seem to use a bare metal language and separation logic to reason about real programs, which isn't surprising since separation logic was only recognizably invented in around 2002.
- [Rudra](https://github.com/sslab-gatech/Rudra): Intended to only uncover common undefined behaviors, rather than to prove arbitrary properties.
- [Prusti](https://github.com/viperproject/prusti-dev): Intended to only automatically check for absence of panics or overflows, or pre/post conditions rather than arbitrary properties.
- [RustHorn](https://github.com/hopv/rust-horn): Intended to only automatically check pre/post conditions rather than arbitrary properties.
- [KLEE](https://llvm.org/pubs/2008-12-OSDI-KLEE.html) and related tools: Intended to only generate reasonably high coverage tests rather than prove arbitrary properties.
- [Property-based testing tools](https://www.lpalmieri.com/posts/an-introduction-to-property-based-testing-in-rust/): Intended to only test a random subset of values rather than all possible values.

---

Then there are many academic projects which verify software at the same deep level as Magmide intends to, but don't have the intent to create a tool that can act as both the logical and computational foundation for all software. These research projects will be very useful to learn from, but again their goals aren't as directly focused on broad engineering practice as Magmide.

- [Lambda Rust/RustBelt](https://www.ralfj.de/research/phd/thesis-screen.pdf): A formalization of a realistic subset of Rust, proofs of its soundness, and proofs of the soundness of many core Rust libraries that use `unsafe`. This project is what spurred the development of the Iris separation logic that will be extensively used in Magmide. RustBelt is obviously the direct ancestor of the Magmide project, and laid the formal foundations for it to be possible. However it only intended to verify Rust code "on the side", rather than creating a tool capable of *implementing* a verified version of Rust. I hope to deeply collaborate with the RustBelt authors!
- [Vellvm](https://github.com/vellvm/vellvm): A formalization of LLVM in Coq. Doesn't intend to use this formalization to create a self-hosting/verifying proof assitant. Importantly, doesn't use a higher order separation logic such as Iris, so it likely can't be used directly in Magmide. However the project itself and its creators will be invaluable sources of knowledge.
- [Vale](https://www.microsoft.com/en-us/research/wp-content/uploads/2017/08/Vale.pdf): A Dafny tool capable of verifying the correctness of annotated assembly language cryptographic routines. This project is extremely cool and similar to Magmide in the sense that it is capable of verifying arbitrary conditions of bare metal code. However, it is very narrowly focused on cryptographic applications, and has no intention of implementing a general purpose language. However the success of the project (and inspired work such as [this more efficient F* verification condition generator](https://www.andrew.cmu.edu/user/bparno/papers/vale-popl.pdf)) shows that something like Magmide is possible.
- [Bedrock](http://adam.chlipala.net/papers/BedrockICFP13/BedrockICFP13.pdf): A project that honestly feels very similar to Magmide! Bedrock is especially concerned with metaprogramming and verification of low-level code. However the project has been closed and the research group has been working on a [much smaller successor project `bedrock2`](https://github.com/mit-plv/bedrock2), along with [many other more academic projects](https://github.com/mit-plv/). It's very unclear to me what relationship these projects have with the private and proprietary [Bedrock Systems](https://bedrocksystems.com), other than both being directly related to [Adam Chlipala](http://adam.chlipala.net). I strongly believe it's absolutely essential these verification systems are open source, not only controlled by corporations and governments, and are shared as broadly as possible, so even if Bedrock Systems was filling the exact same need as Magmide there would be a need for an open source version. All the same, the original bedrock is yet another project that is promising for Magmide, since it shows that verified *macros* are possible and tractable. My (wildly conjecturing) guess about why the original project was discontinued is because Iris came about, which seems reasonable since just in 2020 the research group [had a guest post about Iris on their blog](https://plv.csail.mit.edu/blog/iris-intro.html#iris-intro). It probably didn't make sense to pursue their previous direction if they could learn/use Iris instead.
- [DeepSpec](https://deepspec.org/main): A project verifying a whole family of extant systems end-to-end, which happens to include Vellvm. This again is very similar to the Magmide project, but isn't at all focused on creating tools suitable for mainstream engineers, or building a *new* foundational language. Although I think this research is extremely valuable, I don't think it's going to create a lot of industry excitement for verification.
- [Metamath Zero](https://github.com/digama0/mm0): A project intended to create a minimal and extremely efficient language for specifications and proofs. This project is very focused on simplicity of the proof language and the speed of the verifier, which aren't particular goals of the Magmide project. Magmide is more concerned with creating a foundational tool intended for mainstream use, so simplicity/speed of the verifier is desired but not essential. Instead of relying on a simple verifier implementation, Magmide is relying on Coq to bootstrap initial correctness, and speed of verification isn't a goal until after the project is bootstrapped [("make it work, make it right, make it fast")](https://wiki.c2.com/?MakeItWorkMakeItRightMakeItFast). However I'm excited to learn lessons from mm0 both during and after Magmide's bootstrapping!
- [ATS](http://www.ats-lang.org/): ATS is an extremely advanced and interesting language, which seems to already be capable of building very robust and performant code. It has lots of conceptual overlap with Magmide, such as integrating linear types reminiscent of separation-logic, compiling to a bare metal language (C), and providing special syntax for refinement types. However there are a few important differences:
  - the design is extremely obtuse and the learning materials very academic (frankly I found it difficult even to navigate the docs enough to evaluate the merits of the design)
  - the language seems to require all correctness assertions be somehow integrated into the type signatures of functions, whereas in Magmide the intent is to both allow assertions in types (using asserted types such as `Int & != 0`) as well as assertions in separate theorems, which should allow users to add more and more assertions without hopelessly cluttering the actual implementation
  - the "proof threading" concept where proof objects are explicitly passed and returned is very painful, and Magmide intends to instead make all proofs either attached to data values through asserted types, or simply inferred based on which data values are passed (without requiring extra syntax to signal inference), or deferred to the proof section after the end of the function
  - the linear type system isn't as powerful as Iris, which means all the special use cases Iris specifically worked to support are likely not supported

  However my largest criticism of the project is its continued insistence on the pure functional paradigm. As I discuss at the end of this page, we shouldn't be trying to force the pure functional paradigm on our inherently imperative computational environments, but instead finding ways to ergonomically encode imperative concepts in the world of pure logic.

  Ultimately ATS is very interesting, and I hope the creators can share their insights and ideas with Magmide as it matures.

---

Now to the really interesting comparisons, those with other higher order dependently typed proof assistants. I'll focus on Coq, Lean, and F*.

Before I go on, I just want to make sure something's crystal clear:

**These three projects are amazing, and have obviously involved a terrifying amount of work from a large number of shockingly intelligent and hardworking people.** I'm very confident I could never have come up with the core ideas behind any of them, or implemented anything like them if I wasn't slavishly copying from them. **Nothing I say below is meant to disparage the projects!** I'm not an academic, but I've done just barely enough work to understand this academic field to apply my self-taught non-academic viewpoint. And from my viewpoint I can see the possibilility of a truly beautiful and unified language that finally gets formal verification into the mainstream. Please tell me if I'm crazy or am missing something really obvious! I'm just saying what I see.

With that out of the way....

Those three projects could all be used to *logically define* Magmide, and since they all *technically* have the capability to produce running code, they could rival the intended use cases of Magmide. However none of them quite fit.

All three of them certainly feel very academic, and I'm not even sure exactly how hard the projects are *trying* to be approachable and achieve general adoption. I've already talked a lot about how academics do a pretty bad job explaining their work, often assuming shared knowledge rather than pointing readers toward prerequisites, using formal definitions and jargon instead of intuitive examples and metaphors, and not prioritizing ergonomic tools. But the *real* reason I think these languages haven't achieved general adoption is more nuanced:

*I strongly believe all three of them are overly dogmatic about pure functional programming.* They mistakenly assume the functional programming language at their heart will *itself* be the thing people use to build software.

Functional programming may have its devotees, but there's a reason it's much less adopted than imperative methods: *real computers aren't pure or functional!* In a real computer, *every* action is impure and effectful, since even the most basic operations like updating registers or memory are intrinsically mutations of global state. The main idea of functional programming is a falsehood, one that makes some problems easier to reason about, but at the cost of ignoring the real nature of the problem. That extreme level of abstraction isn't always intuitive or helpful, and most engineers trying to build high performance systems that take advantage of the real machine will never be willing to make that sacrifice.

The Magmide design in contrast *splits up* Logic and Host Magmide into separate "dual" languages, each used in exactly the way it's most natural. Logic Magmide is the imaginary level where pure functions and mathematical algorithms and idealized models exist, which is the perfect realization of the goals of functional programming. Then those logical structures only exist at compile time to help reason about the messy and truly computational behavior of Host Magmide. Separation logic is what makes it possible to make robust safety and correctness assertions about imperative code, rather than simply outlawing mutation and side effects as is done in functional languages. And with a deeply powerful separation logic like Iris we can build things like trackable effects that are more practical, flexible, and ergonomic than other effect systems.

This again brings to mind the possible comparison between Rust and C: "Why build Rust? Can't you do everything in C you could do in Rust?" Well, yes you could! But... do you really want to? It isn't *only* about whether something's possible, it's about whether it's natural and clear and ergonomic. Why mix together the pure logical code and the real computational code when doing so doesn't make things easier and isn't really true? We don't want abstraction mismatches in our foundational language!

So in other words...

![stop trying to make functional programming happen, it's not going to happen](https://blainehansen.me/stop-trying-to-make-fp-happen.jpg)

... or at least, just use pure functional languages in contexts where their purity is actually correct.

I obviously don't think functional languages should never be used to write programs. But we have to acknowledge the limitations of functional programming. With verified imperative foundations underneath us, it will be much easier to discover and implement whatever paradigms we find truly useful in whatever contexts they're useful, such as optimizations like ["functional but in-place"](https://www.microsoft.com/en-us/research/uploads/prod/2020/11/perceus-tr-v1.pdf).

Let's dive into each of those three projects in detail:

## Coq

Coq has made a lot of frustrating design decisions.

- Metaprogramming is [technically possible in Coq](https://github.com/MetaCoq/metacoq), but it was grafted on many years into the project, and it feels like it.
- The language is extremely cluttered and obviously ["designed by accretion"](https://stackoverflow.com/questions/56517779/what-is-the-difference-between-lemma-and-theorem-in-coq).
- All the documentation and introductory books were clearly written by academics who have no interest in helping people with deadlines build something concrete. Compare the [Coq standard library file for `Equivalence`](https://coq.inria.fr/library/Coq.Classes.Equivalence.html) with the somewhat related [`Eq` trait in Rust](https://doc.rust-lang.org/std/cmp/trait.Eq.html).
- The [Notation system](https://coq.inria.fr/refman/user-extensions/syntax-extensions.html) just begs for unclear and profoundly confusing custom syntax, and is itself extremely overengineered.
- Using the tool [can be quite punishing](https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html#lab50).
- It's a pure functional language with a garbage collector, so it will never perform as well as a self-hosted bare metal compiler.
- And let's be honest, the name "Coq" is just terrible.

Another really important problem is that Coq can only produce runnable programs with the [extraction mechanism](https://softwarefoundations.cis.upenn.edu/lf-current/Extraction.html), which gives no guarantees about the extracted code doing the same thing as the original. Extraction [isn't itself verified](https://github.com/MetaCoq/metacoq/issues/163), so arbitrary bugs are possible during the process, and even if it were verified it would rely on the target language environment being correct. Although fully verified Magmide toolchains are very far away, the design is tailored specifically to that goal.

Coq has existed *since 1989* and is still a very niche tool mostly only used by academics or former academics. Rust by comparison doesn't offer anywhere close to the correctness-proving power, has only been a mature language since 2015, but has achieved truly impressive adoption. The most damning accusation I can make against Coq is that it isn't even that broadly adopted *in academia*. Why aren't almost all papers in mathematics, logic, philosophy, economics, and computer science not verified in Coq? And yet approachable tools like python and julia and matlab are much more common?

Coq is still powerful enough to be very useful though, which is why I've chosen it as Magmide's bootstrapping language. I'm working on [`posts/coq-for-engineers.md`](./posts/coq-for-engineers.md) to help get passionate contributors up the learning curve enough to be helpful, because I know I can't build this all myself, and I'm not sure how interested academics will be to help me :fearful:

<!-- using myself as an example, I'm an extremely determined and curious person who has been hell-bent on understanding both it and the theory behind it, but since I'm not being led through it in an academic context where all the implicit knowledge is exposed through in-person mentors, it has been extremely challenging -->

And of course I don't think it would be wise to just throw away all the awesome work done by the Coq project. At some point we could create a parser/converter to allow old Coq code to be read and used by Magmide.

## Lean

Lean is very similar to Coq, and it seems its entire purpose is to be a more cleanly designed successor! However I'm somewhat frustrated that despite having an overall cleaner design, it isn't that substantially different. For example it still has a very ["baked in" custom notation metaprogramming system](https://leanprover.github.io/lean4/doc/syntax.html) rather than something more flexible.

It also makes the mistake of overemphasizing pure functional programming, and muddies the theorem proving language with a bunch of effectfulness concepts and builtin computational types. It also uses the interpreted pure functional language itself as the metaprogramming language, which will hamper performance.

Overall it seems the project is more interested in the needs of academic mathematicians, or at least that seems to be the group who's actually been adopting it. I am excited to see what new things they come up with though!

## F*

F* is the project that's most frustratingly close to being capable of Magmide's goal, since it explictly supports extraction to various targets and is already being used in production-grade verification projects. But again, I don't think it's going to achieve general adoption, not just because of its academic tone, but because it also muddies the pure logical language with effectful computation concepts.

Effectfulness is inherently an imperative computational concept. It seems very counterproductive to me to add primitive effects to a logical lambda calculus, since the whole point of a logical language is that it can be used to model any kind of effects for any kind of system. The logical language should be absolutely pure, because its job is just to do pure logic rather than computation.

Most real functions will have *many* effects, and their authors only care in a small handful of circumstances, when those effects are unexpected/undesired. It's better to use automated checks/proofs to assert a function is *free from* certain effects rather than having to explicitly list effects.

[SteelCore](https://www.fstar-lang.org/papers/steelcore/steelcore.pdf), the variant of separation logic used in various F* projects, also doesn't support the kind of recursive/impredicative ghost state and complex resource algebras that Iris does, or at least only supports them if they evolve monotonically.

<!-- I'm also somewhat frustrated at how verbose the [Low*](https://fstarlang.github.io/lowstar/html/Introduction.html) is. If you're writing code that's supposed to model C, then it's obvious that we're using the C memory model and following the C calling convention. Needing to explicitly point that fact out with an effect type isn't productive. -->

<!-- I'm also confused F* seems to be avoiding deep embeddings. Deep embeddings give us a huge amount of flexibility, since! Why build a proof assistant capable of targeting *some* environments, when a proof assistant has the power to target *all* environments?? -->

And unforunately, F* is also a frustrating name. It isn't unavoidably clear to everyone how to say it (asterisk? splat? bullet?) and searching for the name online is an annoying dance of trying combinations like `f-star`, `f star`, or `"f*"`.

This is all very frustrating, because F* is *so close!* It's right on top of the right feature set, but the fact that it *hasn't* caught the attention of the engineering mainstream is likely the only evidence you need that it *won't*. Maybe it's just not done! Maybe it could flesh out and distill its documentation and add a few conveniences, but I just don't think that's going to be enough.

The F* community seems very interested in solving the tricky balance between automation and manual proofs though, and they've done a lot of cool work relating to specification inference and automated verification condition generation, so I'll be watching them very closely to see what other handy ideas they come up with!

---

So there you go. Maybe my problems with Coq and Lean and F* all seem like minor gripes to you. Maybe you're right! But again, the intention of this project is to build a proof language *for engineers*. Academics have so many little cultural quirks and invisible assumptions, and I rarely come across an academic project that doesn't *feel* like one. Magmide asks the question "what if we designed a proof language from scratch to take formal verification mainstream?" No other project has done that.
