<!-- # Comparisons with other projects

An important question to ask of any project is: "How is the project different than X?" or more probingly: "Why build this new project instead of just using X? Why can't X address your needs?" This page attempts to thorougly answer that question.

Many comparisons with other tools aren't actually that interesting, since the projects don't even have the same goals, or the comparison project isn't "maxed out" in one of Magma's main features [(logical/computational/expressive power)](https://github.com/blainehansen/magma#is-this-design-too-ambitious-is-it-just-everything-and-the-kitchen-sink). Let's get all these out of the way:

- Rust/LLVM: Not maxed out in logical power, can't prove correctness.
- Liquid Haskell: Not maxed out in logical power since we only have refinement types and not a full type theory. Not maxed out in computational power since Haskell doesn't easily allow bare metal operations.
- [Ivy](http://microsoft.github.io/ivy/language.html): Only a first order logic, so not maxed out in logical power.
- TLA+: Not maxed out in logical power, isn't a fully dependent type theory. This means that TLA+ could be implemented *in* Magma.
- Isabelle/HOL, ACL2, PVS, Twelf: Not maxed out in logical power, [missing either dependent types, higher order logic, or general `Prop` types](http://adam.chlipala.net/cpdt/html/Cpdt.Intro.html).
https://github.com/sslab-gatech/Rudra
https://github.com/project-oak/rust-verification-tools
Prusti too.

Then there are systems that merely *apply* formal methods to existing software. These can

My guess about why they weren't able to achieve broad adoption is because they didn't have separation logic, the critical theoretical breakthrough that (eventually) led to Rust's revolutionary ownership model. It's a very clean and intuitive way to reason about mutable and sharable global state. It's extremely difficult to reason about the correctness of imperative programs, especially concurrent ones, without using Separation Logic. And Iris was only recently developed! The reason Magma is exciting *now* is largely because of Iris.

However there might be something to learn from the literate programming patterns in this project. I wish I could get my hands on it!

https://en.wikipedia.org/wiki/B-Method
https://en.wikipedia.org/wiki/Rodin_tool

I don't think mere pre and post annotations on functions is enough. People need the full power, *but they also need to be effectively taught how to use it!*

There are several research projects that are verifying software at the same deep level as Magma intends to, but the projects don't have the same goal of creating a self-hosting/verifying dependently typed language capable of being an approachable foundation for all computing. However the work they're doing is very exciting, and I hope to be able to collaborate and learn from them:

- [Vellvm](TODO): Doesn't use a higher order separation logic, so not maxed out in logical power, at least

https://gitlab.mpi-sws.org/iris/lambda-rust/-/tree/master

- vale
focused on cryptographic code, and it isn't a new proof assistant with the intent to make formal verification go mainstream, but instead a library in an existing proof assistant meant to help crypto researchers
however this project does in a way hint that the magma project is a good idea! it is also generic over different architectures and uses automatic verification condition generators

- bedrock (the first research language)
Proprietary! It's essential systems like this aren't only controlled by corporations and governments.
http://adam.chlipala.net/papers/BedrockICFP13/BedrockICFP13.pdf
https://plv.csail.mit.edu/bedrock/
https://bedrocksystems.com/products/
The original purely research version of bedrock is yet another project that is promising for the magma project, since it shows that verified *macros* are possible and tractable. However it's still stuck in coq and therefore slow and obtuse.

need to look at xcap paper and other references in the bedrock paper

- bedrock (the company)


- [bedrock2](https://github.com/mit-plv/bedrock2)

at first glance it would seem this project is directly trying to do the same thing, but it seems to have dramatically different goals

- no self-hosting
- not creating a full proof checker
- building a language at a relatively high level of abstraction rather than bare metal assembly

however that team will definitely have a ton of useful insights to provide! the work is similar enough there's got to be enough overlap to make working together productive.


- mm0

- DeepSpec:






Now to the really interesting ones, the higher order dependently typed proof assistants Coq, Lean, and F*.

All of these projects could be used to *logically define* Magma, and since they all *technically* have the capability to produce running code, they could rival the intended use cases of Magma. However none of them quite fit, with F* being the most frustratingly close.

How did all of them not achieve the goal? A large reason is that they're all built by academics rather than practicing engineers, so the projects themselves are hidden behind research debt or punishing teaching materials or difficult user experience. But I think there's a more nuanced reason, that the creators of those projects fell victim to a core misunderstanding that kept them from achieving general adoption: they made the mistake of thinking the functional programming language *itself* would be the thing people used to build software.

Functional programming may have its devotees, but there's a reason it's much less adopted than imperative methods: *real computers aren't pure or functional!* The main idea of functional programming is a lie, one that makes some problems easier to reason about, but at the cost of completely hiding the real nature of the actual problem being solved. Engineers trying to build high performance systems that take advantage of the real machine will never be willing to make that sacrifice.

The Magma design in contrast *splits up* Logic and Host Magma into separate "dual" languages, each used in exactly the way it's most natural. Logic Magma is the imaginary level where pure functions and mathematical algorithms and idealized models exist, which is the perfect realization of the goals of functional programming. Then those logical structures only exist at compile time to help reason about the messy and truly computational behavior of Host Magma.

So in other words...

![stop trying to make functional programming happen, it's not going to happen](https://blainehansen.me/stop-trying-to-make-fp-happen.jpg)

... or at least, just use pure functional languages in contexts where their purity is actually correct.

I obviously don't think functional languages should never be used to write programs. But if we don't accept the limitations of functional programming, we're just being dogmatic. Let's instead acknowledge the imperative foundation we must build on, and then imagine the kinds of incredible functional languages we could build with the capability to logically prove the correctness of the implementation and optimizations according to the underlying imperative machine!

This again brings to mind the possible comparison with Rust and C: "Why build Rust? Can't you do everything in C you could do in Rust?" Well, yes you could! But... do you really want to? It isn't *only* about whether something's possible, it's about whether it's natural and clear and ergonomic. We don't want abstraction mismatches in our foundational language!

Let's get into the nitty gritty:

## Coq

because of metacoq and ml extraction, coq *technically* could be used to do everything in this project. however it's important to note that metacoq defines metaprogramming in coq without extraction, which means it will always perform quite poorly. magma by comparison defines its metaprograming in terms of *compute* magma rather than *theory* magma, so it can perform extremely well.
but to be truly honest, the real reason coq isn't good enough is because *it has a truly punishing user experience*. it's not good enough for coq to be *powerful*, it has to be *approachable* to meet the goal of making formal verification common in engineering practice
using myself as an example, I'm an extremely determined and curious person who has been hell-bent on understanding both it and the theory behind it, but since I'm not being led through it in an academic context where all the implicit knowledge is exposed through in-person mentors, it has been extremely challenging
coq has existed *since the 80s* and is still a very niche tool mostly only used by academics or former academics. rust by comparison doesn't offer anywhere close to the correctness-proving power, and has only been a mature language since 2015, but has achieved truly impressive adoption.
the most damning accusation I can make against coq is that it isn't even that broadly adopted *in academia*. why aren't almost all papers in mathematics, logic, philosophy, economics, and computer science not verified in coq? and yet approachable tools like python and julia and matlab are much more common? extreme logical power is useless if it can't be readily accessed

Another really important problem is that Coq can only produce runnable programs with the extraction mechanism, which isn't itself verified and even then relies on the interpreter of the target language being correct and on extracted datatypes (which you can arbitrarily override!) corresponding to the Coq datatypes.

## Lean

I'm frankly not even sure what lean adds over coq. It certainly makes a few better minor design decisions, but it isn't really promising to change the game in any way, at least not sufficiently that it's worth tossing out all the existing work in coq.

Lean seems to have made the same mistake as F*, in building a bunch of "real" computational types in and thinking that engineers would write real programs in Lean.

## F*

I think the way in which they've blended effectful programming and type theory is actually counterproductive. Effectful programming is inherently imperative, and blending the two only seems like it would appeal to people who insist on using functional paradigms. The reason I think Magma should use a pure calculus of constructions is that the proving/modelling layer is intentionally "imaginary". The dependent type system is essentially just a higher order type system for an infinite range of concrete languages, and so only exists at compile time. The blend is confusing and "buries the lede".

In a real computational environment, *all* operations are imperative and effectful. In a purely logical environment, *no* operations are imperative or effectful. Blurring this distinction isn't helpful, but will be confusing and cluttering for everyone.

If you're writing code that's supposed to model C, then it's obvious that we're using the C memory model and following the C calling convention! Needing to explicitly point that fact out with an effect type isn't productive.

F* ultimately suffers from the same problems as Coq. It's obvious it was written by academics rather than practitioners, and the needs and concerns of academics shine through in the design.

Most effect type theories seems more concerned with logical parsimony than raw usefulness. In real software systems engineers only care about effects if they want to prevent bad things from happening or intercept some operations. Most real functions will have *many* effects, and so it's better to use automated checks/proofs to make assertions about the effectfulness of a function rather than writing out every single one explicitly.

And unforunately, F* is also a frustrating name. It isn't clear to everyone how to say it (asterisk? splat? bullet?) and searching for the name online is an annoying dance of trying combinations like `f-star`, `f star`, or `"f*"`.

This is all very frustrating, because F* is *so close!* It's right on top of the right feature set, but the fact that it *hasn't* caught the attention of the engineering mainstream is likely the only evidence you need that it *won't*. Maybe it's just not done! Maybe it could flesh out and distill its documentation and add a few conveniences, but I just don't think that's going to be enough.

The case could certainly be made that Magma should *use* F* to bootstrap Magma. But the Iris project is all in Coq! Iris will likely need to be ported to Magma once it's bootstrapped, so it would be nice to avoid having to also port it to F* before even starting.

Maybe these problems all seem like minor gripes to you. Maybe you're right! But again, the intention of this project is to build a proof language *for engineers*. Academics have so many little cultural quirks and invisible assumptions, and I rarely come across an academic project that doesn't *feel* like one. Magma asks the question "what if we designed a proof language from scratch to take formal verification mainstream?" I think that makes it worthwhile.

Blaine, it will be important to point out that Coq/Lean/F* weren't really *trying* to create tools that were maximally usable and targeted at practicing engineers. It's useful to create something with that intent, even if there isn't any particular innovative idea that makes it dramatically different.

 -->
