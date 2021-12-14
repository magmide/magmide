<!-- # Comparisons with other projects

An important question to ask of any project is: "How is the project different than X?" or more probingly: "Why build this new project instead of just using X? Why can't X address your needs?" This page attempts to thorougly answer that question.

Many comparisons with other projects aren't actually that interesting, since the projects don't even have the same goals, or the comparison project isn't "maxed out" in one of Magmide's main features [(logical/computational/expressive power)](https://github.com/blainehansen/magmide#is-this-design-too-ambitious-is-it-just-everything-and-the-kitchen-sink).

Many of these projects are essentially attempts to allow users to verify code in a fully automated way. Although full automation is nice, I ultimately don't think it's productive to hide the underlying logical ideas from users, instead of just putting in the work to explain them properly. If a tool allows manual proofs alongside metaprogramming capabilities then it can still have full automation in many domains, whereas if a tool can only prove a certain subset of claims automatically then its forever limited to that subset.

Engineers can understand these ideas! They just need to first understand *why those ideas are useful*, and then have them explained effectively. Engineers aren't interested in doing your explanation for you. It seems academics confuse "this concept is too difficult for users to understand" and "we're explaining this concept really poorly and users don't see what value we're adding". Discriminated unions and resource ownership are both extremely simple ideas (*understanding* Rust ownership is easy, it's just *using* it that can be hard), and allow extremely powerful languages. And yet these ideas were buried in academia or niche functional languages for **decades** before someone finally trusted practitioners enough to try in Rust. I don't think mere pre and post annotations on functions is enough. People need the full power, *but they also need to be effectively taught how to use it!*

It feels like academics are using something as powerful as lightsabers but extremely awkwardly holding them with pool cues. But then they give practioners [Fisher Price circular saws](https://www.amazon.co.uk/Fisher-Price-W4745-REV-Circular-Handy-Manny/dp/B005Q9WC4W) and get discouraged when they aren't widely adopted.

- Rust/LLVM: Not maxed out in logical power, can't prove correctness.
- Liquid Haskell: Not maxed out in logical power since we only have refinement types and not a full type theory. Not maxed out in computational power since Haskell doesn't easily allow bare metal operations.
- [Ivy](http://microsoft.github.io/ivy/language.html): Only a first order logic, so not maxed out in logical power. However the idea of separating pure functions and imperative procedures was part of the inspiration for the Logic/Host Magmide separation.
- [TLA+](https://en.wikipedia.org/wiki/TLA%2B): Not based on dependent type theory, so possibly capable of representing paradoxes, but regardless TLA+ could be implemented in Magmide. Not maxed out in computational power, since the language itself is only intended for specification writing rather than combined code/proofs.
- Isabelle/HOL, ACL2, PVS, Twelf, [Rodin tool/B-method](https://en.wikipedia.org/wiki/Rodin_tool): Not maxed out in logical power, [missing either dependent types, higher order logic, or general `Prop` types](http://adam.chlipala.net/cpdt/html/Cpdt.Intro.html), or didn't use a bare metal language and separation logic to reason about real programs.
- [Dafny](https://dafny-lang.github.io/dafny/): Not maxed out in computational power, since it only exposes a fairly high level imperative language.
- [Rudra](https://github.com/sslab-gatech/Rudra): Intended to only uncover common undefined behaviors, rather than to prove arbitrary properties.
- [Prusti](https://github.com/viperproject/prusti-dev): Intended to only automatically check for absence of panics or overflows, or pre/post conditions rather than arbitrary properties.
- [RustHorn](https://github.com/hopv/rust-horn): Intended to only automatically check pre/post conditions rather than arbitrary properties.
- [KLEE](https://llvm.org/pubs/2008-12-OSDI-KLEE.html) and related tools: Intended to only generate reasonably high coverage tests rather than prove arbitrary properties.
- [Property-based testing tools](https://www.lpalmieri.com/posts/an-introduction-to-property-based-testing-in-rust/): Intended to only test a random subset of values rather than all possible values.

Then there are many much more academic projects which apply formal methods to verify software at the same deep level as Magmide intends to, but don't have the intent to create a tool that can act as both the logical and computational foundation for all software. These research projects will be very useful to learn from, but again their goals aren't as directly focused on broad engineering practice as Magmide.

- [Lambda Rust/RustBelt](https://www.ralfj.de/research/phd/thesis-screen.pdf): A formalization of a realistic subset of Rust, proofs of its soundness, and proofs of the soundness of many core Rust libraries that use `unsafe`. This project is what spurred the development of the Iris separation logic that will be extensively used in Magmide. RustBelt is obviously the direct ancestor of the Magmide project, and laid the formal foundations for it to be possible. However it only intended to verify Rust code "on the side", rather than creating a tool capable of *implementing* a verified version of Rust. I hope to deeply collaborate with the RustBelt authors!
- [Vellvm](https://github.com/vellvm/vellvm): A formalization of LLVM in Coq. Doesn't intend to use this formalization to create a self-hosting/verifying proof assitant. Importantly, doesn't use a higher order separation logic such as Iris, so it likely can't be used directly in Magmide. However the project itself and its creators will be invaluable sources of knowledge.
- [Vale](https://www.microsoft.com/en-us/research/wp-content/uploads/2017/08/Vale.pdf): A Dafny tool capable of verifying the correctness of annotated assembly language cryptographic routines. This project is extremely cool and similar to Magmide in the sense that it is capable of verifying arbitrary conditions of bare metal code. However, it is very narrowly focused on cryptographic applications, and has no intention of implementing a general purpose language. However the success of the project (and inspired work such as [this more efficient F* verification condition generator](https://www.andrew.cmu.edu/user/bparno/papers/vale-popl.pdf)) shows that something like Magmide is realistic and tractable.
- [Bedrock](http://adam.chlipala.net/papers/BedrockICFP13/BedrockICFP13.pdf): A project that honestly feels very similar to Magmide! Bedrock is especially concerned with metaprogramming and verification of low-level code. However the project has been closed and the research group has been working on a [much smaller successor project `bedrock2`](https://github.com/mit-plv/bedrock2), along with [many other more academic projects](https://github.com/mit-plv/). It also seems [Adam Chlipala](http://adam.chlipala.net) isn't contributing to `bedrock2` directly, and may be more focused on teaching and advising the (private and proprietary) company [Bedrock Systems](https://bedrocksystems.com)?? I honestly ought to email some of those researchers, but I'll admit I'm sort of scared to ask Dr. Chlipala about the proprietary company (I strongly believe it's absolutely essential that these verification systems are open source, not only controlled by corporations and governments, and are shared as broadly as possible). However the original bedrock is yet another project that is promising for Magmide, since it shows that verified *macros* are possible and tractable. My (wild conjecture) guess about why the original project was discontinued is because Iris came about, which seems reasonable since just in 2020 the research group [had a guest post about Iris on their blog](https://plv.csail.mit.edu/blog/iris-intro.html#iris-intro). It probably didn't make sense to pursue their previous direction if they could learn/use Iris instead.
- [DeepSpec](https://deepspec.org/main): A project verifying a whole family of extant systems end-to-end. This again is very similar to the Magmide project, but isn't at all focused on creating tools suitable for mainstream engineers, or building a *new* foundational language. Although I think this research is extremely valuable, I don't think it's going to create a lot of industry excitement for verification.
- [Metamath Zero](https://github.com/digama0/mm0): A project intended to create a minimal and extremely efficient language for specifications and proofs. This project is very focused on simplicity of the proof language and the speed of the verifier, which aren't particular goals of the Magmide project. Magmide is more concerned with creating a foundational tool intended for mainstream use, so simplicity/speed of the verifier is desired but not essential. Instead of relying on a simple verifier implementation, Magmide is relying on Coq to bootstrap initial correctness, and speed of verification isn't a goal until after the project is bootstrapped [("make it work, make it right, make it fast")](https://wiki.c2.com/?MakeItWorkMakeItRightMakeItFast). However I'm excited to learn lessons from mm0 both during and after Magmide's bootstrapping!

Now to the really interesting comparisons, those with other higher order dependently typed proof assistants. I'll focus on Coq, Lean, and F\*. The "real" reason these projects haven't already achieved Magmide's goal is likely simply that they *weren't actually trying to*. These languages are pretty obviously by/for academics. This fact shines through in two major ways:

- They are too academic! I'm not saying they're "too complicated", I'm saying they're "pointlessly obtuse". I've already talked about this a lot.
- They only use functional languages, and don't give access to bare metal performance or correctness realities.

All of these projects could be used to *logically define* Magmide, and since they all *technically* have the capability to produce running code, they could rival the intended use cases of Magmide. However none of them quite fit, with F* being the most frustratingly close.

How did all of them not achieve the goal? A large reason is that they're all built by academics rather than practicing engineers, so the projects themselves are hidden behind research debt or punishing teaching materials or difficult user experience. But I think there's a more nuanced reason, that the creators of those projects fell victim to a core misunderstanding that kept them from achieving general adoption: they made the mistake of thinking the functional programming language *itself* would be the thing people used to build software.

Functional programming may have its devotees, but there's a reason it's much less adopted than imperative methods: *real computers aren't pure or functional!* The main idea of functional programming is a lie, one that makes some problems easier to reason about, but at the cost of completely hiding the real nature of the actual problem being solved. Engineers trying to build high performance systems that take advantage of the real machine will never be willing to make that sacrifice.

The Magmide design in contrast *splits up* Logic and Host Magmide into separate "dual" languages, each used in exactly the way it's most natural. Logic Magmide is the imaginary level where pure functions and mathematical algorithms and idealized models exist, which is the perfect realization of the goals of functional programming. Then those logical structures only exist at compile time to help reason about the messy and truly computational behavior of Host Magmide.

So in other words...

![stop trying to make functional programming happen, it's not going to happen](https://blainehansen.me/stop-trying-to-make-fp-happen.jpg)

... or at least, just use pure functional languages in contexts where their purity is actually correct.

I obviously don't think functional languages should never be used to write programs. But if we don't accept the limitations of functional programming, we're just being dogmatic. Let's instead acknowledge the imperative foundation we must build on, and then imagine the kinds of incredible functional languages we could build with the capability to logically prove the correctness of the implementation and optimizations according to the underlying imperative machine!

This again brings to mind the possible comparison with Rust and C: "Why build Rust? Can't you do everything in C you could do in Rust?" Well, yes you could! But... do you really want to? It isn't *only* about whether something's possible, it's about whether it's natural and clear and ergonomic. We don't want abstraction mismatches in our foundational language!

Let's get into the nitty gritty:

## Coq

because of metacoq and ml extraction, coq *technically* could be used to do everything in this project. however it's important to note that metacoq defines metaprogramming in coq without extraction, which means it will always perform quite poorly. magmide by comparison defines its metaprograming in terms of *compute* magmide rather than *theory* magmide, so it can perform extremely well.
but to be truly honest, the real reason coq isn't good enough is because *it has a truly punishing user experience*. it's not good enough for coq to be *powerful*, it has to be *approachable* to meet the goal of making formal verification common in engineering practice
using myself as an example, I'm an extremely determined and curious person who has been hell-bent on understanding both it and the theory behind it, but since I'm not being led through it in an academic context where all the implicit knowledge is exposed through in-person mentors, it has been extremely challenging
Coq has existed *since 1989* and is still a very niche tool mostly only used by academics or former academics. Rust by comparison doesn't offer anywhere close to the correctness-proving power, and has only been a mature language since 2015, but has achieved truly impressive adoption.
the most damning accusation I can make against coq is that it isn't even that broadly adopted *in academia*. why aren't almost all papers in mathematics, logic, philosophy, economics, and computer science not verified in coq? and yet approachable tools like python and julia and matlab are much more common? extreme logical power is useless if it can't be readily accessed

Another really important problem is that Coq can only produce runnable programs with the extraction mechanism, which isn't itself verified and even then relies on the interpreter of the target language being correct and on extracted datatypes (which you can arbitrarily override!) corresponding to the Coq datatypes.

## Lean

I'm frankly not even sure what lean adds over coq. It certainly makes a few better minor design decisions, but it isn't really promising to change the game in any way, at least not sufficiently that it's worth tossing out all the existing work in coq. It seems much more focused on the needs of pure mathematicians, and doesn't seem to have very heavily prioritized automation.

Lean seems to have made the same mistake as F*, by including a bunch of "real" computational types and thinking that would be good enough for engineers to write real programs in Lean.

## F*

I think the way in which they've blended effectful programming and type theory is actually counterproductive. Effectful programming is inherently imperative, and blending the two only seems like it would appeal to people who insist on using functional paradigms. The reason I think Magmide should use a pure calculus of constructions is that the proving/modelling layer is intentionally "imaginary". The dependent type system is essentially just a higher order type system for an infinite range of concrete languages, and so only exists at compile time. The blend is confusing and "buries the lede".

In a real computational environment, *all* operations are imperative and effectful. In a purely logical environment, *no* operations are imperative or effectful. Blurring this distinction isn't helpful, but will be confusing and cluttering for everyone.

If you're writing code that's supposed to model C, then it's obvious that we're using the C memory model and following the C calling convention! Needing to explicitly point that fact out with an effect type isn't productive.

F* ultimately suffers from the same problems as Coq. It's obvious it was written by academics rather than practitioners, and the needs and concerns of academics shine through in the design.

Most effect type theories seems more concerned with logical parsimony than raw usefulness. In real software systems engineers only care about effects if they want to prevent bad things from happening or intercept some operations. Most real functions will have *many* effects, and so it's better to use automated checks/proofs to make assertions about the effectfulness of a function rather than writing out every single one explicitly.

And unforunately, F* is also a frustrating name. It isn't clear to everyone how to say it (star? asterisk? splat? bullet?) and searching for the name online is an annoying dance of trying combinations like `f-star`, `f star`, or `"f*"`.

This is all very frustrating, because F* is *so close!* It's right on top of the right feature set, but the fact that it *hasn't* caught the attention of the engineering mainstream is likely the only evidence you need that it *won't*. Maybe it's just not done! Maybe it could flesh out and distill its documentation and add a few conveniences, but I just don't think that's going to be enough.

The case could certainly be made that Magmide should *use* F* to bootstrap Magmide. But the Iris project is all in Coq! Iris will likely need to be ported to Magmide once it's bootstrapped, so it would be nice to avoid having to also port it to F* before even starting.

Maybe these problems all seem like minor gripes to you. Maybe you're right! But again, the intention of this project is to build a proof language *for engineers*. Academics have so many little cultural quirks and invisible assumptions, and I rarely come across an academic project that doesn't *feel* like one. Magmide asks the question "what if we designed a proof language from scratch to take formal verification mainstream?" I think that makes it worthwhile.

It's not enough to just put a new coat of paint on a proof language. If a proof language is capable of proving basically any (provable) claim, then it will be eternally frustrating to not be able to reason about basically any real program!

This is why the Logic/Host separation is so fitting. If a dependently typed language is going to be self-hosting/verifying, then it will necessarily formalize a computational language at the same level as LLVM, one capable of being compiled for many different specific architectures and environments. The very act of doing that *for itself* has the happy coincidence of also giving it the ability to do so *for anything else*. We can support two massive families of use cases with one body of work. By going all the way in both logical and computational power, we ironically end up having to make fewer built-in decisions.
 -->
