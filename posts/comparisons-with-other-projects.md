<!-- # Comparisons with other projects :construction: NOT FINISHED :construction:

This section seeks to thoroughly answer the question "How is Magma different than X?"

## Rust. Not actually safe, at least within the boundaries of the tool itself.
## LLVM. Not actually safe, which also means its optimizations can't be as aggressive. Focuses on downwards compilation rather than upwards metaprogrammatic recombination. Perhaps abstracts too much of the machine away in certain circumstances.

## Coq
because of metacoq and ml extraction, coq *technically* could be used to do everything in this project. however it's important to note that metacoq defines metaprogramming in coq without extraction, which means it will always perform quite poorly. magma by comparison defines its metaprograming in terms of *compute* magma rather than *theory* magma, so it can perform extremely well.
but to be truly honest, the real reason coq isn't good enough is because *it has a truly punishing user experience*. it's not good enough for coq to be *powerful*, it has to be *approachable* to meet the goal of making formal verification common in engineering practice
using myself as an example, I'm an extremely determined and curious person who has been hell-bent on understanding both it and the theory behind it, but since I'm not being led through it in an academic context where all the implicit knowledge is exposed through in-person mentors, it has been extremely challenging
coq has existed *since the 80s* and is still a very niche tool mostly only used by academics or former academics. rust by comparison doesn't offer anywhere close to the correctness-proving power, and has only been a mature language since 2015, but has achieved truly impressive adoption.
the most damning accusation I can make against coq is that it isn't even that broadly adopted *in academia*. why aren't almost all papers in mathematics, logic, philosophy, economics, and computer science not verified in coq? and yet approachable tools like python and julia and matlab are much more common? extreme logical power is useless if it can't be readily accessed

## Lean
I'm frankly not even sure what lean adds over coq. It certainly makes a few better minor design decisions, but it isn't really promising to change the game in any way, at least not sufficiently that it's worth tossing out all the existing work in coq.

## F*, Liquid Haskell
not fully dependently typed

Our lowest level of abstraction defines the limits of our control
Coq is least suited to those applications for which it is most necessary. High performance situations like operating systems, embedded systems, safety critical systems are almost always extremely time and resource constrained, and so must have both the greatest amount of performance and correctness.

This project is seeking to solve these problems by creating a Tool, and a Community. The Tool is largely a technical work, but one we will try to build as intuitively and elegantly as possible (in contrast to existing academic tools). The Community includes governance and education materials.

## vale
focused on cryptographic code, and it isn't a new proof assistant with the intent to make formal verification go mainstream, but instead a library in an existing proof assistant meant to help crypto researchers
however this project does in a way hint that the magma project is a good idea! it is also generic over different architectures and uses automatic verification condition generators

## ivy http://microsoft.github.io/ivy/language.html
only first order

## bedrock
Proprietary! It's essential systems like this aren't only controlled by corporations and governments.
http://adam.chlipala.net/papers/BedrockICFP13/BedrockICFP13.pdf
https://plv.csail.mit.edu/bedrock/
https://bedrocksystems.com/products/
The original purely research version of bedrock is yet another project that is promising for the magma project, since it shows that verified *macros* are possible and tractable. However it's still stuck in coq and therefore slow and obtuse.

need to look at xcap paper and other references in the bedrock paper


## https://github.com/mit-plv/bedrock2

at first glance it would seem this project is directly trying to do the same thing, but it seems to have dramatically different goals

- no self-hosting
- not creating a full proof checker
- building a language at a relatively high level of abstraction rather than bare metal assembly

however that team will definitely have a ton of useful insights to provide! the work is similar enough there's got to be enough overlap to make working together productive.


## mm0

b-system



Existing research around formal methods and program verification, such as in the deepspec project, I believe focuses extremely foolishly on old software workflows and tools. C and LLVM, despite being extremely powerful tools that profoundly advanced computing, are still necessarily "legacy" tools, and so only very clunkily fit into formal verification. Even Rust, as modern as it is, wasn't ever designed with formal verification in mind from the beginning, and inherited many possibly unhelpful assumptions, such as the operating system syscall model, LLVM itself, and the C++ memory model.

The ability to fully verify any program down to the metal completely unlocks the kinds of systems and abstractions we can build! The very act of building such a powerful tool removes all non-negotiable barriers in our way.

Formally verifying the correctness of legacy systems after the fact is necessarily much more difficult than developing new tools from first principles with verification in mind. The only reason I can think of for the post-hoc philosophy is one of terrified pragmatism, where researchers and engineers are too scared to rethink layers that "seem to be working". This seems foolish to me, since we don't *actually* have any confidence those old layers are actually correct. If you start from the bottom and produce fully verified foundations, and every layer you stack on top is itself verified, I conjecture you can move much faster than trying to avoid or work-around bugs in existing legacy foundations.

That work only matters once it has been applied in a way that benefits the world.

The goal behind this project is to answer the question: what would we design if we started from scratch? Magma really is an attempt to lay a completely new foundation for all of computing that could be used to entirely rethink how every layer of software infrastructure works, all the way down to the bare metal.
 -->
