# Crossing No Man's Land: figuring out Magmide's path to success

Should I extend this to a full blog post? Is this too terse?

- The real problem with existing proof languages like Coq *isn't* that they aren't powerful enough to be useful. Because of their core ideas of dependent types, proof objects, and resulting theoretical tools like separation logic, they're already extremely powerful and could be used *today* to build practical things.
- However they're so poorly designed and explained and exposed to practitioners that they might as well not exist. The real problem is the culture and incentives of academia.
- This is frustrating, since these projects have *technically* occupied large areas of use-case space, thereby making it much more difficult for a project like Magmide to quickly deliver incremental concrete value. Any small milestone Magmide could reach would only provide functionality technically already provided by other projects. In order to provide concrete verification value, we'd have to get detoured working on things that don't bring the language closer to a useful threshold of functionality.
- Most concrete verification problems, such as those in smart contracts or cryptography or even memory safe programming, mostly need *reusable theory libraries* defining correctness/safety conditions and algorithms to check for them, as well as a tool capable of applying those conditions to real implementation code. The Magmide project has nothing to do with domain specific theory libraries, but instead seeks to create a completely general tool that makes it uniquely possible for such libraries to be created, shared, and applied. It seeks to create a foundational ecosystem, giving others the tools and education to solve their own problems by leveraging [the verification pyramid](https://github.com/magmide/magmide#do-you-really-think-all-engineers-are-going-to-write-proofs-for-all-their-code).
- This is again frustrating, since those kinds of specific use cases are the only ones not already occupied by other projects. This makes me unsure what incremental project milestones Magmide could use to propel itself toward completion.
- I'm becoming more and more convinced the correct short term path is to first pursue the "Coq for programmers" project, an online book that clearly explains the core ideas of Coq, guides users through the rough edges of installing and working with the tool, gives a practical crash course in theorem proving, explains methods to parse and prove assertions about the contents of external files, and develops a handful of small but interesting case studies such as formalizing a simple smart contract language and verifying programs in it.
- The "Coq for programmers" project would test this hypothesis: if we create documentation/libraries/examples for existing proof languages, such that particularly correctness-conscious teams can use them for small but important applications, that will generate *just enough* interest for a broader audience to see the massive usability flaws as obvious and dire and worth solving. Then hopefully the energy and resources necessary to implement a design like Magmide's (or some other possibly better design!) will inevitably show up.
- An online book project can iterate very quickly, since it can be shared for feedback at almost every stage of completion. We can learn a ton about how programmers think about correctness, as well as how difficult it is to teach and understand the core ideas and heuristic skills of a proof assistant. By finding sharp edges and bad explanations and workarounds for them, we gain a much more solid map of all the problems we need to solve in Magmide.
- The "Coq for programmers" project would live inside the [Magmide github organization](https://github.com/magmide), and would routinely point to Magmide whenever it was explaining something it had to admit was obtuse or difficult. It would be a [fast static site](https://nuxtjs.org/announcements/going-full-static/), with niceties such as [quick search functionality](https://docsearch.algolia.com/) such as on [tailwindcss.com](https://tailwindcss.com/).
- The essential components of the "Coq for programmers" project:
  - Primer on prerequisite ideas: basic algebraic types, pure functional languages, boolean/predicate logic.
  - Core ideas section discussing: dependent types, type theory, proof objects/curry howard correspondence, indexed types, typeclasses as proof objects.
  - Course in interactive theorem proving discussing: rewriting, case analysis, induction, absurdity, automation, reflection, coinduction, setoid/morphism rewriting.
  - Hoare logic and separation logic.
- Optional "nice to have" components, depending on scope:
  - Fast searchable tactic and tactic notation reference, heavily skewed toward examples rather than formal explanations like in the [Coq reference](https://coq.inria.fr/refman/coq-tacindex.html).
  - Explanation of Iris.
  - Explanation of core ideas of category theory.


<!--
cute opening with koan and hypothetical about rust having bad ergonomics


All of the things I could think of are either some sort of coq parser/integration enabling proofs of qualities of source code, or just verified compilers. Both those things are somewhat useful but are ultimately detours.




Any project has to figure out how it's going to be successful, how it's going to power all the work that needs to happen to achieve its goals. For small projects that can be pushed to a useful point in "20% time" or by one person in their free time, this question is easy to answer: keep working until you have something to show.

For projects as massively ambitious as Magmide however, this question is extremely difficult to answer. I'm not capable of pushing this project to a useful point on my own in my free time, and in order for it to be successful I'll need help from a ton of very knowledgable and hardworking people. I've been talking with Juan Benet about this project, and he pointed me toward the [Tesla master plan](https://www.tesla.com/blog/secret-tesla-motors-master-plan-just-between-you-and-me) to use as inspiration. The Tesla master plan plotted several milestones for the car company to reach, with each intended to both be tractable given the resources available at that stage and bring in enough excitement and money to help the company reach the next milestone. [No matter what you may think about Tesla's overall impact on the world](TODO), the plan certainly seems to have worked. It's much easier to work toward small incremental goals that structurally support the pursuit of even larger goals than it is to jump toward a huge goal all at once.

So I've been thinking about what kinds of concretely useful milestones Magmide could reach that would create excitement and bring more contributors and support to the project, and I must admit I'm discouraged by what I've been finding. I'll summarize my thoughts, and then do more to support them.

Essentially: all the aspects of Magmide are there to place the design at a uniquely ["curve-bending"](https://www.youtube.com/watch?v=2ajos-0OWts) point in the design space. The goal is to create a fully powered proof assistant that is pleasant to work with and easy to apply to concrete computational problems. I assert that combination of features will be past a tipping-point of power, one that unleashes not just differences of *scale* in software quality and ambition, but differences in *kind*, all as a result of the force multiplying nature of a highly reusable and sharable verification pyramid. In other words, I think Magmide's design will uniquely enable software projects that are essentially impossible without the presence of *all* Magmide's essential features (maxed out in logical capability, maxed out in computational capability, maxed out in metaprogrammatic capability). If you reduce the scope of even one of the essential features of the project, you've just recreated what's already available in other projects and not really achieved anything. In order to achieve *any* of the goal, you unfortunately have to achieve basically *all* of it.

- If you don't have a fully powered dependent type proof checker, you lose massive swaths of functionality since you can no longer represent many different kinds of interesting and useful logical assertions, dramatically limiting the ability of the language to give valuable guarantees of correctness to many teams.
- If you don't have the ability to write and compile bare metal imperative programs in a way that's fully integrated with your proof assistant, your proof checker is stuck on an island of computationally useless type theoretical purity, dramatically limiting the practicality of the language.
- If you don't have the ability to write metaprograms in your integrated bare metal imperative language, the language can only support usage patterns that are explicitly supported by the compiler, dramatically limiting the expressivity and reusability of the language.

We can look at the space of languages plotted along three axes on a scale of 1-10: computational power (ability to express arbitrarily bare metal computation), logical power (ability to express arbitrarily complex logical assertions in the type system), and ergonomic usability (general "lovedness" of the design, tooling, documentation, teaching). These are my gut feeling ratings, and aren't at all objective.

|       | Computation | Logic | Usability |
|-------|-------------|-------|-----------|
| Rust  | 10          | 5     | 10        |
| C/C++ | 10          | 3     | 6         |
| Coq   | 3           | 10    | 4         |
| Lean  | 5           | 9     | 2         |
| F*    | 8           | 9     | 3         |

Here's a (sloppy and not at all accurate) graph:

![3D plot of language axes](posts/crossing-no-mans-land-1.png)

Rust is of course not "perfectly" usable, the 10 score is given to reflect the project's core cultural commitment to usability, and the fact that *given the inherent complexity of the language* they've done a superb job building a usable tool.

Coq is basically the C of logic, in that it's technically quite well supported, is the most powerful it could possibly be, has a (relatively) large ecosystem, and books that are acceptable but still not welcoming or distilled. But it has punishing tooling and cluttered syntax and often confusing semantics. It's still more usable than Lean or F*! A lot of work has gone into the interactive proof goal technology.

This is why Magmide is so insanely ambitious. It's essentially trying to (converge towards) scores of 10 on all three dimensions. Usability can converge slowly as long as both Computation and Logic are both maxed out, but if both Computation and Logic aren't maxed out then the project isn't usefully distinct from others.

Looking at the first few bullets of the [project and bootstrapping plan](https://github.com/magmide/magmide/blob/main/posts/design-of-magmide.md#project-plan), it's clear to see that Magmide won't be distinctly useful

In order to achieve *any* potential that isn't achievable using other tools, Magmide has to first redo the core work already done by those tools and then use that foundation to surpass.

Since the only unpicked spots in the value space are ones having to do with concrete verification problems that are actually usable for the engineers in those spaces, they are almost all ultimately detours on the path of actually implementing Magmide. The work of finding concretely useful projects that can excite and engage a larger verification audience is intrinsically a distraction from actually solving the real long-term problems of verification :(

One of the big values the project would add is just a new culture of verification that has escaped the suffocation of academia. Educational materials and nice tools are a big part of the usefulness
That's what we really have to do here. The problem is academic culture, and right now verification is trapped inside academic culture. We've already seen that engineering cultures are actually pretty good at (converging towards) approachability, practicality, usability, pragmatism (maybe I'm just thinking about Rust, but ultimately Rust both proves its possible and has actually been changing engineering culture as a whole it seems). Maybe that's the most important thing we can do, just help verification escape from the suffocation of academic culture and begin to grow in the richer earth of engineering culture.
the norms and teaching patterns and documentation expectations are awful in academia, which means that even though these incredibly powerful tools have been created, no one who would actually apply them to do concretely useful has any clue they even exist, let alone how to tractably use them

This is one of the most frustrating aspects of research debt! It seems very frequently that academics merrily walk along some research path, pluck all the low-hanging fruit of a domain, and then publish their work without even a second thought about how to expose that work to people with the means and intention to actually apply it in the world. This means that anyone coming along after them who wants to apply their work isn't seen as doing anything very valuable or interesting, but are just scraping up the dregs of the previous researcher. This makes it much more difficult for things to be applied at all!

Imagine a world where rust existed with the core powerful idea of ownership and lifetimes, but it was really clunky to use and all the tutorials and documentation and books were academic and disconnected. In that world anyone who wanted to build a better tool would have a much more difficult time, because anyone who wanted to use those core ideas technically already could


verifying smart contract languages is the thing that seems most likely to generate energy and resources, but it's an especially distant detour! the whole reason for formalizing LLVM as the intermediate steps of Magmide is that LLVM can be used as both the target and implementation language for the Magmide compiler. Doing something equivalent to that task is unavoidable on the path of bootstrapping the compiler.

Magmide isn't really intended to be the *final* product, the thing that people use to implement all the verified blockchains and compilers and languages in. It's intended to be the foundation for all those things, something that maximizes reusability so it can be a universal force multiplier for all software projects.

so my hypothesis is that if we just create better documentation/libraries/examples for *existing* dependent type languages, then that will generate *just enough* interest for a much larger body of people to see their massive usability flaws as obvious and dire and worth solving, such that the energy and resources necessary to implement a design like Magmide's (or some other possibly better design!) inevitably show up.

It's *already technically possible* to use something like Coq to process and prove assertions about arbitrary code. It's just extremely painful and clunky! And much more importantly, very few who might actually be interested in doing so *are even aware it's possible to*. What would happen if we both told them it was possible and taught them how to do it?

This brings me to yet another "comparison with X", except this comparison is with existing teaching materials


The nice thing about first doing a project like Coq for programmers is that it can get extremely fast feedback, since it doesn't have to be "done" to be shared or useful. We can iterate very quickly and find out a lot about how existing engineers think about correctness, as well as how difficult it is to teach and understand the core ideas and heuristic skills of a proof assistant. By finding all the sharp edges and bad explanations in the existing system and finding workarounds for them, we will gain a much more solid map of all the problems we need to solve in Magmide.





Coq for programmers, basically founding a bastion of people who want decent explanations and useful tools

A binding tool that reuses the coq proof checker to make a better interactive system, isn't linear, has nice asserted types, could be used to write verifiers for other languages

a programming language becomes more useful or gains power as a function of its core features/primitives (representing what it's theoretically capable of doing), its tooling (representing how easy it is to actually use/access those core features), its ecosystem (representing how much reusable work has already been done), and its documentation and educational materials (representing how easy it is to learn how to do all of this). the foundation and most important aspect of a language is its core features, since if the primitives of the language can't possibly support something then none of the other aspects (tooling, ecosystem, documentation) can make up for that fact. only a fundamental change to the language itself can possibly bring about that support

this means that the three orbital features are mutually self-reinforcing and create a feedback loop. improving any of them will tend to make it more tractable and attractive to improve the others.

for a language like coq the core primitives that make it so powerful are dependent types and proof objects, and using those primitives one can implement a separation logic which is similarly powerful. its quite difficult to create a language with dependent types and proof objects, since the type/proof checking algorithm is very subtle and logically complex, and unfortunately the threshold is fairly "all or nothing". either you have a proof checker capable of correctly supporting those features or you don't.

a zen koan: if a language has powerful features but no one can understand how to use them, have they really been implemented?
 -->
