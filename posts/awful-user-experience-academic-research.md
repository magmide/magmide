---
title: "Fixing the awful user experience design of academic computer science."
---

separating jargon from useful names
static pdfs
implicitly imported names
arbitrary symbols and user-defined notations
non-ascii artifacts

premature terseness
https://hal.inria.fr/hal-00816703v1/document

> One of the key ingredients to the concision, and intelligibility, of a mathematical
text is the use of notational conventions and even sometimes the abuse thereof.
These notational conventions are usually shaped by decades of practice by the
specialists of a given mathematical community. If some conventions may vary
according to the author’s taste, most tend to stabilize into a well-established
common practice. A trained reader can hence easily infer from the context of a
typeset mathematical formula he is reading all the information that is not explicit
in the formula but that is nonetheless necessary to the precise description of the
mathematical objects at stake.
Formalizing a page of mathematics using a proof assistant requires the description of objects and proofs at a level of detail that is few orders of magnitude
higher than the one at which a human reader would understand this description.
This paper is about the techniques that can be used to reproduce at the formal
level the ease authors of mathematics have to omit some part of the information
they would need to provide, because it can be inferred. In the context of a large
scale project like the formal proof of the Odd Order Theorem, which involves
a large and broad panel of algebraic theories that should be both developed
and combined, a faithful imitation of these practices becomes of crucial importance. Without them, the user of the proof assistant is soon overwhelmed by the
long-windedness of the mathematical statements at stake.

nope, because computers. in a tool with first-class metaprogramming, we can have both.

also, because we can *locally* rename or alias symbols, we can have *explicit and local* terseness without requiring a globally useless name
the length of a symbol's name should be inversely proportional to how often users will encounter that symbol. absolutely ubiquitous ones (`Theorem`, `forall`, `fun`, `Definition`) should have extremely terse or merely symbolic names. very uncommon ones should have very clear and descriptive names


more than one name for the same thing
there shouldn't be more than one way to do the same thing!
if a syntax sugar exists for a more "flexible" version of something, then detect and require the sugar




subset types can be better
the `&` syntax puts props onto a type (in both logic and computation land) but it remains the base type you declared, just with more assertions. these extended types can be used for anything they can be coerced to (immediate or easily automated coercions don't require extra notation, more complex ones require some kind of `by _` or `by tactic` and then proving)
proving theorems about a function using `function_name.thm` instead of bare `thm` (which implies only the return type? perhaps also about the arguments?) automatically puts the arguments of the function into context and implies the theorem is essentially adding a `&` subset type onto the result of that function. this can mean you can add props to an outside function if you import the module that includes your narrowing proof, it's like external impls
