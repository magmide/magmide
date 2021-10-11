we ought to only use nonword symbols to only indicate concepts of the *language*, things that can't be represented *within* the language, ones that apply to all types equally. that way we can get the broadest use from them

for example, using `..` or `...` for exclusive and inclusive range operators is embedding a *trait-level concept* (ability for some type to generate a range from a beginning to an end, or to perform an operation from one type to another) directly into the language syntax (better to just create a trait functions like `1 :upuntil 5` or `1 :upthrough 5` that return iterators). In contrast, using the same operators to spread an indexed or a named object or especially an indexed or named *type* into another is more general. it's kind of an operator on *kinds* and is shorthand for a *metaprogramming* construct over all types rather than a programming construct over concrete types.





always prefer to pass data explicitly and only proofs and types (which are really just types) implicitly



the big problem with the convention of global constructors for datatype fields is that the names end up having to be mangled since they aren't scoped and could collide! it's terrible design to easily allow these unscoped operators/constructors



One of the big ideas to create an approachable language is to really carefully design it to separate *hard prerequisite knowledge* from *defined knowledge*. Basically hard prerequisites are all the things someone absolutely must know in order to read or write the language, for example the syntax, primitive keywords and constructs, fundamental concepts, etc. These things can be much more terse and cryptic *because the learner has a known and prerequisite learning path to understand them* in the form of the basic language documentation. We know they'll be encountering them constantly, and we expect them to know them because we've provided such a paved path to do so, so it's okay if they're terse and efficient. The same doesn't go for things that can be defined *within* the language! Some random library shouldn't have the same power as the main language to introduce syntax or constructs, since we don't have any idea if someone will be able to track down that random library as the source of those constructs. The wall between what is primitively part of the language and what has been defined in user-land within the language should be crystal clear at all times.
