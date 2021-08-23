we ought to only use nonword symbols to only indicate concepts of the *language*, things that can't be represented *within* the language, ones that apply to all types equally. that way we can get the broadest use from them

for example, using `..` or `...` for exclusive and inclusive range operators is embedding a *trait-level concept* (ability for some type to generate a range from a beginning to an end, or to perform an operation from one type to another) directly into the language syntax (better to just create a trait functions like `1 :upuntil 5` or `1 :upthrough 5` that return iterators). In contrast, using the same operators to spread an indexed or a named object or especially an indexed or named *type* into another is more general. it's kind of an operator on *kinds* and is shorthand for a *metaprogramming* construct over all types rather than a programming construct over concrete types.





always prefer to pass data explicitly and only proofs and types (which are really just types) implicitly



the big problem with the convention of global constructors for datatype fields is that the names end up having to be mangled since they aren't scoped and could collide! it's terrible design to easily allow these unscoped operators/constructors
