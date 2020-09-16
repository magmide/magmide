You should probably write out this whole (almost) blog post informally before you really dig into the formal stuff. This is just such a huge undertaking, first understanding what you even precisely want to accomplish is a good idea.

Think of it like writing the documentation before you write the code! You do that all the time since it helps clarify what's special and useful about the code, and what features it needs to have.












So I guess this whole project has a few beliefs:

- We can and should bring formally verified programming with dependent types to the mainstream.
- We can and should make a bedrock language with a dependent type system that is defined in the smallest and most primitive constructs of machine computation, because all the code we actually write is intended for such systems.
- We should design some set of "known" combinators to allow someone to write a compiler in bedrock that translates some set of terms of a language into bedrock, so that arbitrarily convenient and powerful languages can be implemented from these bedrock building blocks. By doing so we can have all languages be truly safe and also truly interoperable. Formalizing and implementing the algorithms for a type system in bedrock allows you to prove that all of your derived forms are valid in bedrock! Dependent types and the ability to prove arbitrary statements is *most* powerful at this lowest level of abstraction, since it allows us to build literally any language construct we can imagine, since the derived types people build can encapsulate on bytes and propositions, which are the most flexible constructs for machine computation.








So far you've considered "generics" as something that exists in the "computable" set of terms, but that's not really correct
a generic function is actually two function calls, the first of a "known" function that takes some function containing type variables and a type substitution mapping those type variables to concrete types (or to other type variables! which can allow you to partially apply generics, there should probably be two functions at least for now, one that expects all type variables to be resolved and returns a concrete function, and one that allows for partial application and returns a known function. both of these functions can resolve to either their intended type or a compilation error term)


so you should probably have these inductives: concrete types (which include the types that encode type variables in a "computable" way. there's some thinking to do here, but I think this means that you can pass any concrete term to a known function as long as it meets some "known" criteria which for functions is assumed and but for other values simply means that they have to be constants) and concrete terms (basically just the base lambda calculus stuff), known types and known terms (which are the "inductive" step, since they can take both concrete things as well as other knowns, creating the unbounded but finite dag of compilation)

all of this means that bedrock itself won't actually have "primitive syntactic" generics like other languages do, but syntactic generics will of course be possible by means of translation in any theoretical derived language.




It is actually possible to have "dynamic" functions! By the time bedrock is done, *everything* will just be bytes, and *instructions* are just bytes! All you need in order to allow dynamic functions is to "include" the typechecker or compiler in your final "computable" binary! All we've done here is "move up" the known steps, since what is typically known and performed at compile time is still "dynamic" in the sense that actual machine computation is being performed, just like it will be at runtime! compile time is just a special case of runtime!







Known types are simply all about how we're able to produce code.

One of the first things we need is a "bedrock type". This is the actual

If we implement this as a simply typed lambda calculus, then the "ordering" of everything is taken care of?
It's also less interesting, but that's okay, at least for now.

Really this first version to validate everything is basically just a simply typed lambda calculus but where there's some kind of "known" system that allows the functions to operate on types.


You need to sit and draw out how different types relate to each other.

Then you basically do all the work he does in SLTC. Define preservation and progress and all that.





First you have "computable terms". These are basically just terms that have been reduced enough that they can actually be "run", whatever that means in the context you're talking about. In a "compiled" language that means something that's been reduced enough to be output as llvm and run. In these more theoretical contexts it's just reduced down to a subset of terms that have been deemed computable.

The interesting part of the "computable term" definition is what terms it reveals as *not* being computable. These are basically all the "known" structures. Those known structures need to be reduced all the way to computable ones before they're ready to actually compute. But the *bodies* of the known structures *themselves* also need to be reduced as well! This produces a directed acyclic graph of "known" terms that need to be reduced in order all the way down to computable terms.


Does this mean that the only "types" we actually *need* are computable ones? It certainly seems that way, since we can simply say that the only thing we need to "typecheck" is a computable term that we're about to compute. Having more "advanced" higher order types is merely useful for a more ergonomic version of the language that we can do a "higher order" typecheck on before even bothering to reduce any terms. Higher order typechecks probably also play right into a full proof-capable language, one where you can prove that your higher order functions will always reduce to things that will typecheck.

For now it seems all this version needs is an initial "dag" check, if it even allows recursion that is.


Does this mean that the typing relation is something like this?

```v
Inductive ty : Type :=
  | Bool: ty
  | Arrow: ty -> ty -> ty
  | Known: ty -> ty.

I think this really is it! At least for formally defining it, all this "Known" type needs to do to work is to "reduce" in a different way. It yields an abstract description of the type or value or whatever rather than another term. Or rather the term it reduces to *is* the type.

Is this true? I need to keep thinking.

Inductive tm : Type :=
  | var : string -> tm
  | call : tm -> tm -> tm
  | fn : string -> ty -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.
```




maybe we define types not inherently, but as things that reduce from known terms?
or maybe our typechecking function and relation aren't total, we can't (and don't want to bother to) typecheck terms that haven't reduced all the way to computable terms. the typechecking function should return `option` on all terms that aren't computable







So let's say we had a language that had these types

bool: typ; obvious, computable
nat: typ; obvious, computable
arrow: typ -> typ -> typ; obvious, computable
typvalue: booltyp | nattyp | arrowtyp; hmmmm, this is computable since we need to compute based on it to progress and output something
need union (variant) and tuple and unit
known: (tm -> tm) -> typ?; not computable directly, but we can reduce it to being computable

and these terms:

tru: tm; obvious, computable
fls: tm; obvious, computable
n: nat -> tm; obvious, computable
known






While reading types and programming languages, something's occuring to me.

The base "bedrock" language has to be fully strict and exact in the way it defines the calculable language, which can basically only consist of arrays of bytes and propositions on those arrays of bytes.

However once we've done that, we can build all kinds of convenient language forms and theorems about them by simply defining them as meta-functions in that bedrock language.

For example, in the strict "bedrock" sense, subtyping is basically never valid, since subtyping ignores the very concrete byte-level representation of the structures. But if we have a "meta-language" (which is just a "compiler" that itself is a program in bedrock that takes the terms of the meta-language and computes them to bedrock) then we can allow subtyping simply by saying that whenever we encounter an action that gives a subtype, we can compile that action into the actually valid bytes level action that will satisfy the propositions of bedrock. In this way we have a *provably correct* desugaring process.
