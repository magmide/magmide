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





























