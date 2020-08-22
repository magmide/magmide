Known types are simply all about how we're able to produce code.

One of the first things we need is a "bedrock type". This is the actual

If we implement this as a simply typed lambda calculus, then the "ordering" of everything is taken care of?
It's also less interesting, but that's okay, at least for now.

Really this first version to validate everything is basically just a simply typed lambda calculus but where there's some kind of "known" system that allows the functions to operate on types.


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

You need to sit and draw out how different types relate to each other.

Then you basically do all the work he does in SLTC. Define preservation and progress and all that.









Random theorizing about syntax:

```
fn debug value;
  match known(value).type;
    struct(fields) =>
      for key in fields;
        print("#{key}: #{value[key]}")
    nat(n) => print(n)
    bool(b) => print(b)
```
