```coq
Inductive typ: Type :=
  | Unit: typ
  | Nat: typ
  | Bool: typ
  | Arrow: typ -> typ -> typ
.

Fixpoint typeDenote (t: typ): Set :=
  match t with
    | Unit => unit
    | Nat => nat
    | Bool => bool
    | Arrow arg ret => typeDenote arg -> typeDenote ret
  end.

(*Definition typctx := list type.*)

Inductive exp: list typ -> typ -> Type :=
| Const: forall env newtyp (value: typeDenote newtyp), exp env newtyp
| Var: forall env newtyp, member newtyp env -> exp env newtyp
| App: forall env arg ret, exp env (Arrow arg ret) -> exp env arg -> exp env ret
| Abs: forall env arg ret, exp (arg :: env) ret -> exp env (Arrow arg ret).

Arguments Const [env].

(*Definition a: exp hlist Bool := Const HNil true.*)

Fixpoint expDenote env t (e: exp env t): hlist typeDenote env -> typeDenote t :=
  match e with
    | Const _ value => fun _ => tt

    | Var _ _ mem => fun s => hget s mem
    | App _ _ _ e1 e2 => fun s => (expDenote e1 s) (expDenote e2 s)
    | Abs _ _ _ e' => fun s => fun x => expDenote e' (HCons x s)
  end.

(*Eval simpl in expDenote Const HNil.*)






(*
  okay I feel like I want to have a `compile` function that takes terms and just reduces the knowns, typechecks them, and outputs a string representing the "compiled" program
  then a `run` function that reduces the knowns and typechecks the program, but then reduces all the terms and outputs the "stdout" of the program
  this is presupposing that you'll have some kind of effectful commands that append some string to the "stdout". that seems like the more natural way I would prefer to structure a language that I'll eventually be using to learn while making a real imperative language
*)

(*Require Import Coq.Strings.String.
Require Import theorems.Maps.

Inductive typ: Type :=
  (*| Generic*)
  | Bool
  | Nat
  | Arrow (input output: typ)
  | UnionNil
  | UnionCons (arm_name: string) (arm_type: typ) (rest: typ)
  | TupleNil
  | TupleCons (left right: typ)
  (*| KnownType (type_value: trm)*)
  (*| KnownValue (value: trm)*)
.

Inductive Arm: Type :=
  | arm (arm_name: string).

Inductive trm: Type :=
  | tru | fls
  | debug_bool
  (*| nat_const (n: nat)*)
  (*| nat_plus (left right: trm)*)
  (*| debug_nat*)
  | binding (decl_name: string) (after: trm)
  | usage (var_name: string)
  | test (conditional iftru iffls: trm)
  | fn (args_name: string) (output_type: typ) (body: trm)
  | call (target_fn args: trm)
  | union_nil
  | union_cons (arm_name: string) (arm_value: trm) (rest_type: typ)
  | union_match (tr: trm) (arms: list (string * trm))
  | tuple_nil
  | tuple_cons (left right: trm)
  | tuple_access (tup: trm) (index: nat)
.


Fixpoint tuple_lookup (n: nat) (tr: trm): option trm :=
  match tr with
  | tuple_cons t tr' => match n with
    | 0 => Some t
    | S n' => tuple_lookup n' tr'
    end
  | _ => None
  end
.

Fixpoint union_lookup (tr: trm) (arms: list (string, (string * trm))): option trm :=
  match tr with
  | union_cons tr_arm_name tr_arm_value _ => match arms with
    | (arm_name, (arm_var, arm_body)) :: arms' => if eqb_string tr_arm_name arm_name
      then Some (substitute arm_var tr_arm_value arm_body)
      else union_lookup tr arms'
    | [] => None
    end
  | _ => None
  end
.
*)






(*Require Import Coq.Strings.String.
Require Import theorems.Maps.

(*Notation memarr := (@list string).*)


Inductive typ: Type :=
  | Base: string -> typ
  | Arrow: typ -> typ -> typ
  | TupleNil: typ
  | TupleCons: typ -> typ -> typ.


Inductive trm: Type :=
  | var: string -> trm
  | call: trm -> trm -> trm
  | fn: string -> typ -> trm -> trm
  (* tuples *)
  | tuple_proj: trm -> nat -> trm
  | tuple_nil: trm
  | tuple_cons: trm -> trm -> trm.


Inductive tuple_typ: typ -> Prop :=
  | TTnil:
    tuple_typ TupleNil
  | TTcons: forall T1 T2,
    tuple_typ (TupleCons T1 T2).

Inductive well_formed_typ: typ -> Prop :=
  | wfBase: forall i,
    well_formed_typ (Base i)
  | wfArrow: forall T1 T2,
    well_formed_typ T1 ->
    well_formed_typ T2 ->
    well_formed_typ (Arrow T1 T2)
  | wfTupleNil:
    well_formed_typ TupleNil
  | wfTupleCons: forall T1 T2,
    well_formed_typ T1 ->
    well_formed_typ T2 ->
    tuple_typ T2 ->
    well_formed_typ (TupleCons T1 T2).

Hint Constructors tuple_typ well_formed_typ.

Inductive tuple_trm: trm -> Prop :=
  | tuple_tuple_nil:
    tuple_trm tuple_nil
  | tuple_trm_tuple_cons: forall t1 t2,
    tuple_trm (tuple_cons t1 t2).

Hint Constructors tuple_trm.

(*Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).*)
Notation "{ }" := tuple_nil.
Notation "{ x ; .. ; y }" := (tuple_cons x .. (tuple_cons y tuple_nil) ..).


Fixpoint subst (prev: string) (next: trm) (target: trm) : trm :=
  match target with
  | var y => if eqb_string prev y then next else target
  | fn y T t1 => fn y T (if eqb_string prev y then t1 else (subst prev next t1))
  | call t1 t2 => call (subst prev next t1) (subst prev next t2)
  | tuple_proj t1 i => tuple_proj (subst prev next t1) i
  | tuple_nil => tuple_nil
  | tuple_cons t1 tup => tuple_cons (subst prev next t1) (subst prev next tup)
  end.

Notation "'[' prev ':=' next ']' target" := (subst prev next target) (at level 20).


Inductive value: trm -> Prop :=
  | v_fn: forall x T11 t12,
    value (fn x T11 t12)
  | v_tuple_nil: value tuple_nil
  | v_tuple_cons: forall v1 vtup,
    value v1 ->
    value vtup ->
    value (tuple_cons v1 vtup).

Hint Constructors value.

Fixpoint tuple_lookup (n: nat) (tr: trm): option trm :=
  match tr with
  | tuple_cons t tr' => match n with
    | 0 => Some t
    | S n' => tuple_lookup n' tr'
    end
  | _ => None
  end.


Open Scope string_scope.

Notation a := (var "a").
Notation b := (var "b").
Notation c := (var "c").
Notation d := (var "d").
Notation e := (var "e").
Notation f := (var "f").
Notation g := (var "g").
Notation l := (var "l").
Notation A := (Base "A").
Notation B := (Base "B").
Notation k := (var "k").
Notation i1 := (var "i1").
Notation i2 := (var "i2").


Example test_tuple_lookup_nil_0:
  (tuple_lookup 0 {}) = None.
Proof. reflexivity. Qed.

Example test_tuple_lookup_nil_1:
  (tuple_lookup 1 {}) = None.
Proof. reflexivity. Qed.

Example test_tuple_lookup_cons_valid_0_a:
  (tuple_lookup 0 { a }) = Some a.
Proof. reflexivity. Qed.

Example test_tuple_lookup_cons_valid_0_a_b:
  (tuple_lookup 0 { a; b }) = Some a.
Proof. reflexivity. Qed.

Example test_tuple_lookup_cons_invalid:
  (tuple_lookup 3 { a; b; c }) = None.
Proof. reflexivity. Qed.
*)

```







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
