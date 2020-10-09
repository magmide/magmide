Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List Cpdt.CpdtTactics Cpdt.DepList theorems.Maps Coq.Strings.String.

(*blaine, you need to write examples of what you'd like to accomplish in the near term*)
(*some concrete examples of "metaprogramming" in some abstract language is all you need*)
(*you don't have to prove almost anything about them, at least not at first, just get them working as expected and then prove things about them*)

(*the term type you create *is* the meta datatype! syntactic macros are just functions that operate on the same objects as the compiler*)

Inductive ty: Type :=
	| Ty_Bool: ty
	| Ty_Arrow (domain: ty) (range: ty): ty.

Inductive tm: Type :=
	| tm_var (name: string): tm
	| tm_call (fn: tm) (arg: tm): tm
	| tm_fn (argname: string) (argty: ty) (body: tm): tm
	| tm_true: tm
	| tm_false: tm
	| tm_if (test: tm) (tbody: tm) (fbody: tm): tm.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "U -> T" := (Ty_Arrow U T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_call x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" := (tm_fn x t y) (
	in custom stlc at level 90, x at level 99,
	t custom stlc at level 99,
	y custom stlc at level 99,
	left associativity
).
Coercion tm_var : string >-> tm.
Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" := (tm_if x y z) (
	in custom stlc at level 89,
	x custom stlc at level 99,
	y custom stlc at level 99,
	z custom stlc at level 99,
	left associativity
).
Notation "'true'" := true (at level 1).
Notation "'true'" := tm_true (in custom stlc at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false (in custom stlc at level 0).

Definition x: string := "x".
Definition y: string := "y".
Definition z: string := "z".
Hint Unfold x: core.
Hint Unfold y: core.
Hint Unfold z: core.

Notation idB := <{\x:Bool, x}>.
Notation idBB := <{\x:Bool -> Bool, x}>.

Inductive value: tm -> Prop :=
	| v_fn: forall arg T body,
			value <{\arg:T, body}>
	| v_true:
			value <{true}>
	| v_false:
			value <{false}>.
Hint Constructors value: core.


Reserved Notation "'[' old ':=' new ']' target" (in custom stlc at level 20, old constr).
Fixpoint subst (old: string) (new: tm) (target: tm): tm :=
	match target with
	| <{true}> => <{true}>
	| <{false}> => <{false}>
	| tm_var varname =>
			if string_dec old varname then new else target
	| <{\var:T, body}> =>
			if string_dec old var then target else <{\var:T, [old:=new] body}>
	| <{fn arg}> =>
			<{([old:=new] fn) ([old:=new] arg)}>
	| <{if test then tbody else fbody}> =>
			<{if ([old:=new] test) then ([old:=new] tbody) else ([old:=new] fbody)}>
	end

where "'[' old ':=' new ']' target" := (subst old new target) (in custom stlc).
Hint Unfold subst: core.

Check <{[x:=true] x}>.
Compute <{[x:=true] x}>.

Inductive substi (old: string) (new: tm): tm -> tm -> Prop :=
	| s_true: substi old new <{true}> <{true}>
	| s_false: substi old new <{false}> <{false}>
	| s_var_matches:
			substi old new (tm_var old) new
	| s_var_not_matches: forall varname,
			let varitem := (tm_var varname) in
			old <> varname -> substi old new varitem varitem
	| s_fn_matches: forall T body,
			let fn := <{\old:T, body}> in
			substi old new fn fn
	| s_fn_not_matches: forall var T body newbody,
			old <> var
			-> substi old new body newbody
			-> substi old new <{\var:T, body}> <{\var:T, newbody}>
	| s_fn_call: forall fn newfn arg newarg,
			substi old new fn newfn
			-> substi old new arg newarg
			-> substi old new <{fn arg}> <{newfn newarg}>
	| s_if: forall test tbody fbody newtest newtbody newfbody,
			substi old new test newtest
			-> substi old new tbody newtbody
			-> substi old new fbody newfbody
			-> substi old new
				<{if test then tbody else fbody}>
				<{if newtest then newtbody else newfbody}>
.
Hint Constructors substi: core.

Ltac destruct_if :=
	crush; match goal with
		| [ |- context[if ?X then _ else _] ] => destruct X
	end; crush.

Theorem substi_correct: forall old new before after,
	<{ [old:=new]before }> = after <-> substi old new before after.
Proof.
	intros. split; generalize after.
	induction before; destruct_if.
	induction 1; destruct_if.
Qed.


Reserved Notation "t '-->' t'" (at level 40).
Inductive step: tm -> tm -> Prop :=
	| ST_AppAbs: forall x T2 t1 v2,
			value v2
			-> <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
	| ST_App1: forall t1 t1' t2,
			t1 --> t1' ->
			<{t1 t2}> --> <{t1' t2}>
	| ST_App2: forall v1 t2 t2',
			value v1
			-> t2 --> t2'
			-> <{ v1 t2}> --> <{v1 t2'}>
	| ST_IfTrue: forall t1 t2,
			<{if true then t1 else t2}> --> t1
	| ST_IfFalse: forall t1 t2,
			<{if false then t1 else t2}> --> t2
	| ST_If: forall t1 t1' t2 t3,
			t1 --> t1'
			-> <{ if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').

Definition relation (X: Type) := X -> X -> Prop.
Inductive multi {X: Type} (R: relation X): relation X :=
	| multi_refl: forall (x: X), multi R x x
	| multi_step: forall (x y z: X),
			R x y
			-> multi R y z
			-> multi R x z.

Hint Constructors step: core.
Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Tactic Notation "print_goal" :=
	match goal with |- ?x => idtac x end.
Tactic Notation "normalize" :=
	repeat (
		print_goal; eapply multi_step;
		[ (eauto 10; fail) | (instantiate; simpl)]
	);
	apply multi_refl.

Lemma step_example1':
	<{idBB idB}> -->* idB.
Proof. normalize. Qed.

Definition context := partial_map ty.

(*Reserved Notation "ctx '--' t '>>>' T" (at level 101, t custom stlc, T custom stlc at level 0).*)
Inductive has_type: context -> tm -> ty -> Prop :=
  | T_Var: forall ctx x T1,
      ctx x = Some T1 ->
      ctx -- x >>> T1
  | T_Abs: forall ctx x T1 T2 t1,
      (update ctx x T2) -- t1 >>> T1 ->
      ctx -- \x:T2, t1 >>> (T2 -> T1)
  | T_App: forall T1 T2 ctx t1 t2,
      ctx -- t1 >>> (T2 -> T1) ->
      ctx -- t2 >>> T2 ->
      ctx -- t1 t2 >>> T1
  | T_True: forall ctx,
       ctx -- true >>> Bool
  | T_False: forall ctx,
       ctx -- false >>> Bool
  | T_If: forall t1 t2 t3 T1 ctx,
       ctx -- t1 >>> Bool ->
       ctx -- t2 >>> T1 ->
       ctx -- t3 >>> T1 ->
       ctx -- if t1 then t2 else t3 >>> T1

where "ctx '--' t '>>>' T" := (has_type ctx t T).
Hint Constructors has_type: core.

Example typing_example_1:
	typed empty <{\x:Bool, x}> (Bool -> Bool)
Proof. auto. Qed.
