Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import PeanoNat.

Import ListNotations.
From Equations Require Import Equations.
Require Import Program.
Require Import Lia.


From PlutusCert Require Import
  Util
  Language.PlutusIR
  Language.PlutusIR.Analysis.FreeVars
  Language.PlutusIR.Analysis.BoundVars
  Language.PlutusIR.Transform.Congruence
  Language.PlutusIR.Examples.

(*
Note: [Capture-avoiding substitutions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose

let x = t_x
    y = ... x ... in
    x = t_x'
... y ...

Now when y is inlined, x will be captured by the shadowing definition.

This issue can be avoided when when know properties about the syntax:

1) binders are globally unique
2) or, bindings are never shadowed (variables cannot be captured)

(the former implies the latter)

Note that the (unconditional) inlining may break 1) by duplicating binding sites,
e.g. when inlining a let or lambda.

However, (un)conditional inlining maintains 2) as an invariant
when starting with 1). This implies that renaming is not necessary
for semantics preservation when inlining.

*)


(*
Currently, the inliner only inlines trivial terms.
However, we don't want to use this fact.
*)

Inductive Trivial {name} : term name -> Type :=
  | Trivial_Builtin :  forall f, Trivial (Builtin f)
  | Trivial_Var : forall v, Trivial (Var v)
  | Trivial_Constant : forall c, Trivial (Constant c)
  .

Inductive BoundVar :=
  | LetBound    : Term -> BoundVar
  | LambdaBound :         BoundVar.

Definition Env := list (prod string BoundVar).

(*

Plutus can decide to inline a (non-recursive) binding unconditionally: all its
occurences are inlined and the binding-site is removed.

*)

Inductive Inline (env : Env) : Term -> Term -> Type :=

  (* Recursive bindings are not inlined, so we do not
     store them in the env *)
  | Inl_LetRec : forall t t' bs bs',
      ZipWith (Inline_Binding env (boundVars bs ++ scope)) bs bs' ->
      Inline env (boundVars bs ++ scope) t t' ->
      Inline env scope
        (Let Rec bs  t)
        (Let Rec bs' t')

  | Inl_LetNonRec : forall t t' bs bs',
      Inline_BindingsNonRec env scope bs bs' ->
      Inline (boundTerms bs ++ env) (boundVars bs ++ scope) t t' ->
      Inline env scope
        (Let NonRec bs  t)
        (Let NonRec bs' t')

  | Inl_LamAbs: forall v ty t_body t_body',
      ~ (In v (map fst scope)) ->       (* No shadowing *)
      Inline env scope t_body t_body'  ->
      Inline env scope (LamAbs v ty t_body) (LamAbs v ty t_body')

  | Inl_Var_Inlined : forall v t t',
      In (v, t) env ->
      Inline env scope t t' ->
      Inline env scope (Var v) t'

(* TODO: Add congruence rules for missing term constructors *)

(* let nonrec has linear scoping: every binder comes in scope
   for the next binders
*)
with Inline_BindingsNonRec (env : Env) (scope : Scope) : list Binding -> list Binding -> Type :=

  | Inl_Binding_Term : forall b bs b' bs',
      Inline_Binding  env scope b b' ->
      Inline_BindingsNonRec (boundTerms [b] ++ env) (boundVars [b] ++ scope) bs bs' ->
      Inline_BindingsNonRec env scope (b :: bs) (b' :: bs')

  | Inl_Binding_nil  : Inline_BindingsNonRec env scope nil nil


  (* Recognize inlining in a single binding*)
with Inline_Binding (env : Env) (scope : Scope) : Binding -> Binding -> Type :=

  | Inl_TermBind  : forall r v t t',
      Inline env scope t t' ->
      Inline_Binding env scope
        (TermBind r v t)
        (TermBind r v t')

  | Inl_OtherBind : forall b, Inline_Binding env scope b b.

(* TODO: decision procedure

Use set of unconditionally inlined vars to:
  - Produce intermediate tree OR
  - search procedure for all transformations at once
*)
