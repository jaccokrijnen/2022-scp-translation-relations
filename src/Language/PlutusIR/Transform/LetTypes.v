From PlutusCert Require Import Language.PlutusIR.
From PlutusCert Require Import Language.PlutusIR.Transform.Congruence.
From PlutusCert Require Import Language.PlutusIR.Analysis.FreeVars.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Import Coq.Lists.List.ListNotations.

Import NamedTerm.

(* TODO: Combine this with LetNonRec 
   currently desugares only a let-nonrec with only type bindings
*)

Inductive ty_let : Term -> Term -> Type :=

  | tl_Let : forall bs t_body t_body' f_bs,
      ty_let t_body t_body' ->
      ty_let_Bindings bs f_bs ->
      ty_let (Let NonRec bs t_body) (fold_right apply t_body' f_bs )

  | tl_Cong : forall t t',
      Cong ty_let t t' ->
      ty_let t t'


with ty_let_Bindings : list Binding -> list (Term -> Term) -> Type :=

  | tl_Nil  :
      ty_let_Bindings nil nil

  | tl_Cons : forall {b bs f_b f_bs},
      ty_let_Binding        b   f_b ->
      ty_let_Bindings       bs  f_bs ->
      ty_let_Bindings (b :: bs) (f_b :: f_bs)

with ty_let_Binding : Binding -> (Term -> Term) -> Type :=
  | tl_Desugar : forall α k τ,
      ty_let_Binding
        (TypeBind (TyVarDecl α k) τ)
        (fun t_bs => TyInst (TyAbs α k t_bs) τ)
  .
