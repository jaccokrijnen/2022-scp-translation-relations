From Coq Require Import
  Lists.List
  Strings.String.
From PlutusCert Require Import
  Language.PlutusIR
  .
Import NamedTerm.
Import ListNotations.
Open Scope string_scope.


Fixpoint lams (binds : list VDecl) (body : Term) : Term :=
  fold_right (fun '(VarDecl x τ) t => LamAbs x τ t) body binds.

Definition FuncTy : Type := Ty * Ty.
Definition FuncDef : Type := string * FuncTy * Term .

Inductive Binding_Term_def : Binding -> FuncDef -> Prop :=
  | btb : forall x σ τ t,
      Binding_Term_def (TermBind Strict (VarDecl x (Ty_Fun σ τ)) t) (x, (σ, τ), t)
  .

Inductive Map {A B} (f : A -> B -> Prop) : list A -> list B -> Prop :=

  | tb_nil :
      Map f [] []

  | tb_cons : forall x x' xs xs',
      f x x' ->
      Map f xs xs' ->
      Map f (x :: xs) (x' :: xs')
.


(* WIP

Definition ty_choose : list Term_def -> Ty.
Admitted.

Inductive compile_let_rec : Term -> Term -> Prop :=

  | clr_LetRec : forall bs defs t v_choose,
      Map Binding_Term_def bs defs ->
      compile_let_rec (Let Rec bs t) (LamAbs v_choose (ty_choose defs) t)

.

Definition compile_let_rec (bs : list tb) (t_body : Term) : Term :=
  let n := List.length bs in
  let t_fix := Var "x" in
  let τ_choose := in
  Apply t_fix (LamAbs "choose" )
.

*)
