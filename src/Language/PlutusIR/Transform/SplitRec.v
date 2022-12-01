From PlutusCert Require Import
  PlutusIR
  Analysis.FreeVars
  Analysis.Equality
  Analysis.UniqueBinders
  Analysis.WellScoped
  Transform.Congruence
  .
Import NamedTerm.
Import Term.

From Coq Require Import
  Strings.String
  Lists.List
  Lists.ListSet
  .
Import ListNotations.

(* A binding group (Let without a body) *)
Definition binding_group := (Recursivity * list Binding)%type.

(*
Assuming globally unique variables, the new binding groups much satisfy:
  - Well-scoped: each free variable in a binding RHS is bound
  - All bindings equals those in the let-rec before transformaton

Note that strictness of bindings does not matter: if one of the (strict)
bindings diverges, the whole let-block diverges. This behaviour remains when
regrouping/reordering all bindings.
*)

Definition list_eq_elems {A} xs ys : Prop :=
  forall (x : A), In x xs <-> In x ys.


Definition min_Rec (r1 r2 : Recursivity) : Recursivity :=
  match r1, r2 with
    | NonRec, NonRec => NonRec
    | _ , _ => Rec
  end.

(* Collect subsequent binding groups, together with the "inner" term and
   minimum recursivity *)
Inductive outer_binds : Term -> list Binding -> Term -> Recursivity -> Prop :=

  | cv_Let : forall t_body lets t_inner r bs r_body,
      outer_binds t_body lets t_inner r_body ->
      outer_binds (Let r bs t_body) (bs ++ lets) t_inner (min_Rec r_body r)

  | cv_Other : forall t_inner,
      outer_binds t_inner [] t_inner NonRec

  .

Inductive split_syn : Term -> Term -> Prop :=
  | split_rec_let : forall bs t_body t bgs t_inner min_rec,

      (* a decision-procedure would need to find the list bgs of binding groups that
         satisfies the second premise (needs to do backtracking) *)
      outer_binds t bgs t_inner min_rec ->
      list_eq_elems bs bgs ->
      split_syn t_body t_inner ->
      split_syn (Let Rec bs t_body) t

  | split_rec_cong : forall t t',
      Cong split_syn t t' ->
      split_syn t t'
.

Definition split_rec t t' :=
  split_syn t t' /\
  unique t /\
  closed t'
.


Definition outer_binds_dec
     : Term -> list binding_group * Term.
Admitted.
