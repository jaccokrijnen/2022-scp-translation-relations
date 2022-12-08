From Coq Require Import
  Strings.String
  Lists.List.

From Equations Require Import Equations.

From PlutusCert Require Import
  Util
  Util.List
  Language.PlutusIR
  Language.PlutusIR.Analysis.FreeVars
  Language.PlutusIR.Analysis.Purity
  Language.PlutusIR.Analysis.WellScoped
  Language.PlutusIR.Analysis.UniqueBinders
  Language.PlutusIR.Transform.Congruence
  .

Import NamedTerm.
Import UniqueBinders.Term.
Import ListNotations.

Set Implicit Arguments.
Set Equations Transparent.


Notation fv := (free_vars String.eqb).
Notation fv_binding := (free_vars_binding String.eqb).
Notation fv_bindings := (free_vars_bindings String.eqb fv_binding).

Definition name_Binding (b : Binding) :=
  match b with
    | TermBind s (VarDecl x _) t => x
    | TypeBind (TyVarDecl x _) ty => x
    | DatatypeBind (Datatype (TyVarDecl x _) _ _ _) => x
  end.

Inductive dead_syn : Term -> Term -> Prop :=
  | dc_cong : forall t t',
      Cong dead_syn t t' ->
      dead_syn t t'

  | dc_delete_let : forall rec bs t t',
      dead_syn t t' ->
      Forall (pure_binding []) bs ->
      dead_syn (Let rec bs t) t'

  | dc_delete_bindings : forall rec bs bs' t t',
      dead_syn t t' ->
      dead_syn_bindings bs bs' ->
      dead_syn (Let rec bs t) (Let rec bs' t')


with dead_syn_bindings : list Binding -> list Binding -> Prop :=
  | dc_bindings : forall bs bs' bsn bs'n,
      bsn = map name_Binding bs ->
      bs'n = map name_Binding bs' ->

      (* any removed binding is a pure binding *)
      forall b bn, bn = name_Binding b -> 
        ((In bn bsn /\ ~In bn bs'n) -> pure_binding [] b) ->
      (* Any resulting binding has a (related) binding in the original group *)
      forall b' b'n, b'n = name_Binding b' ->
        (In b'n bs'n -> exists b, forall bn, bn = name_Binding b ->
           dead_syn_binding b b' /\ In bn bsn) ->
      dead_syn_bindings bs bs'

with dead_syn_binding : Binding -> Binding -> Prop :=

  | dc_term_bind_cong : forall s vd t t',
      dead_syn t t' ->
      dead_syn_binding (TermBind s vd t) (TermBind s vd t')

  | dc_binding : forall b,
      dead_syn_binding b b
  .

Definition dead_code t t' := dead_syn t t' /\ unique t /\ closed t'.
