From Coq Require Import
  Strings.String
  Lists.List
  Utf8_core
  .

From PlutusCert Require Import
  Util
  Util.List
  Language.PlutusIR
  Language.PlutusIR.Analysis.FreeVars
  Language.PlutusIR.Analysis.Purity
  Language.PlutusIR.Analysis.WellScoped
  Language.PlutusIR.Analysis.UniqueBinders
  Language.PlutusIR.Transform.Compat
  .

Import NamedTerm.
Import UniqueBinders.Term.
Import ListNotations.

Set Implicit Arguments.


Notation fv := (free_vars String.eqb).
Notation fv_binding := (free_vars_binding String.eqb).
Notation fv_bindings := (free_vars_bindings String.eqb fv_binding).

Definition name_Binding (b : Binding) :=
  match b with
    | TermBind s (VarDecl x _) t => x
    | TypeBind (TyVarDecl x _) ty => x
    | DatatypeBind (Datatype (TyVarDecl x _) _ _ _) => x
  end.

Definition name_removed b bs : Prop :=
  ¬ (In (name_Binding b) (map name_Binding bs)).

Inductive elim : Term -> Term -> Prop :=
  | elim_cong : forall t t',
      Compat elim t t' ->
      elim t t'

  | elim_delete_let : forall rec bs t t',
      elim t t' ->
      Forall (pure_binding []) bs ->
      elim (Let rec bs t) t'

  | elim_delete_bindings : forall rec bs bs' t t',
      elim t t' ->
      elim_bindings bs bs' ->
      elim (Let rec bs t) (Let rec bs' t')


with elim_bindings : list Binding -> list Binding -> Prop :=
  | elim_bindings : forall bs bs' bsn bs'n,
      bsn = map name_Binding bs ->
      bs'n = map name_Binding bs' ->

      (* any removed binding is a pure binding *)
      (∀ b, In b bs ->
        name_removed b bs' -> pure_binding [] b
      ) ->

      (* Any resulting binding has a (related) binding in the original group *)
      (∀ b', In b' bs' ->
         ∃ b, In b bs /\
           name_Binding b = name_Binding b' /\
           elim_binding b b'
      ) ->
      elim_bindings bs bs'


with elim_binding : Binding -> Binding -> Prop :=

  | elim_term_bind_cong : forall s vd t t',
      elim t t' ->
      elim_binding (TermBind s vd t) (TermBind s vd t')

  | elim_binding : forall b,
      elim_binding b b
  .

Definition dead_code t t' := elim t t' /\ unique t /\ closed t'.
