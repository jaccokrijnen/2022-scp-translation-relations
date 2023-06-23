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

Inductive dead_syn : Term -> Term -> Prop :=
  | dc_cong : forall t t',
      Compat dead_syn t t' ->
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
      (∀ b, In b bs ->
        name_removed b bs' -> pure_binding [] b
      ) ->

      (* Any resulting binding has a (related) binding in the original group *)
      (∀ b', In b' bs' ->
         ∃ b, In b bs /\
           name_Binding b = name_Binding b' /\
           dead_syn_binding b b'
      ) ->
      dead_syn_bindings bs bs'


with dead_syn_binding : Binding -> Binding -> Prop :=

  | dc_term_bind_cong : forall s vd t t',
      dead_syn t t' ->
      dead_syn_binding (TermBind s vd t) (TermBind s vd t')

  | dc_binding : forall b,
      dead_syn_binding b b
  .

Definition dead_code t t' := dead_syn t t' /\ unique t /\ closed t'.
