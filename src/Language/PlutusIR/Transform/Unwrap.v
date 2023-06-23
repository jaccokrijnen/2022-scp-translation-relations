From PlutusCert Require Import
  PlutusIR
  Transform.Compat
.

Import NamedTerm.

Inductive unwrap_cancel : Term -> Term -> Prop :=

  | uc_cancel : forall ty1 ty2 t t',
      unwrap_cancel t t' ->
      unwrap_cancel (Unwrap (IWrap ty1 ty2 t)) t'

  | uc_cong : forall t t',
      Compat unwrap_cancel t t' ->
      unwrap_cancel t t'

  .
