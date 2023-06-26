From PlutusCert Require Import
  PlutusIR
  Util
  Compat
  .
Import NamedTerm.

From Coq Require Import
  Lists.List
  Strings.String.
Import ListNotations.


Inductive lams : Term -> list Term -> list Binding -> Term -> Prop :=

  | Lams_1 : forall t vdecls v ty t_inner arg args,
      lams              t          args                                         vdecls  t_inner ->
      lams (LamAbs v ty t) (arg :: args) (TermBind Strict (VarDecl v ty) arg :: vdecls) t_inner

  | Lams_2 : forall t args,
  (* ~ (exists v ty t', t = LamAbs v ty t') -> *) (* enforces the longest sequence of lambda binders *)
      lams t args [] t
.

(* accumulating param *)
Inductive betas  : Term -> list Term -> list Binding -> Term -> Prop :=

  | Betas_1 : forall s t args bs t_inner,
      betas        s    (t :: args) bs t_inner ->
      betas (Apply s t)       args  bs t_inner

  | Betas_2 : forall t args bs t_inner,
  (* ~ (exists t_f t_x, t = Apply t_f t_x) -> *) (* enforces the longest sequence of arguments *)
      lams t args bs t_inner ->
      betas t args bs t_inner
.


Inductive beta : Term -> Term -> Prop :=

  | beta_multi : forall t bs bs' t_inner t_inner',
      betas t [] bs t_inner ->
      Compat_Bindings beta bs bs' ->
      beta t_inner t_inner' ->
      beta t (mk_let NonRec bs t_inner')

  | beta_TyInst_TyAbs : forall ty v k t_body,
      beta
        (TyInst (TyAbs v k t_body) ty)
        (Let NonRec [TypeBind (TyVarDecl v k) ty] t_body)

  | beta_Compat : forall t1 t2,
      Compat beta t1 t2 ->
      beta t1 t2
.
