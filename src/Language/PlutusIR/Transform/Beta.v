From PlutusCert Require Import
  PlutusIR
  Util
  Congruence
  .
Import NamedTerm.

From Coq Require Import
  Lists.List
  Strings.String.
Import ListNotations.

(*

This pass transforms beta redexes into let non-recs, so that the later inlining
pass has more opportunities for inlining.

Transforms repeated applications (not just repeated β-redexes), e.g.

         $₃
       /  \
     $₂    t₃
   /  \
  $₁   t₂
/  \                    =>      let nonrec x = t₁
λx t₁                                      y = t₂
|                                          z = t₃
λy                              in t_body
|
λz
|
t_body

*)

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


Goal forall v1 v2 τ1 τ2 t t1 t2,
  betas
    (Apply (Apply (LamAbs v1 τ1 (LamAbs v2 τ2 t)) t1) t2) []
    [TermBind Strict (VarDecl v1 τ1) t1; TermBind Strict (VarDecl v2 τ2) t2] t.
intros.
repeat apply Betas_1.
apply Betas_2.
repeat apply Lams_1.
apply Lams_2.
Qed.

Inductive beta : Term -> Term -> Prop :=

  | beta_multi : forall t bs bs' t_inner t_inner',
      betas t [] bs t_inner ->
      Cong_Bindings beta bs bs' ->
      beta t_inner t_inner' ->
      beta t (mk_let NonRec bs t_inner')

  | beta_TyInst_TyAbs : forall ty v k t_body,
      beta
        (TyInst (TyAbs v k t_body) ty)
        (Let NonRec [TypeBind (TyVarDecl v k) ty] t_body)

  | beta_Cong : forall t1 t2,
      Cong beta t1 t2 ->
      beta t1 t2
.


Definition is_beta : Term -> Term -> bool.
Admitted.

Lemma is_beta_sound : forall t₁ t₂,
  is_beta t₁ t₂ = true -> beta t₁ t₂.
Admitted.
