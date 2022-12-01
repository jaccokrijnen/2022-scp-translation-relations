Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import PeanoNat.

Import ListNotations.
From Equations Require Import Equations.
Require Import Program.
Require Import Lia.

From PlutusCert Require Import
  Util
  Util.List
  Language.PlutusIR
  .

Import NamedTerm.

(*
Inlining considers:

  let nonrec Term bindings
  let Type bindings
  type β-redexes of the form (/\α. t) τ

β-redexes on term-level are handled by the Beta pass.

The plutus compiler will _unconditionally_ inline, meaning that it will inline all occurences
and then remove the remaining dead binding.

We consider the more general case where some occurences may be inlined, but not others. As a consequence,
this pass does not consider binder elimination.

*)

(* Context of all let-bound term variables in scope *)
Inductive binder_info :=
  | bound_term : Term -> binder_info

  (* bound_ty is used for both type lets and type β-redex *)
  | bound_ty : Ty -> binder_info
  .

Definition ctx := list (string * binder_info).

Definition Binding_to_ctx (b : Binding) : ctx :=
  match b with
    | TermBind _ (VarDecl v _) t => [(v, bound_term t)]
    | TypeBind (TyVarDecl α _) τ => [(α, bound_ty τ)]
    | _ => []
  end
.

Definition Bindings_to_ctx (bs : list Binding) : ctx :=
  rev (concat (map Binding_to_ctx bs)).

Local Open Scope list_scope.


(*
TODO: split context in two: type scope and term scope
*)
(*
This relation relates terms where inlining of let-bound variables may
have taken place. Note that the PIR inliner may also remove the let binding
when all of its occurrences have been inlined (dead code). This is not taken into account here.
*)
Inductive inline (Γ : ctx) : Term -> Term -> Prop :=
  | inl_Var_1 : forall v t t',
      Lookup v (bound_term t) Γ ->
      inline Γ t t' ->
      inline Γ (Var v) t'

  | inl_Var_2 : forall v,
      inline Γ (Var v) (Var v)

  | inl_Let_Rec : forall Γ_bs bs bs' t t',
      Γ_bs = Bindings_to_ctx bs ->
      inline_Bindings_Rec (Γ_bs ++ Γ) bs bs' ->
      inline (Γ_bs ++ Γ) t t' ->
      inline Γ (Let Rec bs t) (Let Rec bs' t')

  | inl_Let_NonRec : forall Γ_bs bs bs' t t',
      Γ_bs = Bindings_to_ctx bs ->
      inline_Bindings_NonRec Γ bs bs' ->
      inline (Γ_bs ++ Γ) t t' ->
      inline Γ (Let NonRec bs t) (Let NonRec bs' t')

  | inl_TyInst_beta   : forall t t' α k τ τ',
      inline ((α, bound_ty τ) :: Γ) t t' ->
      inline_Ty Γ τ τ' ->
      inline Γ (TyInst (TyAbs α k t) τ) (TyInst (TyAbs α k t') τ')

  (* Congruence cases *)
  | inl_TyInst_cong   : forall t t' τ τ',
      inline Γ t t' ->
      inline_Ty Γ τ τ' ->
      ~(exists α k t'', t = TyAbs α k t'') -> (* See inl_TyInst_beta *)
      inline Γ (TyInst t τ) (TyInst t' τ')
  | inl_TyAbs    : forall α k t t',
      inline Γ t t' ->
      inline Γ (TyAbs α k t) (TyAbs α k t')
  | inl_LamAbs   : forall x τ τ' t t',
      inline Γ t t' ->
      inline_Ty Γ τ τ' ->
      inline Γ (LamAbs x τ t) (LamAbs x τ' t')
  | inl_Apply    : forall s s' t t',
      inline Γ s s' ->
      inline Γ t t' ->
      inline Γ (Apply s t) (Apply s' t')
  | inl_Constant : forall c,
      inline Γ (Constant c) (Constant c)
  | inl_Builtin  : forall f,
      inline Γ (Builtin f) (Builtin f)
  | inl_Error    : forall τ τ',
      inline Γ (Error τ) (Error τ')
  | inl_IWrap    : forall σ σ' τ τ' t t',
      inline_Ty Γ τ τ' ->
      inline_Ty Γ σ σ' ->
      inline Γ (IWrap σ τ t) (IWrap σ' τ' t')
  | inl_Unwrap   : forall t t',
      inline Γ (Unwrap t) (Unwrap t')

  with inline_Bindings_Rec (Γ : ctx) : list Binding -> list Binding -> Prop :=

    | inl_Binding_Rec_cons : forall b b' bs bs',
        inline_Binding Γ b b' ->
        inline_Bindings_Rec Γ bs bs' ->
        inline_Bindings_Rec Γ (b :: bs) (b' :: bs')

    | inl_Binding_Rec_nil  :  inline_Bindings_Rec Γ [] []

  with inline_Bindings_NonRec (Γ : ctx) : list Binding -> list Binding -> Prop :=

    | inl_Binding_NonRec_cons : forall b b' bs bs',
        inline_Binding Γ b b' ->
        inline_Bindings_NonRec (Binding_to_ctx b ++ Γ) bs bs' ->
        inline_Bindings_NonRec Γ (b :: bs) (b' :: bs')

    | inl_Binding_NonRec_nil  : inline_Bindings_NonRec Γ [] []


  with inline_Binding (Γ : ctx) : Binding -> Binding -> Prop :=

  | inl_TermBind  : forall s x τ τ' t t',
      inline Γ t t' ->
      inline_Ty Γ τ τ' ->
      inline_Binding Γ (TermBind s (VarDecl x τ) t) (TermBind s (VarDecl x τ') t')

  | inl_DatatypeBind_NonRec : forall d,
      inline_Binding Γ (DatatypeBind d) (DatatypeBind d)

  | inl_TypeBind_NonRec : forall tvd τ τ',
      inline_Ty Γ τ τ' ->
      inline_Binding Γ (TypeBind tvd τ) (TypeBind tvd τ')

  with inline_Ty (Γ : ctx) : Ty -> Ty -> Prop :=

   | inl_Ty_Var_1 : forall α τ τ',
      Lookup α (bound_ty τ) Γ ->
      inline_Ty Γ τ τ' ->
      inline_Ty Γ (Ty_Var α) τ

   | inl_Ty_Var_2 : forall α τ τ',
      Lookup α (bound_ty τ) Γ ->
      inline_Ty Γ τ τ' ->
      inline_Ty Γ (Ty_Var α) (Ty_Var α)

   | inl_Ty_Fun : forall σ τ σ' τ',
      inline_Ty Γ σ σ' ->
      inline_Ty Γ τ τ' ->
      inline_Ty Γ (Ty_Fun σ τ) (Ty_Fun σ' τ')

   | inl_Ty_IFix : forall σ τ σ' τ',
      inline_Ty Γ σ σ' ->
      inline_Ty Γ τ τ' ->
      inline_Ty Γ (Ty_IFix σ τ) (Ty_IFix σ' τ')

   | inl_Ty_Forall : forall α k τ τ',
      inline_Ty Γ τ τ' ->
      inline_Ty Γ (Ty_Forall α k τ) (Ty_Forall α k τ')

   | inl_Ty_Builtin : forall t,
      inline_Ty Γ (Ty_Builtin t) (Ty_Builtin t)

   | inl_Ty_Lam : forall α k τ τ',
      inline_Ty Γ τ τ' ->
      inline_Ty Γ (Ty_Lam α k τ) (Ty_Lam α k τ')

   | Ty_App : forall σ τ σ' τ',
      inline_Ty Γ σ σ' ->
      inline_Ty Γ τ τ' ->
      inline_Ty Γ (Ty_App σ τ) (Ty_App σ' τ')

   .
