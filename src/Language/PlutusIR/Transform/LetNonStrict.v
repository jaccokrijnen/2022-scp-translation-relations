From Coq Require Import
  List
  String.
From PlutusCert Require
  Language.PlutusIR
.

Import PlutusIR (term(..), tvdecl(..), vdecl(..), ty(..), 
  dtdecl(..), binding(..), constr(..), Recursivity(..), DefaultUni(..),
  kind(..), Strictness(..)).

From PlutusCert Require Import
  Util.List
  Analysis.BoundVars
.
Import ListNotations.
Import PlutusIR.NamedTerm.


(*
There are two ways the compiler may thunk:

  t ===> (λu. t) ()
  t ===> (Λa. t) (∀a. a)

*)
Inductive thunk_style :=
  | thunk_Unit
  | thunk_Forall
  .

(* Record for each variable if they were thunked at their binding site *)
Definition ctx := list (string * option thunk_style).

Definition Ty_Unit : Ty :=
  Ty_Builtin (PlutusIR.Some (@PlutusIR.TypeIn DefaultUniUnit)).

Definition t_unit : Term :=
  Constant (PlutusIR.Some (PlutusIR.ValueOf DefaultUniUnit tt)).

Inductive let_non_strict (Γ : ctx) : Term -> Term -> Type :=

  (* If the decision procedure becomes problematic because of not structurally smaller terms,
     these two rules should be refactored into a relation similar to rename_Bindings_Rec *)
  | lns_Let_NonRec_nil : forall t t',
      let_non_strict Γ t t' ->
      let_non_strict Γ (Let NonRec [] t) (Let NonRec [] t')

  | lns_Let_NonRec_cons : forall b bs b' bs' t t' Γ_b,
      let_non_strict Γ t t' ->
      let_non_strict_binding Γ b b' Γ_b ->
      let_non_strict (Γ_b ++ Γ) (Let NonRec bs t) (Let NonRec bs' t') ->
      let_non_strict Γ (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t')

  | lns_Let_Rec : forall bs bs' t t' Γ_bs,
      let_non_strict_Bindings_Rec (Γ_bs ++ Γ) bs bs' Γ_bs ->
      let_non_strict (Γ_bs ++ Γ) t t' ->
      let_non_strict Γ (Let Rec bs t) (Let Rec bs' t')

  | lns_Var_Unit : forall x t,
      lookup x Γ = Some (Some thunk_Unit) ->
      let_non_strict Γ (Var x) (Apply t t_unit)

  | lns_Var_force_Forall : forall x t α,
      lookup x Γ = Some (Some thunk_Forall) ->
      let_non_strict Γ (Var x) (TyInst t (Ty_Forall α Kind_Base (Ty_Var α)))

  | lns_Var_unit : forall x,
      lookup x Γ = Some (Some thunk_Unit) ->
      let_non_strict Γ (Var x) (Apply (Var x) t_unit)

  | lns_TyAbs : forall α k t t',
      let_non_strict Γ t t' ->
      let_non_strict Γ (TyAbs α k t) (TyAbs α k t')

  | lns_LamAbs   : forall x τ t t',
      let_non_strict Γ t t' ->
      let_non_strict Γ (LamAbs x τ t) (LamAbs x τ t')

  | lns_Apply    : forall s s' t t',
      let_non_strict Γ s s' ->
      let_non_strict Γ t t' ->
      let_non_strict Γ (Apply s t) (Apply s' t')

  | lns_Constant : forall c,
      let_non_strict Γ (Constant c) (Constant c)

  | lns_Builtin : forall b,
      let_non_strict Γ (Builtin b) (Builtin b)

  | lns_TyInst : forall t t' τ,
      let_non_strict Γ t t' ->
      let_non_strict Γ (TyInst t τ) (TyInst t' τ)

  | lns_Error : forall τ,
      let_non_strict Γ (Error τ) (Error τ)

  | lns_IWrap : forall σ τ t t',
      let_non_strict Γ t t' ->
      let_non_strict Γ (IWrap σ τ t) (IWrap σ τ t')

  | lns_Unwrap : forall t t',
      let_non_strict Γ t t' ->
      let_non_strict Γ (Unwrap t) (Unwrap t')

with let_non_strict_binding (Γ : ctx) : Binding -> Binding -> ctx -> Type :=

  | lns_TermBind_thunk_Unit : forall x τ τ' t t' y,
      let_non_strict Γ t t' ->
      τ' = Ty_Fun Ty_Unit τ ->
      let_non_strict_binding Γ
        (TermBind NonStrict (VarDecl x τ ) t                    )
        (TermBind Strict    (VarDecl x τ') (LamAbs y Ty_Unit t'))
        [(x, Some thunk_Unit)]

  | lns_TermBind_thunk_Forall : forall x τ τ' t t' α,
      let_non_strict Γ t t' ->
      τ' = Ty_Forall α Kind_Base τ ->
      let_non_strict_binding Γ
        (TermBind NonStrict (VarDecl x τ )  t                    )
        (TermBind Strict    (VarDecl x τ') (TyAbs α Kind_Base t'))
        [(x, Some thunk_Forall)]

  | lns_TermBind_cong : forall x τ s t t',
      let_non_strict Γ t t' ->
      let_non_strict_binding Γ
        (TermBind s (VarDecl x τ) t)
        (TermBind s (VarDecl x τ) t')
        [(x, None)]

  | lns_TypeBind : forall tvd ty,
      let_non_strict_binding Γ (TypeBind tvd ty) (TypeBind tvd ty) []

  | lns_DatatypeBind : forall d,
      let_non_strict_binding Γ (DatatypeBind d) (DatatypeBind d)
        (map (fun v => (v, None)) (bvb (DatatypeBind d)))

with let_non_strict_Bindings_Rec (Γ : ctx) : list Binding -> list Binding -> ctx -> Type :=

  | lns_Bindings_Rec_nil :
      let_non_strict_Bindings_Rec Γ [] [] []

  | lns_Bindings_Rec_cons : forall b b' bs bs',
      forall Γ_b Γ_bs,
      let_non_strict_binding Γ b b' Γ_b ->
      let_non_strict_Bindings_Rec Γ bs bs' Γ_bs ->
      let_non_strict_Bindings_Rec Γ (b :: bs) (b' :: bs') (Γ_b ++ Γ_bs)
.
