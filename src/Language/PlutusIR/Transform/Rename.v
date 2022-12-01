From Coq Require Import
  String
  Lists.List
  .
From PlutusCert Require Import
  Util
  Util.List
  Transform.Congruence
  Analysis.FreeVars
  AFI
  .
From PlutusCert Require
  Language.PlutusIR
  .

Import PlutusIR (term(..), tvdecl(..), vdecl(..), ty(..), dtdecl(..), binding(..), constr(..), Recursivity(..)).
Import PlutusIR.NamedTerm.
Import ListNotations.
Import AFI.

(* Rename context*)
Definition ctx := list (string * string).


(* Binding variable x does not capture free variables in (the pre-term) t if they were renamed
   according to Γ *)
Definition no_capture x (Γ : ctx) t :=
  forall y, In (y, x) Γ -> ~ AFI.Term.appears_free_in y t.

Definition no_captureA α (Δ : ctx) t :=
  forall β, In (β, α) Δ -> ~ AFI.Annotation.appears_free_in β t.

Definition no_ty_capture α (Δ : ctx) τ :=
  forall β, In (β, α) Δ -> ~ AFI.Ty.appears_free_in β τ.


Inductive rename_tvs (Δ : ctx) (cs : list constructor) : list TVDecl -> list TVDecl -> ctx -> Type :=

  | rn_tvs_nil :
      rename_tvs Δ cs [] [] []

  | rn_tvs_cons : forall α tvs k β tvs' Δ_tvs,
      (* check that the bound tyvar does not capture other renamed vars in the
         type signatures of the constructors *)
      Forall (fun '(Constructor (VarDecl _ cty) _) => no_ty_capture β Δ cty) cs ->
      rename_tvs ((α, β) :: Δ) cs tvs tvs' Δ_tvs ->
      rename_tvs Δ cs (TyVarDecl α k :: tvs) (TyVarDecl β k :: tvs') ((α, β) :: Δ_tvs)
.

Inductive rename_ty (Δ : ctx) : Ty -> Ty -> Type :=

   | rn_Ty_Var : forall α α',
      lookup α Δ = Some α' ->
      rename_ty Δ (Ty_Var α) (Ty_Var α')

   | rn_Ty_Fun : forall σ τ σ' τ',
      rename_ty Δ σ σ' ->
      rename_ty Δ τ τ' ->
      rename_ty Δ (Ty_Fun σ τ) (Ty_Fun σ' τ')

   | rn_Ty_IFix : forall σ τ σ' τ',
      rename_ty Δ σ σ' ->
      rename_ty Δ τ τ' ->
      rename_ty Δ (Ty_IFix σ τ) (Ty_IFix σ' τ')

   | rn_Ty_Forall : forall α α' k τ τ',
      rename_ty ((α, α') :: Δ) τ τ' ->
      no_ty_capture α Δ τ ->
      rename_ty Δ (Ty_Forall α k τ) (Ty_Forall α' k τ')

   | rn_Ty_Builtin : forall t,
      rename_ty Δ (Ty_Builtin t) (Ty_Builtin t)

   | rn_Ty_Lam : forall α α' k τ τ',
      rename_ty ((α, α') :: Δ) τ τ' ->
      no_ty_capture α Δ τ ->
      rename_ty Δ (Ty_Lam α k τ) (Ty_Lam α' k τ')

   | Ty_App : forall σ τ σ' τ',
      rename_ty Δ σ σ' ->
      rename_ty Δ τ τ' ->
      rename_ty Δ (Ty_App σ τ) (Ty_App σ' τ')
.

Inductive rename (Γ Δ : ctx) : Term -> Term -> Type :=
  | rn_Var : forall x y,
      lookup x Γ = Some y ->
      rename Γ Δ  (Var x) (Var y)

  | rn_Let_Rec : forall bs bs' t t',
      forall Γ_bs Δ_bs,
      rename_Bindings_Rec (Γ_bs ++ Γ) (Δ_bs ++ Δ) Γ_bs Δ_bs bs bs' ->
      rename (Γ_bs ++ Γ) (Δ_bs ++ Δ) t t' ->

      (* All bound type- and term variables in the bindings should not capture _in the body_.

         Alternatively, this could have been implemented by adding `Let NonRec bs t` as 
         an index in rename_binding and putting a simple no_capture at the actual binding *)
      Forall (fun '(_, x') => no_capture x' Γ t) Γ_bs ->
      Forall (fun '(_, α') => no_captureA α' Δ t) Δ_bs ->

      (* All bound (type) variables have to be unique in the binding group *)
      NoDup (bvbs bs') ->
      NoDup (btvbs bs') ->

      rename Γ Δ (Let Rec bs t) (Let Rec bs' t')

  (* If the decision procedure becomes problematic because of not structurally smaller terms,
     these two rules should be refactored into a relation similar to rename_Bindings_Rec *)
  | rn_Let_NonRec_nil : forall t t',
      rename Γ Δ t t' ->
      rename Γ Δ (Let NonRec [] t) (Let NonRec [] t')

  | rn_Let_NonRec_cons : forall Γ_b Δ_b b b' bs bs' t t',
      rename_binding Γ Δ Γ_b Δ_b b b' ->
      rename (Γ_b ++ Γ) (Δ_b ++ Δ) (Let NonRec bs t) (Let NonRec bs' t') ->

      (* All bound (type) variables in the let should not capture.

         Alternatively, add `Let NonRec bs t` as index in rename_binding 
         and put a simple no_capture at the actual binding *)
      Forall (fun '(_, x') => no_capture x' Γ (Let NonRec bs t)) Γ_b ->
      Forall (fun '(_, α') => no_captureA α' Δ (Let NonRec bs t)) Δ_b ->

      rename Γ Δ (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t')

  | rn_TyAbs : forall α α' k t t',
      rename ((α, α') :: Γ) Δ t t' ->
      no_captureA α' Δ t ->
      rename Γ Δ (TyAbs α k t) (TyAbs α' k t')

  | rn_LamAbs : forall x x' τ τ' t t',
      rename_ty Δ τ τ' ->
      rename ((x, x') :: Γ) Δ t t' ->
      no_capture x' Δ t ->
      rename Γ Δ (LamAbs x τ t) (LamAbs x' τ' t')

  | rn_Apply : forall s t s' t',
      rename Γ Δ s s' ->
      rename Γ Δ t t' ->
      rename Γ Δ (Apply s t) (Apply s' t')

  | rn_Constant : forall c,
      rename Γ Δ (Constant c) (Constant c)

  | rn_Builtin : forall b,
      rename Γ Δ (Builtin b) (Builtin b)

  | rn_TyInst : forall t t' τ τ',
      rename Γ Δ t t' ->
      rename_ty Δ τ τ' ->
      rename Γ Δ (TyInst t τ) (TyInst t' τ')

  | rn_Error : forall τ τ',
      rename_ty Δ τ τ' ->
      rename Γ Δ (Error τ) (Error τ')

  | rn_IWrap σ τ σ' τ' t t':
      rename_ty Δ σ σ' ->
      rename_ty Δ τ τ' ->
      rename Γ Δ t t' ->
      rename Γ Δ (IWrap σ τ t) (IWrap σ' τ' t')

  | rn_Unwrap : forall t t',
      rename Γ Δ t t' ->
      rename Γ Δ (Unwrap t) (Unwrap t')

with rename_binding (Γ Δ : ctx) : ctx -> ctx -> Binding -> Binding -> Type :=

  | rn_TermBind : forall s x x' τ τ' t t',
      rename_ty Δ τ τ' ->
      rename Γ Δ t t' ->
      rename_binding Γ Δ [(x, x')] [] (TermBind s (VarDecl x τ) t) (TermBind s (VarDecl x' τ') t')

  | rn_TypeBind : forall α α' k τ τ',
      rename_ty Δ τ τ' ->
      rename_binding Γ Δ [] [(α, α')] (TypeBind (TyVarDecl α k) τ) (TypeBind (TyVarDecl α' k) τ')

  | rn_DatatypeBind : forall α α' k tvs tvs' elim elim' cs cs',
      forall Δ_tvs Γ_cs Γ_b Δ_b,

      (* Renamings of bound ty-vars, which may be used in constructor types *)
      rename_tvs Δ cs' tvs tvs' Δ_tvs ->
      (* Constructor types are renamed and return any renamed constructor names *)
      rename_constrs ((α, α') :: Δ_tvs ++ Δ) Γ cs cs' Γ_cs ->

      (* Renamings for the rest of the program *)
      Γ_b = (elim, elim') :: Γ_cs ->
      Δ_b = [(α, α')] ->


      rename_binding Γ Δ Γ_b Δ_b
        (DatatypeBind (Datatype (TyVarDecl α k) tvs elim cs))
        (DatatypeBind (Datatype (TyVarDecl α' k) tvs' elim' cs'))

(*
  rename_Bindings_Rec is also indexed over contexts Γ_bs, Δ_bs, which are respectively
  the bound term and type variables of the recursive bindings.
*)
with rename_Bindings_Rec (Γ Δ : ctx) : ctx -> ctx -> list Binding -> list Binding -> Type :=

  | rn_Bindings_Rec_nil :
      rename_Bindings_Rec Γ Δ [] [] [] []

  | rn_Bindings_Rec_cons : forall b b' bs bs',
      forall Γ_b Γ_bs Δ_b Δ_bs,
      rename_binding Γ Δ Γ_b Δ_b b b' ->
      rename_Bindings_Rec Γ Δ Γ_bs Δ_bs bs bs' ->
      rename_Bindings_Rec Γ Δ (Γ_b ++ Γ_bs) (Δ_b ++ Δ_bs) (b :: bs) (b' :: bs')

(*
  rename_constrs is also indexed over context Γ_cs, which are
  the renamings of the constructors
*)
with rename_constrs (Γ Δ : ctx) : list constructor -> list constructor -> ctx -> Type :=

  | rn_constrs_nil :
      rename_constrs Γ Δ [] [] []

  | rn_constrs_cons : forall x x' τ τ' n cs cs' Γ_cs,
      rename_ty Δ τ τ' ->
      rename_constrs Γ Δ cs cs' Γ_cs ->
      rename_constrs Γ Δ
        (Constructor (VarDecl x τ) n :: cs)
        (Constructor (VarDecl x' τ') n :: cs')
        ((x, x') :: Γ_cs)
  .


(* MetaCoq Run (run_print_rules rename). *)
