From Coq Require Import
  Strings.String
  Lists.List
.

From PlutusCert Require Import
  Language.PlutusIR
  Analysis.BoundVars
  Transform.Congruence
  Util.List
  Analysis.Purity
  .

Import NamedTerm.
Import ListNotations.

(*

Summary
---

Strict Let Rec bindings that don't have a function type will be thunked so that
their type is of function type (unit -> τ). For example polymorphic functions
(∀a ∀b. ...). This is necessary for the compilation step that translates Let Rec
using the indexed fixpoint combinator, which can only handle recursive bindings
with function type.

This pass doesn't actually do thunking, it just changes strict bindings to
non-strict so that the later LetNonStrict pass will thunk them. An additional
(shadowing) strict binder is then added to "strictify" the term again.

In other words, this pass should establish the post-condititon that all LetRec
bindings have function type.

Global uniqueness
---
According to [1], this pass does not preserve global uniquness, because
each thunked recursive binder will have a non-recursive "adapter" binder with
the same name.

[1] plutus-core/plutus-ir/src/PlutusIR/Transform/ThunkRecursions.hs


Possibly implement as function
---

The relation below is more general, because it allows the transformation to be
optionally applied. However, in the compiler, this is not optional, and all
strict letrecs with non-function type are transformed.

We could implement this in coq as a function which should result in a syntactic
equivalent term (there will be no new binder names).

*)



(* Records each binder in the Let Rec that was unstrictified *)


Definition ctx_unstrictified := list (string * (Term * ctx)).

Definition Binding_to_ctx (b : Binding) : ctx :=
  match b with
    | TermBind s (VarDecl x τ) t => [(x, let_bound s)]
    | _ => []
  end
.

Inductive thunk_rec (Γ : ctx) : Term -> Term -> Type :=

  | tr_Let_Rec : forall bs bs' t t' Γ_bs bs_new Ω,
      thunk_rec_Bindings_Rec (Γ_bs ++ Γ) bs bs' Ω ->
      thunk_rec (Γ_bs ++ Γ) t t' ->
      strictify Γ Ω bs_new ->
      thunk_rec Γ (Let Rec bs t) (Let Rec bs' (mk_let NonRec bs_new t'))

  (* Congruence cases, `Cong` cannot currently capture
     this pattern, which has to extend the ctx Γ in all 
     term binders *)
  | tr_Let_NonRec : forall bs bs' t t' Γ_bs,
     thunk_rec_Bindings_NonRec Γ bs bs' Γ_bs ->
     thunk_rec (Γ_bs ++ Γ) t t' ->
     thunk_rec Γ (Let Rec bs t) (Let Rec bs' t')
  | tr_Var      : forall x,
      thunk_rec Γ (Var x) (Var x)
  | tr_TyAbs    : forall α k t t',
      thunk_rec Γ t t' ->
      thunk_rec Γ (TyAbs α k t) (TyAbs α k t')
  | tr_LamAbs   : forall x τ t t',
      thunk_rec ((x, lambda_bound) :: Γ) t t' ->
      thunk_rec Γ (LamAbs x τ t) (LamAbs x τ t')
  | tr_Apply    : forall s s' t t',
      thunk_rec Γ s s' ->
      thunk_rec Γ t t' ->
      thunk_rec Γ (Apply s t) (Apply s' t')
  | tr_Constant : forall c,
      thunk_rec Γ (Constant c) (Constant c)
  | tr_Builtin  : forall f,
      thunk_rec Γ (Builtin f) (Builtin f)
  | tr_TyInst   : forall t t' τ,
      thunk_rec Γ t t' ->
      thunk_rec Γ (TyInst t τ) (TyInst t' τ)
  | tr_Error    : forall τ,
      thunk_rec Γ (Error τ) (Error τ)
  | tr_IWrap    : forall σ τ t t',
      thunk_rec Γ (IWrap σ τ t) (IWrap σ τ t')
  | tr_Unwrap   : forall t t',
      thunk_rec Γ (Unwrap t) (Unwrap t')

with thunk_rec_Bindings_NonRec (Γ : ctx) : list Binding -> list Binding -> ctx -> Type :=

  | tr_Bindings_NonRec_nil :
      thunk_rec_Bindings_NonRec Γ [] [] Γ

  | tr_Bindings_NonRec_cons : forall b b' bs bs',
      forall Γ_b Γ_bs,
        thunk_rec_Binding_NonRec  Γ b b' ->
        thunk_rec_Bindings_NonRec (Binding_to_ctx b ++ Γ) bs bs' Γ_bs ->
        thunk_rec_Bindings_NonRec Γ (b :: bs) (b' :: bs') (Γ_bs ++ Γ_b)


with thunk_rec_Bindings_Rec (Γ : ctx) : list Binding -> list Binding -> ctx_unstrictified -> Type :=

  | tr_Bindings_Rec_nil :
      thunk_rec_Bindings_Rec Γ [] [] []

  | tr_Bindings_Rec_cons : forall b b' bs bs' Ω_b Ω_bs,
      thunk_rec_Binding_Rec Γ b b' Ω_b ->
      thunk_rec_Bindings_Rec Γ bs bs' Ω_bs->
      thunk_rec_Bindings_Rec Γ (b :: bs) (b' :: bs') (Ω_bs ++ Ω_b)

(* Also indexed by the unstrictified bindings *)
with thunk_rec_Binding_NonRec (Γ : ctx) : Binding -> Binding -> Type :=

  | tr_TermBind_NonRec : forall s vd t t',
      thunk_rec Γ t t' ->
      thunk_rec_Binding_NonRec Γ (TermBind s vd t) (TermBind NonStrict vd t')

  | tr_DatatypeBind_NonRec : forall d,
      thunk_rec_Binding_NonRec Γ (DatatypeBind d) (DatatypeBind d)

  | tr_TypeBind_NonRec : forall tvd τ,
      thunk_rec_Binding_NonRec Γ (TypeBind tvd τ) (TypeBind tvd τ)

(* Also indexed by the unstrictified bindings *)
with thunk_rec_Binding_Rec (Γ : ctx) : Binding -> Binding -> ctx_unstrictified -> Type :=

  (* The actual implementation only unstrictifies non-function type bindings, but
     it is a sound transformation for any strict recursive binding *)
  | tr_TermBind_Rec_Unstrictify : forall vd t t' x τ,
      thunk_rec Γ t t' ->
      vd = VarDecl x τ ->
      thunk_rec_Binding_Rec Γ (TermBind Strict vd t) (TermBind NonStrict vd t') [(x, (t, Γ))]

  | tr_TermBind_Rec : forall s vd t t',
      thunk_rec Γ t t' ->
      thunk_rec_Binding_Rec Γ (TermBind s vd t) (TermBind s vd t') []

  | tr_DatatypeBind_Rec : forall d,
      thunk_rec_Binding_Rec Γ (DatatypeBind d) (DatatypeBind d) []

  | tr_TypeBind_Rec : forall tvd τ,
      thunk_rec_Binding_Rec Γ (TypeBind tvd τ) (TypeBind tvd τ) []

(* Add let NonRec bindings for unstrictified bindings, except if
   they were definitely pure *)
with strictify (Γ : ctx) : ctx_unstrictified -> list Binding -> Type :=

  | str_cons_pure : forall Γ_t t x Ω_bs bs,
     is_pure Γ_t t ->
     strictify Γ                 Ω_bs  bs ->
     strictify Γ ((x, (t, Γ)) :: Ω_bs) bs

  | str_cons_strictify : forall x x_info τ b bs Ω_bs,
     Lookup x (let_bound Strict) Γ ->
     b = TermBind Strict (VarDecl x τ) (Var x) ->
     strictify Γ                 Ω_bs         bs ->
     strictify Γ ((x, x_info) :: Ω_bs) ((b :: bs))

  | str_nil :
     strictify Γ [] []
.
