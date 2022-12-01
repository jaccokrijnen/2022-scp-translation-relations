Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.Language.PlutusIR.Analysis.BoundVars.
Require Import PlutusCert.Util.

Require Import Coq.Lists.List.

Module Ty.

  Inductive unique : Ty -> Prop :=
    | UNI_TyFun : forall T1 T2,
        unique T1 ->
        unique T2 ->
        unique (Ty_Fun T1 T2)
    | UNI_TyBuiltin : forall st,
        unique (Ty_Builtin st)
    | UNI_TyVar : forall X,
        unique (Ty_Var X)
    | UNI_TyForall : forall X K T,
        ~ Ty.appears_bound_in X T ->
        unique T ->
        unique (Ty_Forall X K T)
    | UNI_TyIFix : forall F T,
        unique F ->
        unique T ->
        unique (Ty_IFix F T)
    | UNI_TyLam : forall X K T,
        ~ Ty.appears_bound_in X T ->
        unique T ->
        unique (Ty_Lam X K T)
    | UNI_TyApp : forall T1 T2,
        unique T1 ->
        unique T2 ->
        unique (Ty_App T1 T2)
    .

End Ty.

Module Term.

  Inductive unique : Term -> Prop :=
    | UNI_Var : forall x,
        unique (Var x)
    | UNI_LamAbs : forall x T t,
        ~ Term.appears_bound_in x t ->
        unique t ->
        Ty.unique T ->
        unique (LamAbs x T t)
    | UNI_App : forall t1 t2,
        unique t1 ->
        unique t2 ->
        unique (Apply t1 t2)
    | UNI_TyAbs : forall X K t,
        ~ Annotation.appears_bound_in X t ->
        unique t ->   
        unique (TyAbs X K t)
    | UNI_TyInst : forall t T,
        unique t ->
        Ty.unique T ->
        unique (TyInst t T)
    | UNI_IWrap : forall F T t,
        Ty.unique F ->
        Ty.unique T ->
        unique t ->
        unique (IWrap F T t)
    | UNI_Unwrap : forall t,
        unique t ->
        unique (Unwrap t)
    | UNI_Constant : forall sv,
        unique (Constant sv)
    | UNI_Builtin : forall f,
        unique (Builtin f)
    | UNI_Error : forall T,
        Ty.unique T ->
        unique (Error T)
    | UNI_Let_Nil : forall recty t0,
        unique t0 ->
        unique (Let recty nil t0)
    | UNI_Let_TermBind : forall recty stricty x T t bs t0,
        ~ Term.appears_bound_in x t ->
        ~ Term.appears_bound_in x (Let recty bs t0) ->
        unique t ->
        unique (Let recty bs t0) ->
        unique (Let recty (TermBind stricty (VarDecl x T) t :: bs) t0)
    | UNI_Let_TypeBind : forall recty X K T bs t0,
        ~ Ty.appears_bound_in X T ->
        ~ Annotation.appears_bound_in X (Let recty bs t0) ->
        Ty.unique T ->
        unique (Let recty bs t0) ->
        unique (Let recty (TypeBind (TyVarDecl X K) T :: bs) t0)
    | UNI_Let_DatatypeBind : forall recty X K YKs mfunc cs t0 bs,
        ~ Annotation.appears_bound_in X (Let recty bs t0) ->
        unique (Let recty bs t0) ->
        unique (Let recty (DatatypeBind (Datatype (TyVarDecl X K) YKs mfunc cs) :: bs) t0) 
    .

End Term.
