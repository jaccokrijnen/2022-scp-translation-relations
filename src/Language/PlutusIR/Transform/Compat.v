Set Implicit Arguments.
From PlutusCert Require Import Language.PlutusIR.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import Util.List.

Generalizable All Variables.

Section Compatibility.
  Import NamedTerm.
  Variables (R : Term -> Term -> Type) (S : list Binding -> list Binding -> Type).

  Inductive Compat_Binding : Binding -> Binding -> Type :=
    | C_TermBind     : `{ R t t' -> Compat_Binding (TermBind s v t)
                                                 (TermBind s v t') }

    | C_TypeBind     : `{           Compat_Binding (TypeBind d T)
                                                 (TypeBind d T) }
    | C_DatatypeBind : `{           Compat_Binding (DatatypeBind d)
                                                   (DatatypeBind d) }
    .
  Inductive Compat_Bindings : list Binding -> list Binding -> Type :=
    | Compat_Bindings_Cons : forall {b b' bs bs'}, Compat_Binding b b' -> Compat_Bindings bs bs' -> Compat_Bindings (b :: bs) (b' :: bs')
    | Compat_Bindings_Nil  : Compat_Bindings nil nil.

  Inductive Compat : Term -> Term -> Type :=
    | C_Let      : `{ Compat_Bindings bs bs' -> R t t'    -> Compat (Let r bs t)
                                                                (Let r bs' t')}
    | C_Var      : `{                          Compat (Var n)
                                                    (Var n) }
    | C_TyAbs    : `{ R t t'                -> Compat (TyAbs n k t)
                                                    (TyAbs n k t') }
    | C_LamAbs   : `{ R t t' ->                Compat (LamAbs n T t)
                                                    (LamAbs n T t') }
    | C_Apply    : `{ R s s' -> R t t'      -> Compat (Apply s t)
                                                    (Apply s' t')}
    | C_Constant : `{                          Compat (Constant v)
                                                    (Constant v) }
    | C_Builtin  : `{                          Compat (Builtin f)
                                                    (Builtin f)}
    | C_TyInst   : `{ R t t'                -> Compat (TyInst t T)
                                                    (TyInst t' T)}
    | C_Error    : `{                          Compat (Error T)
                                                    (Error T)}
    | C_IWrap    : `{ R t t'                -> Compat (IWrap T1 T2 t)
                                                    (IWrap T1 T2 t') }
    | C_Unwrap   : `{ R t t'                -> Compat (Unwrap t)
                                                    (Unwrap t')}
  .
End Compatibility.
