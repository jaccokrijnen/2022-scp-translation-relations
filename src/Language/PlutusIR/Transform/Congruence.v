Set Implicit Arguments.
From PlutusCert Require Import Language.PlutusIR.
From Equations Require Import Equations.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import Util.List.

Generalizable All Variables.

Section Congruence.
  Import NamedTerm.
  Variables (R : Term -> Term -> Type) (S : list Binding -> list Binding -> Type).

  Inductive Cong_Binding : Binding -> Binding -> Type :=
    | C_TermBind     : `{ R t t' -> Cong_Binding (TermBind s v t)
                                                 (TermBind s v t') }

    | C_TypeBind     : `{           Cong_Binding (TypeBind d T)
                                                 (TypeBind d T) }
    | C_DatatypeBind : `{           Cong_Binding (DatatypeBind d)
                                                   (DatatypeBind d) }
    .
  Inductive Cong_Bindings : list Binding -> list Binding -> Type :=
    | Cong_Bindings_Cons : forall {b b' bs bs'}, Cong_Binding b b' -> Cong_Bindings bs bs' -> Cong_Bindings (b :: bs) (b' :: bs')
    | Cong_Bindings_Nil  : Cong_Bindings nil nil.

  Inductive Cong : Term -> Term -> Type :=
    | C_Let      : `{ Cong_Bindings bs bs' -> R t t'    -> Cong (Let r bs t)
                                                                (Let r bs' t')}
    | C_Var      : `{                          Cong (Var n)
                                                    (Var n) }
    | C_TyAbs    : `{ R t t'                -> Cong (TyAbs n k t)
                                                    (TyAbs n k t') }
    | C_LamAbs   : `{ R t t' ->                Cong (LamAbs n T t)
                                                    (LamAbs n T t') }
    | C_Apply    : `{ R s s' -> R t t'      -> Cong (Apply s t)
                                                    (Apply s' t')}
    | C_Constant : `{                          Cong (Constant v)
                                                    (Constant v) }
    | C_Builtin  : `{                          Cong (Builtin f)
                                                    (Builtin f)}
    | C_TyInst   : `{ R t t'                -> Cong (TyInst t T)
                                                    (TyInst t' T)}
    | C_Error    : `{                          Cong (Error T)
                                                    (Error T)}
    | C_IWrap    : `{ R t t'                -> Cong (IWrap T1 T2 t)
                                                    (IWrap T1 T2 t') }
    | C_Unwrap   : `{ R t t'                -> Cong (Unwrap t)
                                                    (Unwrap t')}
  .

    Definition C_TermBind'     : forall t t' s s' v v' , s = s' -> v = v' -> R t t' -> Cong_Binding
                                    (TermBind s  v t)
                                    (TermBind s' v' t').
    Proof. intros. subst. apply C_TermBind. assumption. Qed.

    Definition C_TypeBind' : forall d d' ty ty',
      d = d' ->
      ty = ty' ->
      Cong_Binding (TypeBind d ty)
      (TypeBind d' ty').
    Proof. intros. subst. constructor. Qed.

    Definition C_DatatypeBind' : forall d d', d = d' -> Cong_Binding (DatatypeBind d)
                                                   (DatatypeBind d').
    Proof. intros. subst. constructor. Qed.

End Congruence.
