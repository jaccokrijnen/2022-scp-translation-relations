Set Implicit Arguments.
From PlutusCert Require Import Language.PlutusIR.
From PlutusCert Require Import Language.PlutusIR.Analysis.Equality.
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
                                                 (TermBind s v t') (*TODO: handle uniques properly*)}

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

    Definition is_cong_binding (is_R : Term -> Term -> bool) (b b' : Binding) : bool :=
      match b, b' with
        | (TermBind s v t), (TermBind s' v' t') => Strictness_eqb s s' && VDecl_eqb v v' && is_R t t'
        | (TypeBind v T), (TypeBind v' T') => TVDecl_eqb v v'  && Ty_eqb T T'
        | (DatatypeBind d), (DatatypeBind d') => DTDecl_eqb d d'
        | _, _                               => false
      end
    .

    Definition is_cong (is_R : Term -> Term -> bool) (t t' : Term) : bool :=
      match t, t' with
        | (Let r bs t), (Let r' bs' t')      => Recursivity_eqb r r' && forall2b (is_cong_binding is_R) bs bs' && is_R t t'
        | (Var n), (Var n')                  => String.eqb n n'
        | (TyAbs n k t), (TyAbs n' k' t')    => String.eqb n n' && Kind_eqb k k' && is_R t t'
        | (LamAbs n T t), (LamAbs n' T' t')  => String.eqb n n'&& Ty_eqb T T' && is_R t t'
        | (Apply s t), (Apply s' t')         => is_R s s' && is_R t t'
        | (Constant v), (Constant v')        => some_valueOf_eqb v v'
        | (Builtin f), (Builtin f')          => func_eqb f f'
        | (TyInst t T), (TyInst t' T')       => Ty_eqb T T' && is_R t t'
        | (Error T), (Error T')              => Ty_eqb T T'
        | (IWrap T1 T2 t), (IWrap T1' T2' t') => Ty_eqb T1 T1' && Ty_eqb T2 T2' && is_R t t'
        | (Unwrap t), (Unwrap t')            => is_R t t'
        | _, _                               => false
      end
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

  Notation "'Nothing'" := None.
  Notation "'Just'"    := Datatypes.Some.


  Definition s2o a b : sumbool a b -> option a := fun x => match x with
    | left x => Just x
    | _      => Nothing
    end.

  Set Equations Transparent.

  Variables r_dec : forall t1 t2, option (R t1 t2).
  (*
  Equations cong_dec : forall t1 t2, option (Cong t1 t2) :=
    cong_dec (Let _ _ _) (Let _ _ _) := Nothing;

    cong_dec (Var n)     (Var n')
      with string_dec n n' =>
     { | left eq_refl := Just C_Var;
       | _            := Nothing  };

    cong_dec (TyAbs n k t) (TyAbs n' k' t')
      with (string_dec n n', Kind_dec k k', r_dec t t') =>
     { | (left eq_refl, left eq_refl, Just r) := Just (C_TyAbs r);
       | _  := Nothing};

    cong_dec (LamAbs n ty t) (LamAbs n' ty' t')
      with (string_dec n n', Ty_dec ty ty', r_dec t t') =>
     { | (left eq_refl, left eq_refl, Just r) := Just (C_LamAbs r);
       | _  := Nothing};

    cong_dec (Apply t1 t2) (Apply t1' t2')
      with (r_dec t1 t1', r_dec t2 t2') =>
     { | (Just r, Just r') := Just (C_Apply r r');
       | _  := Nothing};

    cong_dec (Constant v) (Constant v')
      with some_valueOf_dec v v' =>
     { | left eq_refl := Just C_Constant;
       | _       := Nothing};

    cong_dec (Builtin f) (Builtin f')
      with func_dec f f' =>
    { | left eq_refl := Just C_Builtin;
      | _ := Nothing
    };

    cong_dec (TyInst t ty) (TyInst t' ty')
      with (r_dec t t', Ty_dec ty ty') =>
     { | (Just r, left eq_refl) := Just (C_TyInst r);
       | _  := Nothing};

    cong_dec (Error ty) (Error ty')
      with (Ty_dec ty ty') =>
     { | (left eq_refl) := Just C_Error;
       | _  := Nothing};

    cong_dec (IWrap ty1 ty2 t) (IWrap ty1' ty2' t')
      with (r_dec t t', Ty_dec ty1 ty1', Ty_dec ty2 ty2') =>
     { | (Just r, left eq_refl, left eq_refl) := Just (C_IWrap r);
       | _  := Nothing};

    cong_dec (Unwrap t) (Unwrap t')
      with (r_dec t t') =>
     { | Just r := Just (C_Unwrap r);
       | _  := Nothing};

    cong_dec _           _           := Nothing.
   *)
End Congruence.
