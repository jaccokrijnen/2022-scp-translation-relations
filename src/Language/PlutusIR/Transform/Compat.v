Set Implicit Arguments.
From PlutusCert Require Import Language.PlutusIR.
From Coq Require Import
  Bool.Bool
  Utf8_core.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import
  Util.List
  Analysis.Equality
  .

Import NamedTerm.

Section Compatibility.

  Context
    (R : Term -> Term -> Type)
    (dec_R : Term -> Term -> bool)
  .

  Inductive Compat_Binding : Binding -> Binding -> Type :=
    | C_TermBind     : ∀ s v t t',
        R t t' -> Compat_Binding (TermBind s v t) (TermBind s v t')

    | C_TypeBind     : ∀ d T,
        Compat_Binding (TypeBind d T) (TypeBind d T)

    | C_DatatypeBind : ∀ d,
        Compat_Binding (DatatypeBind d) (DatatypeBind d)
    .

  Inductive Compat_Bindings : list Binding -> list Binding -> Type :=
    | Compat_Bindings_Cons : ∀ {b b' bs bs'},
        Compat_Binding b b' -> Compat_Bindings bs bs' -> Compat_Bindings (b :: bs) (b' :: bs')

    | Compat_Bindings_Nil :
        Compat_Bindings nil nil.

  Inductive Compat : Term -> Term -> Type :=
    | C_Let : ∀ bs bs' r t t',
        Compat_Bindings bs bs' -> R t t' -> Compat (Let r bs t) (Let r bs' t')

    | C_Var : ∀ n,
        Compat (Var n) (Var n)

    | C_TyAbs : ∀ n k t t',
        R t t' -> Compat (TyAbs n k t) (TyAbs n k t')

    | C_LamAbs : ∀ n T t t' ,
        R t t' -> Compat (LamAbs n T t) (LamAbs n T t')

    | C_Apply : ∀ s s' t t' ,
        R s s' -> R t t' -> Compat (Apply s t) (Apply s' t')

    | C_Constant : ∀ v,
        Compat (Constant v) (Constant v)

    | C_Builtin : ∀ f,
        Compat (Builtin f) (Builtin f)

    | C_TyInst : ∀ t t' T,
        R t t' -> Compat (TyInst t T) (TyInst t' T)

    | C_Error : ∀ T,
        Compat (Error T) (Error T)

    | C_IWrap : ∀ T1 T2 t t',
        R t t' -> Compat (IWrap T1 T2 t) (IWrap T1 T2 t')

    | C_Unwrap : ∀ t t',
        R t t' -> Compat (Unwrap t) (Unwrap t')
  .

  Definition dec_compat_binding  (b b' : Binding) : bool :=
    match b, b' with
      | (TermBind s v t), (TermBind s' v' t') => Strictness_eqb s s' && VDecl_eqb v v' && dec_R t t'
      | (TypeBind v T), (TypeBind v' T') => TVDecl_eqb v v'  && Ty_eqb T T'
      | (DatatypeBind d), (DatatypeBind d') => DTDecl_eqb d d'
      | _, _                               => false
    end
  .


  Definition dec_compat (t t' : Term) : bool :=
    match t, t' with
      | (Let r bs t), (Let r' bs' t')      => Recursivity_eqb r r' && forall2b dec_compat_binding bs bs' && dec_R t t'
      | (Var n), (Var n')                  => String.eqb n n'
      | (TyAbs n k t), (TyAbs n' k' t')    => String.eqb n n' && Kind_eqb k k' && dec_R t t'
      | (LamAbs n T t), (LamAbs n' T' t')  => String.eqb n n'&& Ty_eqb T T' && dec_R t t'
      | (Apply s t), (Apply s' t')         => dec_R s s' && dec_R t t'
      | (Constant v), (Constant v')        => some_valueOf_eqb v v'
      | (Builtin f), (Builtin f')          => func_eqb f f'
      | (TyInst t T), (TyInst t' T')       => Ty_eqb T T' && dec_R t t'
      | (Error T), (Error T')              => Ty_eqb T T'
      | (IWrap T1 T2 t), (IWrap T1' T2' t') => Ty_eqb T1 T1' && Ty_eqb T2 T2' && dec_R t t'
      | (Unwrap t), (Unwrap t')            => dec_R t t'
      | _, _                               => false
    end
    .

  Ltac split_hypos :=
    match goal with
    | H : (?x && ?y)%bool = true |- _ => apply andb_true_iff in H; destruct H; split_hypos
    | _ => idtac
    end.

  Create HintDb Hints_soundness.
  Hint Resolve
    string_eqb_eq
    Recursivity_eqb_eq
    Strictness_eqb_eq
    Kind_eqb_eq
    Ty_eqb_eq
    some_valueOf_eqb_eq
    func_eqb_eq
    VDecl_eqb_eq
    TVDecl_eqb_eq
    DTDecl_eqb_eq
  : Hints_soundness.



  Lemma dec_compat_Binding_Compat_Binding : ∀ b b',
      (∀ t t', dec_R t t' = true -> R t t') ->
      dec_compat_binding b b' = true -> Compat_Binding b b'.
  Proof with eauto with reflection.
    intros b b' H_term_sound H_dec.
    destruct b, b'.
    all: simpl in H_dec; try discriminate H_dec.
    all: split_hypos.
    - assert (s = s0)...
      assert (v = v0)...
      subst.
      apply C_TermBind...
    - assert (t = t1)...
      assert (t0 = t2)...
      subst.
      apply C_TypeBind.
    - assert (d = d0)...
      subst.
      apply C_DatatypeBind.
  Qed.

  Lemma dec_compat_Bindings_Compat_Bindings : ∀ bs bs',
      (∀ t t', dec_R t t' = true -> R t t') ->
      forall2b dec_compat_binding bs bs' = true -> Compat_Bindings bs bs'.
  Proof with eauto.
    intros bs.
    induction bs.
    all: intros bs' H_term_sound H_dec.
    all: destruct bs'.
    all: simpl in H_dec.
    all: try discriminate H_dec.
    - apply Compat_Bindings_Nil.
    - split_hypos.
      apply Compat_Bindings_Cons.
      + apply dec_compat_Binding_Compat_Binding...
      + eauto.
  Qed.

  Lemma sound_dec_compat t t' :
    (∀ t t', dec_R t t' = true -> R t t') ->
    dec_compat t t' = true -> Compat t t'.
  Proof with eauto with reflection.
    generalize t'.
    clear t'.
    intros t'.
    induction t.
    all: intros H_sound_R H_dec.
    all: destruct t'.
    all: simpl in H_dec.
    all: try discriminate H_dec.
    all: split_hypos.
    - apply H_sound_R in H0.
      apply Recursivity_eqb_eq in H.
      subst.
      eapply C_Let...
      apply dec_compat_Bindings_Compat_Bindings...
    - apply String.eqb_eq in H_dec.
      subst.
      constructor.
    - assert (b = s)...
      assert (k = k0)...
      subst.
      eapply C_TyAbs...
    - assert (b = s)...
      assert (t = t1)...
      subst.
      apply C_LamAbs...
    - apply C_Apply...
    - assert (s = s0)...
      subst.
      apply C_Constant.
    - assert (d = d0)... subst.
      apply C_Builtin.
    - assert (t0 = t1)... subst.
      apply C_TyInst...
    - assert (t = t0)... subst.
      apply C_Error.
    - assert (t = t2)...
      assert (t0 = t3)...
      subst.
      apply C_IWrap...
    - apply C_Unwrap...
  Qed.

End Compatibility.
