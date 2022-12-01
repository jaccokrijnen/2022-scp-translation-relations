From Coq Require Import
  Strings.String
  Lists.List
  Arith.PeanoNat
  Strings.Ascii
  Program.Basics
  .

Import ListNotations.
Local Open Scope string_scope.

From PlutusCert Require Import
  Util
  Language.PlutusIR
  Language.PlutusIR.Folds
  .

Import NamedTerm.

Module Ty.

  Inductive appears_bound_in (X: tyname) : Ty -> Prop :=
    | ABI_TyFun1 : forall T1 T2,
        appears_bound_in X T1 ->
        appears_bound_in X (Ty_Fun T1 T2)
    | ABI_TyFun2 : forall T1 T2,
        appears_bound_in X T2 ->
        appears_bound_in X (Ty_Fun T1 T2)
    | ABI_TyIFix1 : forall F T,
        appears_bound_in X F ->
        appears_bound_in X (Ty_IFix F T)
    | ABI_TyIFix2 : forall F T,
        appears_bound_in X T ->
        appears_bound_in X (Ty_IFix F T)
    | ABI_TyForall1 : forall K T,
        appears_bound_in X (Ty_Forall X K T)
    | ABI_TyForall2 : forall Y K T,
        X <> Y ->
        appears_bound_in Y T ->
        appears_bound_in X (Ty_Forall Y K T)
    | ABI_TyLam1 : forall K T,
        appears_bound_in X (Ty_Lam X K T)
    | ABI_TyLam2 : forall Y K T,
        X <> Y ->
        appears_bound_in Y T ->
        appears_bound_in X (Ty_Lam Y K T)
    | ABI_TyApp1 : forall T1 T2,
        appears_bound_in X T1 ->
        appears_bound_in X (Ty_App T1 T2)
    | ABI_TyApp2 : forall T1 T2,  
        appears_bound_in X T2 ->
        appears_bound_in X (Ty_App T1 T2).

End Ty.

Module Term.

  Definition bv_constructor (c : constructor) : string :=
    match c with
    | Constructor (VarDecl x _) _ => x
    end.

  Inductive appears_bound_in (x : name) : Term -> Prop :=
    | ABI_LamAbs1 : forall T t,
        appears_bound_in x (LamAbs x T t)
    | ABI_LamAbs2 : forall y T t,
        x <> y ->
        appears_bound_in x t ->
        appears_bound_in x (LamAbs y T t)
    | ABI_Apply1 : forall t1 t2,
        appears_bound_in x t1 ->
        appears_bound_in x (Apply t1 t2)
    | ABI_Apply2 : forall t1 t2,
        appears_bound_in x t2 ->
        appears_bound_in x (Apply t1 t2)
    | ABI_TyAbs : forall X K t,
        appears_bound_in x t ->
        appears_bound_in x (TyAbs X K t)
    | ABI_TyInst : forall t T,
        appears_bound_in x t ->
        appears_bound_in x (TyInst t T)
    | ABI_IWrap : forall F T t,
        appears_bound_in x t ->
        appears_bound_in x (IWrap F T t)
    | ABI_Unwrap : forall t,
        appears_bound_in x t ->
        appears_bound_in x (Unwrap t)
    | ABI_Let_Nil : forall recty t0,
        appears_bound_in x t0 ->
        appears_bound_in x (Let recty nil t0)
    | ABI_Let_Cons : forall recty b bs t0,
        appears_bound_in x (Let recty bs t0) ->
        appears_bound_in x (Let recty (b :: bs) t0)
    | ABI_Let_TermBind1 : forall recty stricty T t bs t0,
        appears_bound_in x (Let recty (TermBind stricty (VarDecl x T) t :: bs) t0)
    | ABI_Let_TermBind2 : forall recty stricty y T t bs t0,
        appears_bound_in x t ->
        appears_bound_in x (Let recty (TermBind stricty (VarDecl y T) t :: bs) t0)
    | ABI_Let_DatatypeBind : forall recty XK YKs mfunc cs t0 bs,
        In x (mfunc :: map bv_constructor cs) ->
        appears_bound_in x (Let recty (DatatypeBind (Datatype XK YKs mfunc cs) :: bs) t0) 
    .

End Term.

Module Annotation.

  Inductive appears_bound_in (X : tyname) : Term -> Prop :=
    | ABI_LamAbs1 : forall x T t,
        Ty.appears_bound_in X T ->
        appears_bound_in X (LamAbs x T t)
    | ABI_LamAbs : forall x T t,
        appears_bound_in X t ->
        appears_bound_in X (LamAbs x T t)
    | ABI_Apply1 : forall t1 t2,
        appears_bound_in X t1 ->
        appears_bound_in X (Apply t1 t2)
    | ABI_Apply2 : forall t1 t2,
        appears_bound_in X t2 ->
        appears_bound_in X (Apply t1 t2)
    | ABI_TyAbs1 : forall K t,
        appears_bound_in X (TyAbs X K t)
    | ABI_TyAbs2 : forall Y K t,
        X <> Y ->
        appears_bound_in X t ->
        appears_bound_in X (TyAbs Y K t)
    | ABI_TyInst1 : forall t T,
        appears_bound_in X t ->
        appears_bound_in X (TyInst t T)
    | ABI_TyInst2 : forall t T,
        Ty.appears_bound_in X T ->
        appears_bound_in X (TyInst t T)
    | ABI_IWrap1 : forall F T t,
        Ty.appears_bound_in X F ->
        appears_bound_in X (IWrap F T t)
    | ABI_IWrap2 : forall F T t,
        Ty.appears_bound_in X T ->
        appears_bound_in X (IWrap F T t)
    | ABI_IWrap3 : forall F T t,
        appears_bound_in X t ->
        appears_bound_in X (IWrap F T t)
    | ABI_Unwrap : forall t,
        appears_bound_in X t ->
        appears_bound_in X (Unwrap t)
    | ABI_Error : forall T,
        Ty.appears_bound_in X T ->
        appears_bound_in X (Error T)
    | ABI_Let_Nil : forall recty t0,
        appears_bound_in X t0 ->
        appears_bound_in X (Let recty nil t0)
    | ABI_Let_Cons : forall recty b bs t0,
        appears_bound_in X (Let recty bs t0) ->
        appears_bound_in X (Let recty (b :: bs) t0)
    | ABI_Let_TermBind1 : forall recty stricty x T t bs t0,
        Ty.appears_bound_in X T ->
        appears_bound_in X (Let recty (TermBind stricty (VarDecl x T) t :: bs) t0)
    | ABI_Let_TermBind2 : forall recty stricty y T t bs t0,
        appears_bound_in X t ->
        appears_bound_in X (Let recty (TermBind stricty (VarDecl y T) t :: bs) t0)
    | ABI_Let_TypeBind1 : forall recty K T bs t0,
        appears_bound_in X (Let recty (TypeBind (TyVarDecl X K) T :: bs) t0)
    | ABI_Let_TypeBind2 : forall recty Y K T bs t0,
        Ty.appears_bound_in X T ->
        appears_bound_in X (Let recty (TypeBind (TyVarDecl Y K) T :: bs) t0)
    | ABI_Let_DatatypeBind : forall recty K YKs mfunc cs t0 bs,
        appears_bound_in X (Let recty (DatatypeBind (Datatype (TyVarDecl X K) YKs mfunc cs) :: bs) t0) 
    .

End Annotation.

#[export] Hint Constructors 
  Ty.appears_bound_in 
  Term.appears_bound_in
  Annotation.appears_bound_in
  : core.


Section BoundVars.
  Context
    {var tyvar : Set}
    (var_eqb : var -> var -> bool)
    .

Definition term' := term var tyvar var tyvar.
Definition binding' := binding var tyvar var tyvar.
Definition constructor' := constr tyvar var tyvar.

(** Retrieve bound term variable bindings *)

Definition bvc (c : constructor') : var :=
  match c with
  | Constructor (VarDecl x _) _ => x
  end.

Definition bvb (b : binding') : list var :=
  match b with
  | TermBind _ (VarDecl x _) _ => cons x nil
  | TypeBind (TyVarDecl X _) _ => nil
  | DatatypeBind (Datatype (TyVarDecl X _) YKs matchFunc cs) => matchFunc :: (rev (map bvc cs))
  end.

Definition bvbs (bs : list binding') : list var := List.concat (map bvb bs).


Fixpoint boundTerms_bindings (bs : list binding') : list (var * term var tyvar var tyvar) := match bs with
    | ((TermBind _ (VarDecl v _) t) :: bs) => (v, t) :: boundTerms_bindings bs
    | (b                :: bs) =>           boundTerms_bindings bs
    | nil               => nil
    end.

(** Retrieve bound type variable bindings *)

Definition btvb (b : binding') : list tyvar :=
  match b with
  | TermBind _ (VarDecl x _) _ => nil
  | TypeBind (TyVarDecl X _) _ => cons X nil
  | DatatypeBind (Datatype (TyVarDecl X _) YKs matchFunc cs) => cons X nil
  end.

Definition btvbs (bs : list binding') : list tyvar := List.concat (map btvb bs).

Fixpoint bound_vars (t : term') : list var :=
 match t with
   | Let rec bs t => concat (map bound_vars_binding bs) ++ bound_vars t
   | (LamAbs n ty t)   => n :: (bound_vars t)
   | (Var n)           => []
   | (TyAbs n k t)     => bound_vars t
   | (Apply s t)       => bound_vars s ++ bound_vars t
   | (TyInst t ty)     => bound_vars t
   | (IWrap ty1 ty2 t) => bound_vars t
   | (Unwrap t)        => bound_vars t
   | (Error ty)        => []
   | (Constant v)      => []
   | (Builtin f)       => []
   end
with bound_vars_binding (b : binding') : list var := match b with
  | TermBind _ (VarDecl v _) t => [v] ++ bound_vars t
  | DatatypeBind (Datatype _ _ matchf constructors ) => [matchf] ++ map constructorName constructors
  | _                          => []
  end.

Definition bound_vars_bindings := @concat _ ∘ map bound_vars_binding.

End BoundVars.

Import BoundVars.Term.

Definition P_Term (t : Term) : Prop := Forall (fun v => appears_bound_in v t) (bound_vars t).
Definition P_Binding (b : Binding) := Forall (fun v => forall t bs recty, appears_bound_in v (Let recty (b :: bs) t)) (bound_vars_binding b).

Lemma bound_vars_appears_bound_in : (forall t, P_Term t) /\ (forall b, P_Binding b).
Proof with eauto using appears_bound_in.
  apply Term__multind with (P := P_Term) (Q := P_Binding).
  all: unfold P_Term...
  - intros.
    unfold P_Term.
    apply Forall_app.
    split.
    + unfold P_Binding in H.
      induction bs.
      * constructor.
      * simpl. 
        apply Forall_app.
        split.
          ** apply ForallP_Forall in H.
             apply Forall_inv in H.
             eapply Forall_impl.
               2: { apply H. }
               auto.
          ** apply ForallP_Forall in H.
             apply Forall_inv_tail in H.
             apply ForallP_Forall in H.
             apply IHbs in H.
             eapply Forall_impl.
             intros b. apply ABI_Let_Cons.
             auto.

    + unfold P_Term in *.
      eapply Forall_impl with (P := fun v => appears_bound_in v t)...
      eauto using appears_bound_in.
      intros.
      induction bs...
      apply ForallP_Forall in H.
      apply Forall_inv_tail in H.
      apply ForallP_Forall in H...
  - intros.
    cbv.
    auto.
  - intros.
    eapply Forall_impl. 2: exact H.
    eauto.
  - intros.
    eapply Forall_cons...
    eapply Forall_impl with (P := fun a => appears_bound_in a t0)...
    intros. 
      destruct (string_dec a s).
      * subst. apply ABI_LamAbs1.
      * apply ABI_LamAbs2...

  (* Common pattern: only need to prove an implication using a ABI rule *)
  Ltac tac rule :=
    intros; eapply Forall_impl; [intros a; apply rule | auto].

  - intros.
    apply Forall_app. split.
      + tac ABI_Apply1.
      + tac ABI_Apply2.
  - intros. cbv. auto.
  - intros. cbv. auto.
  - tac ABI_TyInst.
  - intros. cbv. auto.
  - tac ABI_IWrap.
  - tac ABI_Unwrap.
  - intros.
    unfold P_Binding.
    intros.
    cbv.
    destruct v.
    eapply Forall_cons.
      + intros...
      + intros. eapply Forall_impl with (P := fun v => appears_bound_in v t).
        1: { intros. apply ABI_Let_TermBind2... }
        auto.
  - unfold P_Binding.
    intros.
    cbv...
  - unfold P_Binding.
    cbv.
    destruct dtd.
    apply Forall_cons.
    + intros.
      apply ABI_Let_DatatypeBind.
      constructor...
    + apply Forall_forall.
      intros.
      apply ABI_Let_DatatypeBind.
      apply in_cons.
      assumption.
Qed.

Inductive decide {a : Type} (P : a -> Type) (x : a) :=
  | dec_False : notT (P x) -> decide P x
  | dec_True  : P x        -> decide P x
  .

#[local]
Hint Constructors decide : core.

Definition dec_all a P (xs : list a) : ForallT (decide P) xs -> decide (ForallT P) xs.
Proof.
Admitted.
