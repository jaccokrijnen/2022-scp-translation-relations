Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Export PlutusCert.Language.PlutusIR.Analysis.BoundVars.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Module Ty.

  Inductive appears_free_in : tyname -> Ty -> Prop :=
    | AFI_TyVar : forall X,
        appears_free_in X (Ty_Var X)
    | AFI_TyFun1 : forall X T1 T2,
        appears_free_in X T1 ->
        appears_free_in X (Ty_Fun T1 T2)
    | AFI_TyFun2 : forall X T1 T2,
        appears_free_in X T2 ->
        appears_free_in X (Ty_Fun T1 T2)
    | AFI_TyIFix1 : forall X F T,
        appears_free_in X F ->
        appears_free_in X (Ty_IFix F T)
    | AFI_TyIFix2 : forall X F T,
        appears_free_in X T ->
        appears_free_in X (Ty_IFix F T)
    | AFI_TyForall : forall X bX K T,
        X <> bX ->
        appears_free_in X T ->
        appears_free_in X (Ty_Forall bX K T)
    | AFI_TyLam : forall X bX K T,
        X <> bX ->
        appears_free_in X T ->
        appears_free_in X (Ty_Lam bX K T)
    | AFI_TyApp1 : forall X T1 T2,
        appears_free_in X T1 ->
        appears_free_in X (Ty_App T1 T2)
    | AFI_TyApp2 : forall X T1 T2,
        appears_free_in X T2 ->
        appears_free_in X (Ty_App T1 T2)
    .

  Definition closed (T : Ty) :=
    forall X, ~(appears_free_in X T).

End Ty.

Module Term.

  Inductive appears_free_in : name -> Term -> Prop :=
    | AFIT_Let : forall x r bs t,
        ~(In x (bvbs bs)) ->
        appears_free_in x t ->
        appears_free_in x (Let r bs t)
    | AFIT_LetNonRec : forall x bs t,
        appears_free_in__bindings_nonrec x bs ->
        appears_free_in x (Let NonRec bs t)
    | AFIT_LetRec : forall x bs t,
        ~(In x (bvbs bs)) ->
        appears_free_in__bindings_rec x bs ->
        appears_free_in x (Let Rec bs t)
    | AFIT_Var : forall x,
        appears_free_in x (Var x)
    | AFIT_TyAbs : forall x bX K t0,
        appears_free_in x t0 ->
        appears_free_in x (TyAbs bX K t0)
    | AFIT_LamAbs : forall x bx T t0,
        x <> bx ->
        appears_free_in x t0 ->
        appears_free_in x (LamAbs bx T t0)
    | AFIT_Apply1 : forall x t1 t2,
        appears_free_in x t1 ->
        appears_free_in x (Apply t1 t2)
    | AFIT_Apply2 : forall x t1 t2,
        appears_free_in x t2 ->
        appears_free_in x (Apply t1 t2)
    | AFIT_TyInst : forall x t0 T,
        appears_free_in x t0 ->
        appears_free_in x (TyInst t0 T)
    | AFIT_IWrap : forall x F T t0,
        appears_free_in x t0 ->
        appears_free_in x (IWrap F T t0)
    | AFIT_Unwrap : forall x t0,
        appears_free_in x t0 ->
        appears_free_in x (Unwrap t0)

  with appears_free_in__bindings_nonrec : name -> list Binding -> Prop :=
    | AFIT_ConsB1_NonRec : forall x b bs,
        appears_free_in__binding x b ->
        appears_free_in__bindings_nonrec x (b :: bs)
    | AFIT_ConsB2_NonRec : forall x b bs,
        ~(In x (bvb b)) ->
        appears_free_in__bindings_nonrec x bs ->
        appears_free_in__bindings_nonrec x (b :: bs)

  with appears_free_in__bindings_rec : name -> list Binding -> Prop :=
    | AFIT_ConsB1_Rec : forall x b bs,
        appears_free_in__binding x b ->
        appears_free_in__bindings_rec x (b :: bs)
    | AFIT_ConsB2_Rec : forall x b bs,
        appears_free_in__bindings_rec x bs ->
        appears_free_in__bindings_rec x (b :: bs)

  with appears_free_in__binding : name -> Binding -> Prop :=
    | AFIT_TermBind : forall x s vd t0,
        appears_free_in x t0 ->
        appears_free_in__binding x (TermBind s vd t0)
    .

  Definition closed (t : Term) :=
    forall x, ~(appears_free_in x t).

End Term.

Module Annotation.

  Fixpoint splitTy (T : Ty) : list Ty * Ty :=
    match T with
    | Ty_Fun Targ T' => (cons Targ (fst (splitTy T')), snd (splitTy T'))
    | Tr => (nil, Tr)
    end.


  Definition fromDecl (tvd : tvdecl tyname) : tyname * Kind :=
    match tvd with
    | TyVarDecl v K => (v, K)   
    end.

  Inductive appears_free_in (X : tyname) : Term -> Prop :=
    | AFIA_Let : forall r bs t,
        ~(In X (btvbs bs)) ->
        appears_free_in X t ->
        appears_free_in X (Let r bs t)
    | AFIA_LetNonRec : forall bs t,
        appears_free_in__bindings_nonrec X bs ->
        appears_free_in X (Let NonRec bs t)
    | AFIA_LetRec : forall bs t,
        ~(In X (btvbs bs)) ->
        appears_free_in__bindings_rec X bs ->
        appears_free_in X (Let Rec bs t)
    | AFIA_TyAbs : forall bX K t0,
        X <> bX ->
        appears_free_in X t0 ->
        appears_free_in X (TyAbs bX K t0)
    | AFIA_LamAbs1 : forall bx T t0,
        Ty.appears_free_in X T ->
        appears_free_in X (LamAbs bx T t0)
    | AFIA_LamAbs2 : forall bx T t0,
        appears_free_in X t0 ->
        appears_free_in X (LamAbs bx T t0)
    | AFIA_Apply1 : forall t1 t2,
        appears_free_in X t1 ->
        appears_free_in X (Apply t1 t2)
    | AFIA_Apply2 : forall t1 t2,
        appears_free_in X t2 ->
        appears_free_in X (Apply t1 t2)
    | AFIA_TyInst1 : forall t0 T,
        Ty.appears_free_in X T ->
        appears_free_in X (TyInst t0 T)
    | AFIA_TyInst2 : forall t0 T,
        appears_free_in X t0 ->
        appears_free_in X (TyInst t0 T)
    | AFIA_IWrap1 : forall F T t0,
        Ty.appears_free_in X F ->
        appears_free_in X (IWrap F T t0)
    | AFIA_IWrap2 : forall F T t0,
        Ty.appears_free_in X T ->
        appears_free_in X (IWrap F T t0)
    | AFIA_IWrap3 : forall F T t0,
        appears_free_in X t0 ->
        appears_free_in X (IWrap F T t0)
    | AFIA_Unwrap : forall t0,
        appears_free_in X t0 ->
        appears_free_in X (Unwrap t0)

  with appears_free_in__constructor (X : tyname) : constructor -> Prop :=
    | AFIA_Constructor : forall x T ar Targs Tr,
        (Targs, Tr) = splitTy T ->
        (exists U, In U Targs /\ Ty.appears_free_in X U) ->
        appears_free_in__constructor X (Constructor (VarDecl x T) ar)

  with appears_free_in__bindings_nonrec (X : tyname) : list Binding -> Prop :=
    | AFIA_ConsB1_NonRec : forall b bs,
        appears_free_in__binding X b ->
        appears_free_in__bindings_nonrec X (b :: bs)
    | AFIA_ConsB2_NonRec : forall b bs,
        ~(In X (btvb b)) ->
        appears_free_in__bindings_nonrec X bs ->
        appears_free_in__bindings_nonrec X (b :: bs)

  with appears_free_in__bindings_rec (X : tyname) : list Binding -> Prop :=
    | AFIA_ConsB1_Rec : forall b bs,
        appears_free_in__binding X b ->
        appears_free_in__bindings_rec X (b :: bs)
    | AFIA_ConsB2_Rec : forall b bs,
        appears_free_in__bindings_rec X bs ->
        appears_free_in__bindings_rec X (b :: bs)

  with appears_free_in__binding (X: tyname) : Binding -> Prop :=
    | AFIA_TermBind1 : forall s x T t0,
        Ty.appears_free_in X T ->
        appears_free_in__binding X (TermBind s (VarDecl x T) t0)
    | AFIA_TermBind2 : forall s x T t0,
        appears_free_in X t0 ->
        appears_free_in__binding X (TermBind s (VarDecl x T) t0)
    | AFI_TypeBind : forall Y K T,
        Ty.appears_free_in X T ->
        appears_free_in__binding X (TypeBind (TyVarDecl Y K) T)
    | AFI_DatatypeBind : forall Y K ZKs matchFunc cs,
        ~ In X (map fst (rev (map fromDecl ZKs))) ->
        (exists c, In c cs /\ appears_free_in__constructor X c) ->
        appears_free_in__binding X (DatatypeBind (Datatype (TyVarDecl Y K) ZKs matchFunc cs))
  .

  Definition closed (t : Term) :=
    forall x, ~(appears_free_in x t).

End Annotation.

#[export] Hint Constructors 
  Ty.appears_free_in 
  : core.

#[export] Hint Constructors 
  Term.appears_free_in 
  Term.appears_free_in__bindings_nonrec
  Term.appears_free_in__bindings_rec
  Term.appears_free_in__binding 
  : core.

#[export] Hint Constructors 
  Annotation.appears_free_in 
  Annotation.appears_free_in__constructor
  Annotation.appears_free_in__bindings_nonrec
  Annotation.appears_free_in__bindings_rec
  Annotation.appears_free_in__binding : core. 

(** Full closedness of terms (and type annotations) *)
Definition closed (t : Term) :=
  (forall x, ~(Term.appears_free_in x t)) /\ (forall X, ~(Annotation.appears_free_in X t)).
