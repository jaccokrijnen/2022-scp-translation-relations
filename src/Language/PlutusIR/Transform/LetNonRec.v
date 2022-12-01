From PlutusCert Require Import Language.PlutusIR.
Import NamedTerm.
From PlutusCert Require Import Language.PlutusIR.Transform.Congruence.
From PlutusCert Require Import Language.PlutusIR.Analysis.FreeVars.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Import Coq.Lists.List.ListNotations.


(* CNR = Compile Non-Recursive
   Desugaring strict, non-recursive lets into lambda-applications
*)
Inductive CNR_Term : Term -> Term -> Type :=
  | CNR_Let : forall {bs t_body t_body' f_bs},
      CNR_Term t_body t_body' ->
      CNR_Bindings bs f_bs ->
      CNR_Term (Let NonRec bs t_body) (fold_right apply t_body' f_bs )
  | CNR_Cong : forall {t t'},
      Cong CNR_Term t t' ->
      CNR_Term t t'

(*
  `CNR_Bindings bs fs` states that each binding
   in the group `bs` can be desugared into t_bs
   where t_bs is of the form
     Apply (LamAbs (Apply (LamAbs ... t ...) t_1)) t_0
*)
with CNR_Bindings : list Binding -> list (Term -> Term) -> Type :=
  | CNR_Nil  :
      CNR_Bindings nil nil
  | CNR_Cons : forall {b bs f_b f_bs},
      CNR_Binding        b   f_b ->
      CNR_Bindings       bs  f_bs ->
      CNR_Bindings (b :: bs) (f_b :: f_bs )

(* `CNR_Binding b f` states that the strict binding
      v = t_bound
    can be desugared into
      (\v -> t) t_bound
    for any term `t`
*)
with CNR_Binding : Binding -> (Term -> Term) -> Type :=
  | CNR_Desugar : forall {v t_bound t_bound' ty},
      CNR_Term t_bound t_bound' ->
      CNR_Binding
        (TermBind Strict (VarDecl v ty) t_bound)
        (fun t_bs => Apply (LamAbs v ty t_bs) t_bound')
  .


(* Functional specification of the pass *)
Fixpoint compile_term (t : Term) : Term := match t with
  | Let NonRec bs t => fold_right apply t (map compile_NonRec_Binding bs)
  | Let Rec bs t    => Let Rec (map compile_Rec_Binding bs) (compile_term t)

  | TyAbs α k t     => TyAbs α k (compile_term t)
  | LamAbs x τ t    => LamAbs x τ (compile_term t)
  | Apply t1 t2     => Apply (compile_term t1) (compile_term t2)
  | IWrap σ τ t     => IWrap σ τ (compile_term t)
  | Unwrap t        => Unwrap (compile_term t)
  | TyInst t τ      => TyInst (compile_term t) τ

  | Var x           => Var x
  | Constant c      => Constant c
  | Builtin f       => Builtin f
  | Error τ         => Error τ
  end

with compile_NonRec_Binding (b : Binding) : Term -> Term :=
  match b with
  | TermBind Strict (VarDecl v ty) t_bound => fun t_bs => Apply (LamAbs v ty t_bs) (compile_term t_bound)
  | b => id
  end

with compile_Rec_Binding (b : Binding) : Binding := match b with
  | TermBind Strict vd t_bound => TermBind Strict vd (compile_term t_bound)
  | b => b
  end
  .

(* Constructors where equalities in indices are made
   explicit *)
Ltac eq_principle :=
  intros;
  subst;
  constructor;
  assumption.

Definition C_TyAbs' : forall R (t t' : Term) (n n' : tyname) (k k' : Kind),
              n = n' -> k = k'
              -> R t t' -> Cong R (TyAbs n k t) (TyAbs n' k' t').
Proof. eq_principle. Qed.

Definition C_LamAbs' : forall R (t t' : Term) (n n' : tyname) (ty ty': Ty),
                n = n' -> ty = ty' -> R t t' -> Cong R (LamAbs n ty t) (LamAbs n' ty' t').
Proof. eq_principle. Qed.

Definition C_Var' : forall R (n n' : tyname), (n = n') -> Cong R (Var n) (Var n').
Proof. eq_principle. Qed.

Definition C_Let' : forall R (bs bs' : list Binding) (t t' : Term) (r r' : Recursivity),
             r = r' ->
             Cong_Bindings R bs bs' ->
             R t t' -> Cong R (Let r bs t) (Let r' bs' t').
Proof. eq_principle. Qed.

Definition C_Apply' : forall R (s s' t t' : Term),
               R s s' -> R t t' -> Cong R (Apply s t) (Apply s' t').
Proof. eq_principle. Qed.
Definition C_Constant' : forall R (v v' : @some valueOf), v = v' -> Cong R (Constant v) (Constant v').
Proof. eq_principle. Qed.
Definition C_Builtin' : forall R (f f' : DefaultFun), f = f' -> Cong R (Builtin f) (Builtin f').
Proof. eq_principle. Qed.
Definition C_TyInst' : forall R (t t' : Term) (ty ty' : Ty),
                ty = ty' -> R t t' -> Cong R (TyInst t ty) (TyInst t' ty').
Proof. eq_principle. Qed.

Definition C_Error' : forall R (ty ty' : Ty), ty = ty' -> Cong R (Error ty) (Error ty').
Proof. eq_principle. Qed.

Definition C_IWrap' : forall R (t t' : Term) (ty1 ty1' ty2 ty2' : Ty),
               ty1 = ty1' -> ty2 = ty2' -> R t t' -> Cong R (IWrap ty1 ty2 t) (IWrap ty1' ty2' t').
Proof. eq_principle. Qed.
Definition C_Unwrap' : forall R (t t' : Term), R t t' -> Cong R (Unwrap t) (Unwrap t').
Proof. eq_principle. Qed.

Create HintDb eq_principles.
Hint Resolve C_Let' C_Var' C_LamAbs' C_TyAbs' C_Apply' C_Constant' C_Builtin' C_TyInst' C_Error' C_IWrap' C_Unwrap : eq_principles.

(*
Definition CNR_Let' : forall (bs : list Binding) (t1 t1' t2 t2' t3 t3' : Term),
  t1 = t1' -> t2 = t2' -> t3 = t3' ->
  CNR_Term t1 t2 ->
  CNR_Bindings bs f_bs -> CNR_Term (Let NonRec bs t1') t3'.
Proof. intros. subst. eapply CNR_Let.
  + apply X.
  + apply X0.
  Qed.
*)

Definition CNR_Desugar'
    : forall v v' t_bound t_bound' ty,
        v = v' ->
        CNR_Term t_bound t_bound' ->
        CNR_Binding
          (TermBind Strict (VarDecl v ty) t_bound)
          (fun t_bs => Apply (LamAbs v' ty t_bs) t_bound').
Proof.
  intros. subst. apply CNR_Desugar. assumption.
Qed.

