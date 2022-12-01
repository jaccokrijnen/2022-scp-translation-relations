Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Ascii.
Require Import Omega.
From Equations Require Import Equations.

Set Implicit Arguments.

From PlutusCert Require Import Language.PlutusIR.
Import NamedTerm.
From PlutusCert Require Import Language.PlutusIR.Folds.

Local Open Scope string_scope.

Section list_size.
  Context {A : Type} (f : A -> nat).

  Equations list_size (l : list A) : nat :=
  list_size nil := 0;
  list_size (cons x xs) := S (f x + list_size xs).

  Lemma In_list_size:
    forall x xs, In x xs -> f x < S (list_size xs).
  Proof.
    intros. funelim (list_size xs); simpl in x. destruct H.
    destruct H0.
    - subst; omega.
    - specialize (H _ H0). intuition.
  Qed.
End list_size.
Transparent list_size.

Definition term_size (t : Term) : nat :=
  foldTermUse (fun xs => 1 + list_sum xs) t.

Definition binding_size (b : Binding) : nat :=
  foldBindingUse (fun xs => 1 + list_sum xs) b.

Definition bindings_size (bs : list Binding) : nat :=
  foldBindingsUse (fun xs => 1 + list_sum xs) bs.

(*
Lemmas for showing how `term_size` (defined as a fold) reduces
*)

Axiom fold_reduce_let : forall r t bs,
  term_size (Let r bs t)  = 1 + (term_size t) + (bindings_size bs).
(*
  unfold term_size, bindings_size, foldTermUse, foldBindingsUse.
  unfold foldTerm at 1. unfold a_Let; simpl.
  simpl.
reflexivity. Qed.
*)

Lemma fold_reduce_apply : forall s t,
  term_size (Apply s t) = 1 + list_sum [term_size s ; term_size t].
reflexivity. Qed.

Lemma fold_reduce_tyabs : forall n k t,
  term_size (TyAbs n k t) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma fold_reduce_lamabs : forall n k t,
  term_size (LamAbs n k t) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma fold_reduce_tyinst : forall t ty,
  term_size (TyInst t ty) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma fold_reduce_iwrap : forall ty1 ty2 t,
  term_size (IWrap ty1 ty2 t) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma fold_reduce_unwrap : forall t,
  term_size (Unwrap t) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma fold_reduce_termbind s v t:
  binding_size (TermBind s v t) = 1 + list_sum [term_size t].
  reflexivity.
Qed.

(* Shorthand types for size comparison between terms *)
Definition Smaller (s s' t t' : Term) : Prop :=
  term_size s + term_size s' < term_size t + term_size t'.

Definition Smaller_bs (cs cs' bs bs': list Binding) : Prop :=
  length cs + length cs' < length bs + length bs'.

Definition Smaller_t_bs (t t' : Term) (bs bs' : list Binding) :=
  term_size t + term_size t' < bindings_size bs + bindings_size bs'.

Definition Smaller_t_b (t t' : Term) (b b' : Binding) :=
  term_size t + term_size t' < binding_size b + binding_size b'.

Lemma size_non_zero : forall t, term_size t > 0.
  induction t; compute; intuition.
Qed.


(*Prove that structural subterms are smaller in size*)
Lemma let_struct : forall r bs t, term_size t < term_size (Let r bs t).
Proof. intros r bs t. rewrite fold_reduce_let. simpl. intuition. Qed.

Lemma app_struct_l : forall s t, term_size s < term_size (Apply s t).
  compute; intuition.
Qed.

Lemma app_struct_r : forall s t, term_size t < term_size (Apply s t).
Proof. intros s t. rewrite fold_reduce_apply. simpl. intuition. Qed.

Lemma tyabs_struct : forall n k t, term_size t < term_size (TyAbs n k t).
Proof. intros n k t. rewrite fold_reduce_tyabs. simpl. intuition. Qed.

Lemma lamabs_struct : forall n ty t, term_size t < term_size (LamAbs n ty t).
Proof. intros n k t. rewrite fold_reduce_lamabs. simpl. intuition. Qed.

Lemma tyinst_struct : forall t ty, term_size t < term_size (TyInst t ty).
Proof. intros t ty. rewrite fold_reduce_tyinst. simpl. intuition. Qed.

Lemma iwrap_struct : forall ty1 ty2 t, term_size t < term_size (IWrap ty1 ty2 t).
Proof. intros ty1 ty2 t. rewrite fold_reduce_iwrap. simpl. intuition. Qed.

Lemma unwrap_struct : forall t, term_size t < term_size (Unwrap t).
Proof. intros t. rewrite fold_reduce_unwrap. simpl. intuition. Qed.

Lemma termbind_struct s v t :  term_size t < binding_size (TermBind s v t).
Proof. rewrite fold_reduce_termbind. simpl. intuition. Qed.

Lemma bind_binds_struct b bs : binding_size b < bindings_size (b :: bs).
Proof. unfold bindings_size, Folds.foldBindingsUse, Folds.foldBindings. simpl. intuition. Qed.


(* Sum of two sizes decrease*)
Definition plus_lt_r : forall n m p : nat, n < m -> n + p < m + p :=
  Plus.plus_lt_compat_r.

Definition plus_lt_l : forall n m p : nat, n < m -> p + n < p + m :=
  Plus.plus_lt_compat_l.

Definition plus_lt_lr : forall n m p q : nat, n < m -> p < q -> n + p < m + q :=
  Plus.plus_lt_compat.
