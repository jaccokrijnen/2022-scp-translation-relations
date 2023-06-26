From Coq Require Import
  Strings.String
  Lists.List
  Bool.Bool
  Arith.PeanoNat
.

From PlutusCert Require Import
  Language.PlutusIR
  Util.List
  Equality
  .

Import NamedTerm.
Import PeanoNat.Nat.

(** ** Arity of built-in functions *)
Definition arity (df : DefaultFun) : nat :=
  match df with
  | AddInteger => 2
  | SubtractInteger => 2
  | MultiplyInteger => 2
  | DivideInteger => 2
  | QuotientInteger => 2
  | RemainderInteger => 2
  | ModInteger => 2
  | LessThanInteger => 2
  | LessThanEqInteger => 2
  | GreaterThanInteger => 2
  | GreaterThanEqInteger => 2
  | EqInteger => 2
  | Concatenate => 2
  | TakeByteString => 2
  | DropByteString => 2
  | SHA2 => 1
  | SHA3 => 1
  | VerifySignature => 3
  | EqByteString => 2
  | LtByteString => 2
  | GtByteString => 2
  | IfThenElse => 4
  | CharToString => 1
  | Append => 2
  | Trace => 1
  end.



Inductive is_error : Term -> Prop :=
  | IsError : forall T,
      is_error (Error T).

Inductive value : Term -> Prop :=
  | V_LamAbs : forall x T t0,
      value (LamAbs x T t0) 
  | V_TyAbs : forall X K t,
      value (TyAbs X K t)
  | V_IWrap : forall F T v,
      value v ->
      ~ is_error v ->
      value (IWrap F T v)
  | V_Constant : forall u,
      value (Constant u)
  | V_Error : forall T,
      value (Error T)
  (** Builtins *) 
  | V_Neutral : forall nv,
      neutral_value 0 nv ->
      value nv

with neutral_value : nat -> Term -> Prop :=
  | NV_Builtin : forall n f,
      n < arity f ->
      neutral_value n (Builtin f)
  | NV_Apply : forall n nv v,
      value v ->
      ~ is_error v ->
      neutral_value (S n) nv ->
      neutral_value n (Apply nv v)
  | NV_TyInst : forall n nv T,
      neutral_value (S n) nv ->
      neutral_value n (TyInst nv T)
  .

#[export] Hint Constructors value : core.
#[export] Hint Constructors neutral_value : core.

Scheme value__ind := Minimality for value Sort Prop
  with neutral_value__ind := Minimality for neutral_value Sort Prop.

Combined Scheme value__multind from 
  value__ind,
  neutral_value__ind.

Definition neutral (t : Term) := neutral_value 0 t.

#[export] Hint Unfold neutral : core.
Definition is_error_b (t : Term) :=
  match t with
    | Error T => true
    | _       => false
  end.

Lemma is_error_is_error_b : forall t, is_error_b t = true -> is_error t.
Proof.
  intros t H.
  destruct t; inversion H.
  constructor.
Qed.

Fixpoint
  dec_value' (n : nat) (t : Term) {struct t} :=
  match t with
    | LamAbs x T t0 => true
    | TyAbs X K t   => true
    | IWrap F T v   => dec_value' n v && negb (is_error_b v)
    | Constant u    => true
    | Error T       => true

    (* neutral terms *)
    | Builtin f   => ltb n (arity f)
    | Apply nv v  => dec_value' n v && negb (is_error_b v) && dec_value' (S n) nv
    | TyInst nv T => dec_value' (S n) nv
    | _ => false
  end
  .

Definition dec_value := dec_value' 0.

Definition dec_neutral_value (n : nat) (t : Term) :=
  match t with
    | Builtin f   => dec_value' n t
    | Apply nv v  => dec_value' n t
    | TyInst nv T => dec_value' n t
    | _           => false
  end.

Lemma dec_value_value : forall t,
  (dec_value t = true -> value t) /\
  (forall n, dec_neutral_value n t = true -> neutral_value n t).
Proof.
(*
  intros t.
  induction t.
  all: split.
  all: try destruct IHt.
  all: match goal with
    | H : _ |- dec_value _ = true -> _ => intro H_dec; auto; inversion H_dec
    | _ => idtac
  end.
  - 
  - 
  all: auto; inversion H_dec.
  - clear H0.
    unfold dec_value in H_dec.
    unfold dec_value' in H_dec.
    fold dec_value' in H_dec.
    repeat (rewrite_eqbs; destruct_ands).
    apply V_Neutral.
    apply NV_Apply; auto.
*)

Admitted.

Lemma dec_neutral_value_neutral_value : forall n t, dec_neutral_value n t = true -> neutral_value n t.
Admitted.

