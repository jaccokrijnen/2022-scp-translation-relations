From PlutusCert Require Import
  Language.PlutusIR
  Analysis.BoundVars.
Import NamedTerm.

Require Import
  Strings.String
  Lists.List
.

Import ListNotations.


Definition ctx := list string.

Definition tvd_name (tvd : tvdecl tyname) : tyname :=
  match tvd with
  | TyVarDecl v K => v
  end.

Reserved Notation "Δ '|-*' T" (at level 40, T at level 0).
Inductive well_scoped_Ty (Δ : ctx) : Ty -> Prop :=
  | WST_Var : forall X,
      In X Δ ->
      Δ |-* (Ty_Var X)
  | WST_Fun : forall T1 T2,
      Δ |-* T1 ->
      Δ |-* T2 ->
      Δ |-* (Ty_Fun T1 T2)
  | WST_IFix  : forall F T,
      Δ |-* T ->
      Δ |-* F ->
      Δ |-* (Ty_IFix F T)
  | WST_Forall : forall X K T,
      (X :: Δ) |-* T ->
      Δ |-* (Ty_Forall X K T)
  | WST_Builtin : forall u,
      Δ |-* (Ty_Builtin (Some (TypeIn u)))
  | WST_Lam : forall X K1 T,
      (X :: Δ) |-* T ->
      Δ |-* (Ty_Lam X K1 T)
  | WST_App : forall T1 T2,
      Δ |-* T1 ->
      Δ |-* T2 ->
      Δ |-* (Ty_App T1 T2) 
where "Δ '|-*' T " := (well_scoped_Ty Δ T).

Reserved Notation "Δ ',,' Γ '|-+' t " (at level 101, t at level 0, no associativity).
Reserved Notation "Δ '|-ok_c' c " (at level 101, c at level 0).
Reserved Notation "Δ ',,' Γ  '|-oks_nr' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Δ ',,' Γ '|-oks_r' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Δ ',,' Γ '|-ok_b' b" (at level 101, b at level 0, no associativity).

Inductive constructor_well_formed (Δ : ctx) : constructor -> Prop :=
  | W_Con : forall x T ar,
      Δ |-* T ->
      Δ |-ok_c (Constructor (VarDecl x T) ar)
  where 
    "Δ '|-ok_c' c" := (constructor_well_formed Δ c)
.

Inductive well_scoped (Δ Γ: ctx) : Term -> Prop :=
  | WS_Var : forall x,
      In x Γ ->
      Δ ,, Γ |-+ (Var x)
  | WS_LamAbs : forall x T t,
      Δ |-* T ->
      Δ ,, (x :: Γ) |-+ t ->
      Δ ,, Γ |-+ (LamAbs x T t)
  | WS_Apply : forall t1 t2,
      Δ ,, Γ |-+ t1 ->
      Δ ,, Γ |-+ t2 ->
      Δ ,, Γ |-+ (Apply t1 t2)
  (* Universal types *)
  | WS_TyAbs : forall X K t,
      (X :: Δ) ,, Γ |-+ t ->
      Δ ,, Γ |-+ (TyAbs X K t)
  | WS_TyInst : forall t T,
      Δ ,, Γ |-+ t ->
      Δ |-* T ->
      Δ ,, Γ |-+ (TyInst t T)
  | WS_IWrap : forall F T M,
      Δ |-* F ->
      Δ |-* T ->
      Δ ,, Γ |-+ M ->
      Δ ,, Γ |-+ (IWrap F T M)
  | WS_Unwrap : forall M,
      Δ ,, Γ |-+ M ->
      Δ ,, Γ |-+ (Unwrap M)
  | WS_Constant : forall u a,
      Δ ,, Γ |-+ (Constant (Some (ValueOf u a)))
  | WS_Builtin : forall f,
      Δ ,, Γ |-+ (Builtin f)
  | WS_Error : forall S,
      Δ |-* S ->
      Δ ,, Γ |-+ (Error S)
  | WS_Let : forall bs t Δ' Γ',
      Δ' = rev (btvbs bs) ++ Δ ->
      Γ' = rev (bvbs bs) ++ Γ ->
      Δ ,, Γ |-oks_nr bs ->
      Δ' ,, Γ' |-+ t ->
      Δ ,, Γ |-+ (Let NonRec bs t)
  | WS_LetRec : forall bs t Δ' Γ',
      Δ' = rev (btvbs bs) ++ Δ ->
      Γ' = rev (bvbs bs) ++ Γ ->
      Δ' ,, Γ' |-oks_r bs ->
      Δ' ,, Γ' |-+ t ->
      Δ ,, Γ |-+ (Let Rec bs t)


with bindings_well_formed_nonrec (Δ Γ : ctx) : list Binding -> Prop :=

  | W_NilB_NonRec :
    Δ ,, Γ |-oks_nr nil

  | W_ConsB_NonRec : forall b bs,
      Δ ,, Γ |-ok_b b ->
      (btvb b ++ Δ) ,, (bvb b ++ Γ) |-oks_nr bs ->
      Δ ,, Γ |-oks_nr (b :: bs)

with bindings_well_formed_rec (Δ Γ : ctx) : list Binding -> Prop :=

  | W_NilB_Rec :
      Δ ,, Γ |-oks_r nil
  | W_ConsB_Rec : forall b bs,
      Δ ,, Γ |-ok_b b ->
      Δ ,, Γ |-oks_r bs ->
      Δ ,, Γ |-oks_r (b :: bs)

with binding_well_formed (Δ Γ : ctx) : Binding -> Prop :=
  | W_Term : forall s x T t,
      Δ |-* T ->
      Δ ,, Γ |-+ t ->
      Δ ,, Γ |-ok_b (TermBind s (VarDecl x T) t)
  | W_Type : forall X K T,
      Δ |-* T ->
      Δ ,, Γ |-ok_b (TypeBind (TyVarDecl X K) T)
  | W_Data : forall X YKs cs matchFunc Δ',
      Δ' = rev (map tvd_name YKs) ++ Δ  ->
      (forall c, In c cs -> Δ' |-ok_c c) ->
      Δ ,, Γ |-ok_b (DatatypeBind (Datatype X YKs matchFunc cs))

  where "Δ ',,' Γ '|-+' t" := (well_scoped Δ Γ t)
  and "Δ ',,' Γ '|-oks_nr' bs" := (bindings_well_formed_nonrec Δ Γ bs)
  and "Δ ',,' Γ '|-oks_r' bs" := (bindings_well_formed_rec Δ Γ bs)
  and "Δ ',,' Γ '|-ok_b' b" := (binding_well_formed Δ Γ b)
.

Definition closed := well_scoped [] [].
