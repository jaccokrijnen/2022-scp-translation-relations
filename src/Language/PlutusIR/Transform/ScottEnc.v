From PlutusCert Require Import
  Language.PlutusIR
  Language.PlutusIR.Transform.Congruence
  Language.PlutusIR.Analysis.FreeVars
  Language.PlutusIR.Analysis.Equality
  Folds
  Transform.Rename

.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Import Coq.Lists.List.ListNotations.

Open Scope string_scope.

Import NamedTerm.

Fixpoint encode (t : Term) : Term.
Admitted.

Definition scott_enc t t' := rename [] [] (encode t) t'.

(*
Fixpoint scottEncode (t : Term) : Term :=
  match t with
    | Let NonRec bs t   => fold_right scottBinding (scottEncode t) bs

    | Let rec bs t    => Let rec bs (scottEncode t)
    | Var n           => Var n
    | TyAbs n k t     => TyAbs n k (scottEncode t)
    | LamAbs n ty t   => LamAbs n ty (scottEncode t)
    | Apply s t       => Apply (scottEncode s) (scottEncode t)
    | Constant v      => Constant v
    | Builtin f       => Builtin f
    | TyInst t ty     => TyInst (scottEncode t) ty
    | Error ty        => Error ty
    | IWrap ty1 ty2 t => IWrap ty1 ty2 (scottEncode t)
    | Unwrap t        => Unwrap (scottEncode t)
    end

with scottBinding (b : Binding) : Term -> Term := fun t =>
  match b with
    | DatatypeBind (Datatype (TyVarDecl name k) tvs matcher constructors) =>
        let t' := fold_right (fun con t => Apply (LamAbs con tt t) (Error tt)) t constructors
        in TyInst (TyAbs name k t') tt (* No types in AST, so apply to unit *)

    | binding => Let NonRec [binding] t
  end.

*)

Fixpoint applyN {a : Type} (n : nat) : (a -> a) -> a -> a :=
  fun f x =>
  match n with
    | O => x
    | S n => applyN n f (f x)
  end.

Definition string_of_nat : nat -> string := fun n =>
  NilZero.string_of_uint (Nat.to_uint n)
  .

Fixpoint mkVars (n : nat) (prefix : string) : list string :=
  match n with
    | O   => []
    | S n => mkVars n prefix ++ [prefix ++ string_of_nat n]
  end.

Definition mkIterTyAbs  := fun tvs t => fold_right (flip (TyAbs (name := string)) tt) t tvs.
Definition mkIterLamAbs := fun vs  t => fold_right (flip (LamAbs (name := string)) tt) t vs.
Definition mkIterApp    := fun f args => fold_left (Apply (name := string)) args f.

Fixpoint index_of (c : constructor) (cs : list constructor) : option nat :=
  match cs with
    | c' :: cs' => if constructor_dec c c' then Datatypes.Some 0 else option_map S (index_of c cs')
    | nil       => None
    end
.

Definition dt_constructors (dt : DTDecl) : list constructor :=
  match dt with
    Datatype _ _ _ cs => cs
    end.

Definition tvdecl_name (tvd : TVDecl) : tyname :=
  match tvd with TyVarDecl n _ => n end.

(* Todo: (mutually) recursive types*)
Definition encode_constructor (dt : DTDecl) (c : constructor) : Term :=
  match dt, c with
    | Datatype (TyVarDecl d _) tvs _ cs
    , Constructor name arity =>
      let argVars := mkVars arity "arg_" in
      (*/\ t_1 .. t_n*)
      mkIterTyAbs (map tvdecl_name tvs)
        (* \arg_1 .. arg_n *)
        (mkIterLamAbs argVars
          (*forall out*)
          (TyAbs ("out_" ++ d) tt
            (*\case_c0 .. case_cn *)
            (mkIterLamAbs (map (fun c => "case_" ++ constructorName c) cs)
              (mkIterApp (Var ("case_" ++ constructorName c)) (map (Var (name := string)) argVars) )
            )
          )
        )
  end.

(* Todo: (mutually) recursive types*)
Definition encode_matcher (dt : DTDecl) : Term :=
  LamAbs "x" tt (Var "x")
.

(* Scott encoding written as a fold *)

(* Identity algebra*)
Definition idAlgBinding : AlgBinding Term Binding (list Binding) :=
  {| a_TermBind     := TermBind (name := string)
  ;  a_TypeBind     := TypeBind (name := string)
  ;  a_DatatypeBind := DatatypeBind (name := string)
  |}.

(* Encode DatatypeBind with scott encoding *)
Definition scottAlgBinding : AlgBinding
  Term (* Terms return Terms *)
  (Term -> Term) (* a Binding returns a function: given the term
                    built up from the next bindings,
                    wraps a LamAbs or TyAbs node for the LHS *)
  (list Binding)
  :=
  {| a_TermBind     := fun s v r => Let NonRec [TermBind s v r ]
  ;  a_TypeBind     := fun tv ty => Let NonRec [TypeBind tv ty ]
  ;  a_DatatypeBind := fun dt    =>
      match dt with
        Datatype (TyVarDecl name k) tvs matcher constructors =>
        ( fun t =>
            let lam_constructors t := fold_right (fun con => LamAbs (constructorName con) tt) t constructors in
            let lam_matcher      t := LamAbs matcher tt t in
            let abs_ty           t := TyAbs name k t in
            let app_constructors t := fold_left (fun t' con => Apply t' (encode_constructor dt con)) constructors t in (* todo: scott encode constructors*)
            let app_matcher t      := Apply t (encode_matcher dt) in (*Todo: encode scott matcher *)
            let app_ty      t      := TyInst t tt in
            app_matcher (app_constructors (app_ty
              (abs_ty (lam_constructors (lam_matcher t)))))
        )
      end
  |}.

Definition scottAlgTerm : AlgTerm Term ((Term -> Term) * Binding) (list (Term -> Term) * list Binding) :=
  {| a_Let      := fun rec rs t => match rec with
      | NonRec => fold_right apply t (fst rs)
      | _      => Let rec (snd rs) t
      end
  ;  a_Var      := Var (name := string)
  ;  a_TyAbs    := TyAbs (name := string)
  ;  a_LamAbs   := LamAbs (name := string)
  ;  a_Apply    := Apply (name := string)
  ;  a_Constant := Constant (name := string)
  ;  a_Builtin  := Builtin (name := string)
  ;  a_TyInst   := TyInst (name := string)
  ;  a_Error    := Error (name := string)
  ;  a_IWrap    := IWrap (name := string)
  ;  a_Unwrap   := Unwrap (name := string)
  |}.

(*
This doesn't typecheck anymore:

Definition scottEncode' : Term -> Term :=
  foldTerm scottAlgTerm (algBindingProd scottAlgBinding idAlgBinding).

Definition ScottEncode' : Term -> Term -> Type :=
  FoldTerm scottAlgTerm (algBindingProd scottAlgBinding idAlgBinding).

*)
