Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Ascii.
Require Import Omega.
From Equations Require Import Equations.

Set Implicit Arguments.

From PlutusCert Require Import
  Language.PlutusIR
  Language.PlutusIR.Folds
  Analysis.BoundVars
  Util
.


(* Parametrized for _named_ binders (not de Bruijn) *)
Section FreeVars.
  Context
    {var tyvar : Set}
    (var_eqb : var -> var -> bool)
    .

Notation term'    := (term var tyvar var tyvar).
Notation binding' := (binding var tyvar var tyvar).



Section fvbs.

Definition delete_all : var -> list var -> list var :=
  fun x xs => filter (fun y => negb (var_eqb x y)) xs.

Fixpoint delete (x : var) (xs : list var) : list var :=
  match xs with
    | nil => nil
    | cons y ys => if var_eqb x y then ys else y :: delete x ys
  end.

Definition elem x xs := existsb (var_eqb x) xs.

Definition delete_all_many : list var -> list var -> list var :=
  fun ds xs => filter (fun x => negb (elem x ds)) xs.
(*
  Workaround for: Cannot guess decreasing argument of fix (in free_vars/free_vars_binding)
*)
Context (free_vars_binding : Recursivity -> binding' -> list var).

Fixpoint free_vars_bindings  rec (bs : list binding') : list var :=
  match rec with
    | Rec    =>
        delete_all_many (bound_vars_bindings bs) (concat (map (free_vars_binding Rec) bs))
    | NonRec =>
        match bs with
          | nil     => []
          | b :: bs => free_vars_binding NonRec b
                       ++ delete_all_many (bound_vars_binding b) (free_vars_bindings NonRec bs)
        end
  end.
End fvbs.


Fixpoint free_vars (t : term var tyvar var tyvar) : list var :=
 match t with
   | Let rec bs t => free_vars_bindings free_vars_binding rec bs ++ delete_all_many (bound_vars_bindings bs) (free_vars t)
   | (LamAbs n ty t)   => delete_all n (free_vars t)
   | (Var n)           => [n]
   | (TyAbs n k t)     => free_vars t
   | (Apply s t)       => free_vars s ++ free_vars t
   | (TyInst t ty)     => free_vars t
   | (IWrap ty1 ty2 t) => free_vars t
   | (Unwrap t)        => free_vars t
   | (Error ty)        => []
   | (Constant v)      => []
   | (Builtin f)       => []
   end

with free_vars_binding rec (b : binding') : list var :=
  match b with
    | TermBind _ (VarDecl v _) t => match rec with
      | Rec    => delete_all v (free_vars t)
      | NonRec => free_vars t
      end
    | _        => []
  end
  .

End FreeVars.

