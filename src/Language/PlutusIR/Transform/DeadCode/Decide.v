From Coq Require Import
  String
  List
  Bool
  Program
  Utf8_core
.

From PlutusCert Require Import
  Language.PlutusIR
  Util
  Analysis.UniqueBinders
  Analysis.Purity
  Analysis.Equality
  Transform.Compat
  Transform.DeadCode
.

Import NamedTerm.
Import ListNotations.

Section Bindings.

  Context (dec_elim_Term : Term -> Term -> bool).

  Definition dec_elim_Binding (b b' : Binding) : bool := match b, b' with
    | TermBind s vd t, TermBind s' vd' t' => Strictness_eqb s s' && VDecl_eqb vd vd' && dec_elim_Term t t'
    | b, b' => Binding_eqb b b'
    end.

  Definition dec_removed b bs' :=
    if negb (existsb (String.eqb (name_Binding b)) bs')
      then dec_pure_binding [] b
      else true.

  Definition dec_was_present b' bs : bool :=
    match find (λ b, String.eqb (name_Binding b) (name_Binding b')) bs with
      | Datatypes.Some b => dec_elim_Binding b b'
      | None => false
    end
  .

  (* inlined and specialized `find` for termination checking *)
  Definition find_Binding b' :=
  fix find (bs : list Binding) : bool :=
    match bs with
    | []      => false
    | b :: bs => if String.eqb (name_Binding b) (name_Binding b') then dec_elim_Binding b b' else find bs
    end.

  Definition dec_elim_Bindings (bs bs' : list Binding) : bool :=
    let bsn := map name_Binding bs in
    let bs'n := map name_Binding bs' in
    forallb (fun b => dec_removed b bs'n) bs &&
    forallb (fun b' => find_Binding b' bs) bs'.

End Bindings.

Fixpoint dec_elim_Term (x y : Term) {struct x} : bool := match x, y with

  | Let r bs t   , Let r' bs' t' => 
      if dec_elim_Bindings dec_elim_Term bs bs'
      then (* same let block, but bindings were removed *)
        Recursivity_eqb r r' && dec_elim_Term t t'
      else (* t' is another let block, the whole block in the pre-term was removed *)
        forallb (dec_pure_binding []) bs && dec_elim_Term t y (* Check whether the whole let was removed *)
  | Let _ bs t   , _ => 
     forallb (dec_pure_binding []) bs && dec_elim_Term t y (* Check whether the whole let was removed *)
  | _ , _ => dec_compat dec_elim_Term x y

  end
.


