From PlutusCert Require Import Language.PlutusIR.

Set Implicit Arguments.

(* Relates any two terms, can be used as placeholder for to-be-defined relations *)
Inductive Universal {a : Type} : a -> a -> Type :=
  Uni : forall {x y}, Universal x y.
