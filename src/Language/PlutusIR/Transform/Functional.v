(* A functional relation parameterized by the function *)
Inductive Functional {A B} {f : A -> B} : A -> B -> Type :=
  Mapping : forall x, Functional x (f x).
