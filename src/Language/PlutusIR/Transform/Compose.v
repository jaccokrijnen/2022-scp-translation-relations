From Coq Require Import Lists.List.
Import ListNotations.
Set Printing Universes.
Set Polymorphic Universes.

(* Composition of multiple binary relations on the same type*)
Polymorphic Inductive compose {a} : list (a -> a -> Type) -> a -> a -> Type :=
  | ComposeCons : forall x y z R Rs, R x y -> compose Rs y z -> compose (R :: Rs) x z
  | ComposeNil  : forall x,                                     compose nil       x x.

Arguments ComposeCons {_ _ _ _ _ _}.
Arguments ComposeNil {_ _}.


(* TODO: resolve this duplication with compose above *)
Fixpoint compose_prop {a} (rs : list (a -> a -> Prop)) (x y : a) : Prop :=
  match rs with
    | r :: rs => exists x', r x x' /\ compose_prop rs x' y
    | []       => x = y
  end
.

Polymorphic Inductive hcompose {a} : forall {b : Type}, a -> b -> Type :=
  | HComposeCons : forall b c (x : a) (y : b) (z : c) (R : a -> b -> Type),
      R x y -> hcompose y z -> hcompose x z
  | HComposeNil  : forall x, hcompose x x.

Arguments HComposeCons {_ _ _ _ _ _ _}.
Arguments HComposeNil  {_ _}.
(*
Definition cat_rhs z Rs rs := match rs with
  | ComposeCons r rs => forall x', compose Rs x' z
  | ComposeNil       => unit
  end.
*)
(*
Definition depArgs : compose Rs x y -> Type :=
  
    | ComposeCons r rs' => 
    | ComposeNil  => unit
  end.
*)

(* Fixpoint cat_compose {a} {x y z : a} {Rs} (_ : compose Rs x y) := *)

Fixpoint cat_compose {a} {x y z : a} {Rs Ss : list (a -> a -> Type)}
  (rs : compose Rs x y) (ss : compose Ss y z) : compose (Rs ++ Ss) x z :=
  match rs
    in     compose Rs x y
    return compose Ss y z -> compose (Rs ++ Ss) x z
  with
    | ComposeCons r rs => fun ss => ComposeCons r (cat_compose rs ss)
    | ComposeNil       => fun ss => ss
  end ss.
