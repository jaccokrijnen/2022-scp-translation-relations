Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.


Fixpoint lookup {X:Type} (k : string) (l : list (string * X)) : option X :=
  match l with
  | nil => None
  | (j,x) :: l' => if j =? k then Datatypes.Some x else lookup k l'
  end.

Inductive Lookup {A B :Type} (k : A) (v : B) : list (A * B) -> Prop :=
  | Here    : forall {kvs}, Lookup k v ((k, v) :: kvs)
  | There   : forall {k' v' kvs}, ~ (k = k') -> Lookup k v kvs -> Lookup k v ((k', v') :: kvs)
.

Lemma Lookup_lookup : forall A k (v : A) kvs, Lookup k v kvs <-> lookup k kvs = Some v.
Admitted.

Lemma Lookup_functional : forall A B (k : A) (v v' : B) kvs,  Lookup k v kvs -> Lookup k v' kvs -> v = v'.
Admitted.

Lemma Lookup_unique : forall A B (k : A) (v : B) kvs (P P' : Lookup k v kvs), P = P'.
Admitted.

Lemma Lookup_In : forall A B (k : A) (v : B) kvs, NoDup kvs -> In (k, v) kvs <-> Lookup k v kvs.
Admitted.

Fixpoint drop {X:Type} (n:string) (nxs:list (string * X)) : list (string * X) :=
  match nxs with
  | nil => nil
  | (n',x) :: nxs' => if n' =? n then drop n nxs' else (n',x) :: (drop n nxs')
  end.

Fixpoint mdrop {X:Type} (ns : list string) (nxs: list (string * X)) : list (string * X) :=
  match ns with
  | nil => nxs
  | n :: ns' =>
      mdrop ns' (drop n nxs) 
  end.

Definition forall2b {A} (p : A -> A -> bool) := fix f xs ys :=
  match xs, ys with
    | []       , []        => true
    | (x :: xs), (y :: ys) => (p x y && f xs ys)%bool
    | _        , _         => false
  end.




Lemma mdrop_nil : forall X ns,
    @mdrop X ns nil = nil.
Proof. induction ns; auto. Qed.
