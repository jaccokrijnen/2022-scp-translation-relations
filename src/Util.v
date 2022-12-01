Require Import String.
Require Import List.
Require Import PeanoNat.
Require Import Program.Basics.
Set Implicit Arguments.
Import ListNotations.



Section list_rect'.
  Variable (a : Type).
  Variable (res_a : a -> Type).
  Variable (res_list : list a -> Type).

  Context
    (H_cons         : forall x xs, res_a x -> res_list xs -> res_list (x :: xs))
    (H_nil          : res_list nil).

Definition list_rect' (elem_rect': forall (x : a), res_a x) :=
  fix list_rect' xs :=
  match xs return res_list xs with
    | nil       => @H_nil
    | cons x xs => @H_cons x xs (elem_rect' x) (list_rect' xs)
  end.
End list_rect'.

(* Type equivalent of Forall *)
Inductive ForallT (A : Type) (P : A -> Type) : list A -> Type :=
  | ForallT_nil : ForallT P nil
  | ForallT_cons : forall {x : A} {l : list A},
                  P x -> ForallT P l -> ForallT P (x :: l).
Arguments ForallT_nil {_} {_}.
Arguments ForallT_cons {_} {_} {_} {_}.
Hint Constructors ForallT : core.

Definition ForallT_uncons {A P} {x : A} {xs} : ForallT P (x :: xs) -> (P x * ForallT P xs) :=
  fun ps => match ps with
    | ForallT_cons p ps => (p, ps)
  end.

Definition ForallT_hd {A P} {x : A} {xs} : ForallT P (x :: xs) -> P x :=
  fun ps => match ps with
    | ForallT_cons p _ps => p
  end.

Definition ForallT_tl {A P} {x : A} {xs} : ForallT P (x :: xs) -> ForallT P xs :=
  fun ps => match ps with
    | ForallT_cons p ps => ps
  end.

(* ForallT for Props *)  
Inductive ForallP (A : Type) (P : A -> Prop) : list A -> Prop :=
  | ForallP_nil : ForallP P nil
  | ForallP_cons : forall {x : A} {l : list A},
                  P x -> ForallP P l -> ForallP P (x :: l).
Arguments ForallP_nil {_} {_}.
Arguments ForallP_cons {_} {_} {_} {_}.
#[export] Hint Constructors ForallP : core.

Definition ForallP_uncons {A P} {x : A} {xs} : ForallP P (x :: xs) -> (P x * ForallP P xs) :=
  fun ps => match ps with
    | ForallP_cons p ps => (p, ps)
  end.

Definition ForallP_hd {A P} {x : A} {xs} : ForallP P (x :: xs) -> P x :=
  fun ps => match ps with
    | ForallP_cons p _ps => p
  end.

Definition ForallP_tl {A P} {x : A} {xs} : ForallP P (x :: xs) -> ForallP P xs :=
  fun ps => match ps with
    | ForallP_cons p ps => ps
  end.


(* Todo, remove ForallP *)
Lemma ForallP_Forall : forall A P (xs : list A), ForallP P xs <-> Forall P xs.
Proof with eauto using Forall.
  intros.
  split; intros.
  - induction xs...
    inversion H...
  - induction xs...
    inversion H...
Qed.


(* Prove P or Q depending on x *)
Definition sumboolOut (P Q : Prop) (x : {P} + {Q}) :=
  match x return (if x then P else Q) with
    | left x  => x
    | right x => x
  end
.

(* Prove P or unit *)
Definition optionOut (P : Prop) (x : option P) :=
  match x return (if x then P else unit) with
    | Datatypes.Some x => x
    | None             => tt
  end.


(* Applicative combinators for option type *)
Definition option_app (a b : Type): option (a -> b) -> option a -> option b :=
  fun mf mx => match mf, mx with
    | Datatypes.Some f, Datatypes.Some x => Datatypes.Some (f x)
    | _, _ => None
    end.

Notation "'Nothing'" := None.
Notation "'Just'"    := Datatypes.Some.

Definition pure {a : Type} : a -> option a := @Datatypes.Some a.
Definition option_alt a : option a-> option a-> option a :=
  fun x y => if x then x else y.

Notation "x <*> y" := (option_app x y) (at level 81, left associativity).
Notation "f <$> x" := (option_map f x) (at level 80, right associativity).
Notation "x <|> y" := (option_alt x y) (at level 82, right associativity).

Definition sequence_options {a} : list (option a) -> option (list a) :=
  fun os => fold_right (fun mx mxs => cons <$> mx <*> mxs) (pure nil) os.

Fixpoint cat_options {a} (xs : list (option a)) : (list a) :=
  match xs with
    | nil            => nil
    | (Some x) :: xs => x :: cat_options xs
    | None     :: xs => cat_options xs
    end.


(* sumbool to bool *)
Definition sumbool_to_bool (A : Type) (a b : A) : {a = b} + {a <> b} -> bool
  := fun sb => match sb with
  | left _ => true
  | right _ => false
  end
  .
(* sumbool to option *)
Definition sumbool_to_optionl {a b} (x : sumbool a b) : option a :=
  match x with
    | left p => Datatypes.Some p
    | _      => None
  end.

Definition sumbool_to_optionr {a b} (x : sumbool a b) : option b :=
  match x with
    | right p => Datatypes.Some p
    | _       => None
  end.


Definition string_dec_option := fun x y => sumbool_to_optionl (string_dec x y).

(* lookup with evidence *)
Definition lookup {a b} (dec : forall x1 x2 : a, {x1 = x2} + {x1 <> x2}) :
  forall (x : a) (xs : list (a * b)),
  option ({y & In (x, y) xs}).
  Proof.
  induction xs as [ | p ps ].
  - exact Nothing.
  - refine (match p as x return x = p -> _ with
      | (x', y) => fun H =>
        match dec x x' with
          | left eq => Just (existT _ y _)
          | right _ => _ IHps
        end
      end eq_refl
  ); subst.
  { unfold In. tauto. }
  { refine (fun IH => _ <$> IH).
    destruct 1 as [r in_ps].
    exists r. unfold In in *. tauto.
  }
Defined.

Eval cbv in lookup Nat.eq_dec 3 [(1, 2); (3, 4)].

(* decision functions that return option instead of sumbool *)

Definition in_dec_option (x : string) (xs : list string) : option (~(In x xs)) :=
  match in_dec string_dec x xs with
  | left _      => None
  | right proof => Just proof
  end.

Definition negneg : forall (p : Prop), p -> ~~p :=
  fun _ proof f => f proof.

Definition map_right {a b c : Prop} : (b -> c) -> sumbool a b -> sumbool a c :=
  fun f e => match e with
    | right x => right (f x)
    | left  x => left x
    end
    .

(* The conclusion has double negation so I can
   use it for things like Forall (lam x => ~In x ys) xs*)
Definition notIn_dec {a} : forall
  (H : forall (x y : a), {x = y} + {x <> y})
  (x : a)
  (xs : list a), {~ In x xs} + {~~In x xs}.
Proof.
  intros. refine (_ (in_dec H x xs)).
  intros.
  apply Sumbool.sumbool_not in x0.
  refine ((fun nn => _) (negneg (p := In x xs))).
  apply (map_right (negneg (p := In x xs))) in x0.
  assumption.
Qed.
(* Proof search for ~(In x xs). Better to use in_dec instead *)
Ltac notIn := intros H; simpl in H; repeat (destruct H as [l | H]; [try (inversion l) | ]); assumption.

Ltac notIn2 :=
  match goal with
    | [ |- ~(In ?x ?xs)] => exact (sumboolOut (in_dec string_dec x xs))
  end.

Lemma existsb_nexists : forall {A : Type} l (f : A -> bool),
    existsb f l = false <-> ~ exists x, In x l /\ f x = true.
Proof.
  intros.
  split.
  - intros.
    intros Hcon.
    apply existsb_exists in Hcon.
    rewrite H in Hcon.
    discriminate.
  - intros.
    induction l.
    + simpl.
      reflexivity.
    + simpl.
      destruct (f a) eqn:Hf.
      * exfalso.
        apply H.
        exists a.
        split. left. auto. auto.
      * simpl.
        eapply IHl.
        intros Hcon.
        eapply H.
        destruct Hcon as [x [HIn Hfx]].
        exists x.
        split. right. auto. auto.
Qed.

Definition remove_list {A} (dec : forall x y, {x = y} + {x <> y}) : list A -> list A -> list A :=
  fun rs xs => fold_right (remove dec) xs rs.

Fixpoint remove_eqb {a} a_eqb xs : list a :=
  match xs with
    | nil => nil
    | x :: xs => if a_eqb x : bool then remove_eqb a_eqb xs else x :: remove_eqb a_eqb xs
  end
  .

Definition is_cons {A} (xs : list A) : Prop := exists y ys, xs = y :: ys.

Definition zip := combine.
Arguments zip {A B}%type_scope (_ _)%list_scope.
Definition unzip := split.
Arguments unzip {A B}%type_scope (_)%list_scope.

Definition zip_with {A B C} (f : A -> B -> C) : list A -> list B -> list C :=
  fun xs ys => map (uncurry f) (zip xs ys).

Notation " g ∘ f " := (compose g f)
  (at level 40, left associativity).
