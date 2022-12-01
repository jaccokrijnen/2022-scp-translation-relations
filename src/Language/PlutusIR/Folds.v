From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Strings.String.
From PlutusCert Require Import
  Util
  Language.PlutusIR.

Import NamedTerm.

Set Implicit Arguments.


(*
Algebra for the AST types.
This can probably be generated as a mutual recursion scheme
*)
Section Algebras.
  Context (rTerm rBinding rBindings : Type).

Record AlgTerm: Type := mkTermAlg
  { a_Let      : Recursivity -> rBindings -> rTerm -> rTerm
  ; a_Var      : name -> rTerm
  ; a_TyAbs    : tyname -> Kind -> rTerm -> rTerm
  ; a_LamAbs   : name -> Ty -> rTerm -> rTerm
  ; a_Apply    : rTerm -> rTerm -> rTerm
  ; a_Constant : @some valueOf -> rTerm
  ; a_Builtin  : DefaultFun -> rTerm
  ; a_TyInst   : rTerm -> Ty -> rTerm
  ; a_Error    : Ty -> rTerm
  ; a_IWrap    : Ty -> Ty -> rTerm -> rTerm
  ; a_Unwrap   : rTerm -> rTerm
  }

with AlgBinding : Type := mkBindingAlg
  { a_TermBind     : Strictness -> VDecl -> rTerm -> rBinding
  ; a_TypeBind     : TVDecl -> Ty -> rBinding
  ; a_DatatypeBind : DTDecl -> rBinding
  }

with AlgBindings : Type := mkBindingsAlg
  { a_cons : rBinding -> rBindings -> rBindings
  ; a_nil  : rBindings
  }.

End Algebras.

Print Visibility.



(* Composition of algebras: products *)

(* Shorthand for type signature of a product *)
Definition algProd (alg : Type -> Type) :=
  forall {a b},  alg a -> alg b -> alg (a * b)%type. (* type scope is not inferred because alg is not yet typed *)

Definition algBindingProd {rTerm rBindings} : algProd (fun x => AlgBinding rTerm x rBindings) :=
  fun _ _ a1 a2 =>
    {| a_TermBind     := fun s v t => (a_TermBind a1 s v t , a_TermBind a2 s v t)
    ;  a_TypeBind     := fun tv ty => (a_TypeBind a1 tv ty , a_TypeBind a2 tv ty)
    ;  a_DatatypeBind := fun dt    => (a_DatatypeBind a1 dt, a_DatatypeBind a2 dt)
    |}.


Section Folds.

  Context {rt rb rbs : Type}. (* Algebra return types *)
  Context (algTerm     : AlgTerm     rt rb rbs).
  Context (algBinding  : AlgBinding  rt rb rbs).
  Context (algBindings : AlgBindings rt rb rbs).


  (* See note [Structural Recursion Checker] *)
  Definition foldBindings (foldBinding : Binding -> rb) (bs : list Binding) : rbs :=
    fold_right (a_cons algBindings) (a_nil algBindings) (map foldBinding bs)
  .

  Fixpoint foldTerm (t : Term) : rt := match t with
    | (Let rec bs t)    => a_Let algTerm rec (foldBindings foldBinding bs) (foldTerm t)
    | (Var n)           => a_Var algTerm n
    | (TyAbs n k t)     => a_TyAbs algTerm n k (foldTerm t)
    | (LamAbs n ty t)   => a_LamAbs algTerm n ty (foldTerm t)
    | (Apply s t)       => a_Apply algTerm (foldTerm s) (foldTerm t)
    | (Constant v)      => a_Constant algTerm v
    | (Builtin f)       => a_Builtin algTerm f
    | (TyInst t ty)     => a_TyInst algTerm (foldTerm t) ty
    | (Error ty)        => a_Error algTerm ty
    | (IWrap ty1 ty2 t) => a_IWrap algTerm ty1 ty2 (foldTerm t)
    | (Unwrap t)        => a_Unwrap algTerm (foldTerm t)
  end

  with foldBinding (b : Binding) : rb := match b with
    | (TermBind s v t)  => a_TermBind algBinding s v (foldTerm t)
    | (TypeBind tv ty)  => a_TypeBind algBinding tv ty
    | (DatatypeBind dt) => a_DatatypeBind algBinding dt
    end
.

(*
Note [Structural recursion]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

I'd like to write/generate a separate definition for the fold
on bindings:

  with foldBindings (bs : list Binding) : rbs := match bs with
    | cons b bs => a_cons algBs (foldBinding b) (foldBindings bs)
    | nil       => a_nil algBs
    end.

which is effectively an unfolded version of the expression in
fold_Term:

  fold_right (a_cons algBs) (a_nil algBs) (map foldBinding bs)

however, Coq doesn't allow it because it the | cons b bs branch
makes two recursive calls: (foldBinding b) and (foldBindings bs).
The first is not considered a proper recursive call:

  Recursive call to foldBinding has principal argument equal to
  "b" instead of "bs".

Apparently it expects that recursive calls (to any of the mutual
recursive functions in the group) use bs. This seems to be
contradicted though by the last example in

  https://coq.inria.fr/refman/language/core/inductive.html#top-level-recursive-functions

But that example works because it rolls its own list type. Whereas in our case `list
binding` is not part of the mutually recursively defined data structure.

A work-around could be to redefine a list type, specialized to
Binding as its elements.

Coq'Art mentions on p404/405 a nested fix, and how Coq determines that it is
structurally recursive. It seems that nowadays Coq's analysis is a bit smarter,
since we are allowed to pass the function to fold_right (it's not syntactically
a structurally recursive call!). <Is this a "polyvariant" analysis? See APA
slides. Or is Coq just inlining my fixpoint definition? Jur told me that Helium
does some polyvariant analyses, whereas GHC uses monovariant analyses by doing
inlining>

However! The analysis can fail when the function is passed in a different order:

(example from PlutusIR.v, I was writing a boolean equality on Terms)

Fixpoint Term_eqb (x y : Term) {struct x} : bool := match x, y with
  | Let rec bs t, Let rec' bs' t' =>
    ...
      && list_eqb Binding_eqb bs bs' (* Nested fix*)
        && ...

Now, this definition works:

  Definition list_eqb' a (eqb : a -> a -> bool): list a -> list a -> bool := fix f xs ys :=
    match xs, ys with
    | nil, nil             => true
    | cons x xs, cons y ys => eqb x y && f xs ys
    | _, _                 => false
    end.


But this one didn't!

  Definition list_eqb a : (a -> a -> bool) -> list a -> list a -> bool := fix f eqb xs ys :=
    match xs, ys with
    | nil, nil             => true
    | cons x xs, cons y ys => eqb x y && f eqb xs ys
    | _, _                 => false
    end.

and this third one doesn't either

  Fixpoint list_eqb a (eqb : a -> a -> bool) (xs : list a) (ys : list a) : bool :=
    match xs, ys with
    | nil, nil             => true
    | cons x xs, cons y ys => eqb x y && list_eqb eqb xs ys
    | _, _                 => false
    end.

The difference is minor, but the first Definition generates
  fun _ eqb => fix f xs ys => ...
and the second:
  fun _ => fix f eqb xs ys => ...


Another strange situation, I couldn't get this to work:

Fixpoint Term_desugar (x y : Term) {struct x} : bool := match x, y with
  | Let NonRec bs body, t =>
      (fix Bindings_desugar
        (bs : list Binding) (t : Term) {struct bs} := match bs with
        | nil       => Term_desugar body t
        | cons b bs => match b, t with
          | TermBind Strict v t, Apply (LamAbs v' tt body') t' =>
            ... && Bindings_desugar bs body body'
          | _, _ => false
          end
        end) bs body t

It has trouble spotting that the argument `body` is passed unchanged in the
recursive calls, so `Term_desugar body t` is rejected as a valid recursive
call since it can't see that it's always structurally smaller.
The solution was easy, just don't pass body to the nested fix:

Fixpoint Term_desugar (x y : Term) {struct x} : bool := match x, y with
  | Let NonRec bs body, t =>
      (fix Bindings_desugar
        (bs : list Binding) (t : Term) {struct bs} := match bs with
        | nil       => Term_desugar body t
        | cons b bs => match b, t with
          | TermBind Strict v rhs, Apply (LamAbs v' _ body') rhs' =>
            ... && Bindings_desugar bs body'
          | _, _ => false
          end
        end) bs t

Listen todo: Non-composibility of termination syntactic structural recursion checks
(Iowa type theory commute)
*)


  (* Call tree of a fold *)
  (*
  Generalizable All Variables.

  Inductive FoldTerm : Term -> a -> Type :=
    | FoldTerm_Let      : `{ FoldTerm t r                     -> FoldTermBindings bs rs ->
                                                                 FoldTerm (Let rec bs t)    (A_Let alg rec rs r)}
    | FoldTerm_Var      : `{                                     FoldTerm (Var n)           (A_Var alg n)}
    | FoldTerm_TyAbs    : `{ FoldTerm t r                     -> FoldTerm (TyAbs n k t)     (A_TyAbs alg n k r)}
    | FoldTerm_LamAbs   : `{ FoldTerm t r                     -> FoldTerm (LamAbs n ty t)   (A_LamAbs alg n ty r)}
    | FoldTerm_Apply    : `{ FoldTerm s r_s -> FoldTerm t r_t -> FoldTerm (Apply s t)       (A_Apply alg r_s r_t)}
    | FoldTerm_Constant : `{                                     FoldTerm (Constant v)      (A_Constant alg v)}
    | FoldTerm_Builtin  : `{                                     FoldTerm (Builtin f)       (A_Builtin alg f)}
    | FoldTerm_TyInst   : `{ FoldTerm t r                     -> FoldTerm (TyInst t ty)     (A_TyInst alg r ty)}
    | FoldTerm_Error    : `{                                     FoldTerm (Error ty)        (A_Error alg ty)}
    | FoldTerm_IWrap    : `{ FoldTerm t r                     -> FoldTerm (IWrap ty1 ty2 t) (A_IWrap alg ty1 ty2 r)}
    | FoldTerm_Unwrap   : `{ FoldTerm t r                     -> FoldTerm (Unwrap t)        (A_Unwrap alg r)}

  with FoldBindings : list Binding -> list b -> Type :=
    | Fold_Cons : `{ FoldBinding x r -> FoldBindings xs rs -> FoldBindings (x :: xs) (r :: rs) }
    | Fold_Nil  : FoldBindings nil nil

  with FoldBinding : Binding -> b -> Type :=
    | Fold_TermBind     : `{ FoldTerm t r -> FoldBinding (TermBind s v t) (A_TermBind algB s v r)}
    | Fold_TypeBind     : `{             FoldBinding (TypeBind tv ty) (A_TypeBind algB tv ty)}
    | Fold_DatatypeBind : `{             FoldBinding (DatatypeBind dt) (A_DatatypeBind algB dt)}
    .

Axiom folds_equal : forall rT rB (aTerm : AlgTerm rT rB) (aBind : algBinding rT rB) t t',
  foldTerm aTerm aBind t = t' -> FoldTerm aTerm aBind t t'.

  *)


End Folds.


Section Use. (* name comes from "use" rules in attribute grammars *)

  (*
  Specific folds that compute a value of type `a` by combining the subtree
  results with a function of type `list a -> a`.

  All three of the mutually recursive datatypes have to produce the same type a.
  *)

  Context {a : Type} (f : list a -> a).
  Definition useAlg : AlgTerm a a a.
  refine (
    {|
    a_Let := fun (_ : Recursivity) (rBs : a) (r : a) => f [rBs; r];
    a_Var := fun _ : name => f nil ;
    a_TyAbs := fun (_ : tyname) (_ : Kind) (X : a) => f [X];
    a_LamAbs := fun (_ : name) (_ : Ty) (X : a) => f [X];
    a_Apply := fun X X0 : a => f [X; X0];
    a_Constant := fun _ : @some valueOf => f [];
    a_Builtin := fun _ : DefaultFun => f [];
    a_TyInst := fun (X : a) (_ : Ty) => f [X];
    a_Error := fun _ : Ty => f [];
    a_IWrap := fun (_ _ : Ty) (X : a) => f [X];
    a_Unwrap := fun X : a => f [X]
    |}
    ).
  Defined.

  Definition useAlgBinding : AlgBinding a a a :=
    {|
    a_TermBind := fun (_ : Strictness) (_ : VDecl) (X : a) => f [X];
    a_TypeBind := fun (_ : TVDecl) (_ : Ty) => f [];
    a_DatatypeBind := fun _ : DTDecl => f []
    |}
    .

  Definition useAlgBindings : AlgBindings a a a :=
    {|
    a_nil := f [];
    a_cons := fun rx rxs => f [rx; rxs]
    |}.

  Definition foldTermUse (t : Term) : a :=
    foldTerm useAlg useAlgBinding useAlgBindings t.

  Definition foldBindingUse (b : Binding) : a :=
    foldBinding useAlg useAlgBinding useAlgBindings b.

  Definition foldBindingsUse (bs : list Binding) : a :=
    foldBindings useAlgBindings foldBindingUse bs.
End Use.

Section Attributes.
(*

Inductive Attr : string -> Type -> Type :=
  attr : forall str ty, Attr str ty.

Definition AttrVals : list Attr -> Type :=
  av

Definition getAttr : Attr -> list Attr ->
*)
End Attributes.

  (* TODO express that Fold is a functional relation, and a decision
  procedure how to always produce a proof *)
  (*
  Fixpoint fold_defined (t : Term) : sigT (fun r => Fold t r) :=
    match t with (*TODO:use return syntax?*)
      | Let rec bs t => _ (projT2 (fold_defined t))
      (* | Let rec bs t => existT (A_Let alg rec bs  (Fold_Let (proj2_sig (fold_defined t))))*)
      | _ => _
    end.
      | Var      => name -> Term
      | TyAbs    => tyname -> Kind -> Term -> Term
      | LamAbs   =>  name -> Ty -> Term -> Term
      | Apply    =>  Term -> Term -> Term
      | Constant =>  some -> Term
      | Builtin  =>  func -> Term
      | TyInst   =>  Term -> Ty -> Term
      | Error    =>  Ty -> Term
      | IWrap    =>  Ty -> Ty -> Term -> Term
      | Unwrap   =>  Term -> Term
    end.
   *)


(*
Idea: use a separate type for the names of constructors, and a dependent type
to express the type of fold for that constructor.

attributes can then be defined per constructor, perhaps it is useful to receive the
fields as a records instead of separate arguments.
*)

Inductive con_term :=
  | con_Let
  | con_Var
  | con_TyAbs
  | con_LamAbs
  | con_Apply
  | con_Constant
  | con_Builtin
  | con_TyInst
  | con_Error
  | con_IWrap
  | con_Unwrap
  .

Definition con_type (v v' b b': Set) P Q : con_term -> Type :=
  fun c => match c with
    | con_Let       => forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t)
    | con_Var       => forall s : v, P (Var s)
    | con_TyAbs     => forall (s : b') (k : kind) (t : term v v' b b'), P t -> P (TyAbs s k t)
    | con_LamAbs    => forall (s : b) (t : ty v' b') (t0 : term v v' b b'), P t0 -> P (LamAbs s t t0)
    | con_Apply     => forall t : term v v' b b', P t -> forall t0 : term v v' b b', P t0 -> P (Apply t t0)
    | con_Constant  => forall s : @some valueOf, P (Constant s)
    | con_Builtin   => forall d : DefaultFun, P (Builtin d)
    | con_TyInst    => forall t : term v v' b b', P t -> forall t0 : ty v' b', P (TyInst t t0)
    | con_Error     => forall t : ty v' b', P (Error t)
    | con_IWrap     => forall (t t0 : ty v' b') (t1 : term v v' b b'), P t1 -> P (IWrap t t0 t1)
    | con_Unwrap    => forall t : term v v' b b', P t -> P (Unwrap t)
    end.

Inductive con_binding :=
  | con_TermBind
  | con_TypeBind
  | con_DatatypeBind
  .

Definition con_type_binding (name tyname : Set) (P : term name tyname binderName binderTyname -> Type) (Q : binding name tyname binderName binderTyname -> Type) : con_binding -> Type :=
  fun c => match c with
    | con_TermBind => forall s v t, P t -> Q (TermBind s v t)
    | con_TypeBind => forall v ty, Q (TypeBind v ty)
    | con_DatatypeBind => forall dtd, Q (DatatypeBind dtd)
    end.

(*
Eval cbv in (forall v P Q, con_type v P Q con_TyAbs).

Definition collect (a : Type) v : forall (c : con_term), con_type v (fun _ => list a) (fun _ => list a) c.
Proof.
  refine (
  fun c => match c as p return con_type _ (fun _ => list a) (fun _ => list a) p with
  | con_Let      => fun _ _ _ rec bs t rs r_body => _  (* r_body (* todo: include rs *) *)
  | con_Var      => fun _ _ _ s                  => _
  | con_TyAbs    => fun _ _ _ s k t r            => _  (* r *)
  | con_LamAbs   => fun _ _ _ s ty t r           => _  (* r *)
  | con_Apply    => fun _ _ _ t1 r1 t2 r2        => _  (* r1 (* todo: r2 *) *)
  | con_Constant => fun _ _ _ s                  => _
  | con_Builtin  => fun _ _ _ f                  => _
  | con_TyInst   => fun _ _ _ t r ty             => _  (* r *)
  | con_Error    => fun _ _ _ ty                 => _
  | con_IWrap    => fun _ _ _ ty1 ty2 t r        => _  (* r *)
  | con_Unwrap   => fun _ _ _ t r                => _  (* r *)
  end).



*)
