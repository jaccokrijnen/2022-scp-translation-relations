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
  Transform.DeadCode.Decide
.

Import NamedTerm.
Import ListNotations.

Definition P_Term t := forall t', dec_Term t t' = true -> dead_syn t t'.
Definition P_Binding b := forall b', dec_Binding dec_Term b b' = true -> dead_syn_binding b b'.

Ltac split_hypos :=
  match goal with
  | H : (?x && ?y)%bool = true |- _ => apply andb_true_iff in H; destruct H; split_hypos
  | _ => idtac
  end.


Lemma H_safely_removed bs bs':
    forallb (fun b => safely_removed b (map name_Binding bs')) bs = true ->
    ∀ b : Binding, In b bs → name_removed b bs' → pure_binding [] b.
Proof with eauto with reflection.
  intros H_dec.
  intros b H_In H_removed.
  unfold safely_removed in H_dec.
  rewrite forallb_forall in H_dec. (* why did rewrite accept a <-> ? was also possible with eapply -> ..., but generated an existential for x *)
  apply H_dec in H_In as H_dec_andb.
  clear H_dec H_In.

  destruct (negb
    (existsb (String.eqb (name_Binding b))
       (map name_Binding bs')))
       eqn:H_1.
  + apply is_pure_binding_pure_binding...

  (* contradiction *)
  + apply negb_false_iff in H_1.
    unfold name_removed in *.
    apply existsb_exists in H_1.
    destruct H_1 as [x [H_in H_name_b_eq_x]].
    apply String.eqb_eq in H_name_b_eq_x.
    subst.
    contradiction.
Qed.

Lemma H_find_binding' bs bs' :
  (∀ b, In b bs -> P_Binding b) ->
    forallb (fun b' => find_Binding dec_Term b' bs) bs' = true ->
    ∀ b', In b' bs' ->
       ∃ x, In x bs /\
         name_Binding x = name_Binding b' /\
         dead_syn_binding x b'
    .
Proof with eauto with reflection.
  intro H_P_Binding.
  rewrite forallb_forall.
  intros H_dec b' H_In.
  apply H_dec in H_In as H_find_b'.
  clear H_dec.
  induction bs as [ | b ].
  - discriminate H_find_b'.
  - simpl in H_find_b'.
    destruct (name_Binding b =? name_Binding b')%string
      eqn:H_name_eq.

    (* b related to b' *)
    + exists b.
      repeat split...
      * constructor...
      * assert (H : P_Binding b).
        ++ apply H_P_Binding.
           constructor...
        ++ unfold P_Binding in H...


    (* a not related to b' *)
    + apply IHbs in H_find_b' as H_ex. clear IHbs.
      * destruct H_ex as [x [H_x_In [H_eq_name H_dead_syn]]].
        assert (In x (b :: bs)). { apply in_cons... }
        exists x...
      * intros b0 H_b0_in.
        apply H_P_Binding.
        apply in_cons...
Qed.

Create HintDb Hints_bindings.
#[local]
Hint Resolve
  H_safely_removed : Hints_bindings.
#[local]
Hint Constructors
  dead_syn_bindings : Hints_bindings.
#[local]
Hint Resolve
  H_safely_removed
  H_find_binding' : Hints_bindings.
#[local]
Hint Constructors
  dead_syn
  dead_syn_binding
  dead_syn_bindings
  : reflection.

Lemma dec_Bindings_sound' : ∀ bs bs',
  (∀ b, In b bs -> P_Binding b) ->
  dec_Bindings dec_Term bs bs' = true -> dead_syn_bindings bs bs'.
Proof with eauto with Hints_bindings.
  intros H_P_bs bs bs' H.
  simpl in H.
  unfold dec_Bindings in H.
  split_hypos.
  eapply dc_bindings...
Qed.


Lemma dec_TermBind_sound : ∀ s v t b b',
  b = TermBind s v t ->
  P_Term t -> 
  dec_Binding dec_Term b b' = true ->
  dead_syn_binding b b'.
Proof with eauto with reflection.
  intros s v t b b' H_eq H_P_Term H_dec.
  unfold P_Term in *.
  subst.
  simpl in H_dec.
  destruct b'.
  all: try discriminate.
  split_hypos.
  assert (s = s0)...
  assert (v = v0)...
  subst...
Qed.

Lemma dec_TypeBind_sound : ∀ v ty b b',
  b = TypeBind v ty ->
  dec_Binding dec_Term b b' = true ->
  dead_syn_binding b b'.
Proof with eauto with reflection.
  intros v ty b b' H_eq H_dec.
  subst.
  destruct b'.
  all: try discriminate.
  simpl in H_dec.
  split_hypos.
  assert (v = t)... subst.
  assert (ty = t0)... subst...
Qed.

Lemma dec_DatatypeBind_sound : ∀ dtd b b',
  b = DatatypeBind dtd ->
  dec_Binding dec_Term b b' = true ->
  dead_syn_binding b b'.
Proof with eauto with reflection.
  intros dtd b b' H_eq H_dec.
  subst.
  destruct b'.
  all: try discriminate.
  simpl in H_dec.
  split_hypos.
  assert (dtd = d)... subst...
Qed.

Lemma all_pure : ∀ bs,
  forallb (is_pure_binding []) bs = true ->
  Forall (pure_binding []) bs.
Proof.
  intros bs H_dec.
  apply Forall_forall.
  intros b H_In.
  rewrite forallb_forall in H_dec.
  auto using is_pure_binding_pure_binding.
Qed.

#[local]
Hint Resolve all_pure : reflection.
#[local]
Hint Resolve dec_Bindings_sound' : reflection.
#[local]
Hint Resolve
  dec_TermBind_sound 
  dec_TypeBind_sound 
  dec_DatatypeBind_sound 
  : reflection.
#[local]
Hint Constructors Compat : reflection.

Theorem dec_Term_Binding_sound :
  (∀ t, P_Term t) /\ (∀ b, P_Binding b).
Proof with eauto with reflection.
  apply Term__multind with (P := P_Term) (Q := P_Binding).
  all: intros.

  (* P_Term (Let rec bs t) *)
  - unfold P_Term in *.
    intros t' H_dec_Term.
    simpl in H_dec_Term.
    destruct t'; simpl in H_dec_Term.
    all: split_hypos.
    {
      destruct (dec_Bindings dec_Term bs l) eqn:H_dec_bs.
      all: split_hypos.
      (* H_dec_Term: then branch *)
      * split_hypos.

        assert (H_bindings : dead_syn_bindings bs l).
        {
          apply ForallP_Forall in H.
          rewrite -> Forall_forall in H...
        }
        assert (H_eq_rec : rec = r)... subst.
        eapply dc_delete_bindings...

      (* H_dec_Term: else branch *)
      * eapply dc_delete_let...
    }
    all: try eapply dc_delete_let...

  - unfold P_Term.
    destruct t'.
    all: intro H_dec; try discriminate H_dec.
    assert (s = s0)... subst...
  - unfold P_Term.
    destruct t'.
    all: intro H_dec; try discriminate H_dec.
    simpl in H_dec. split_hypos.
    assert (s = s0)... subst.
    assert (k = k0)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (s = s0)...
    assert (t = t1)... subst...
  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    idtac...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (s = s0)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (d = d0)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (t0 = t1)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (t = t0)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (t = t2)... subst.
    assert (t0 = t3)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    idtac...

  - unfold P_Binding...
  - unfold P_Binding...
  - unfold P_Binding...
Qed.

Corollary dec_Term_sound : ∀ t t', dec_Term t t' = true -> dead_syn t t'.
Proof.
  apply dec_Term_Binding_sound.
Qed.

Corollary dec_Binding_sound : ∀ t t', dec_Term t t' = true -> dead_syn t t'.
Proof.
  apply dec_Term_Binding_sound.
Qed.
