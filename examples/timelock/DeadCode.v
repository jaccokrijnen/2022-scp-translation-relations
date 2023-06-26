From Coq Require Import
  Strings.String.
From PlutusCert Require Import
  PlutusIR
  DeadCode
  DeadCode.Decide
  DeadCode.DecideSound.
From Timelock Require Import
  PreTerm
  PostTerm.


Lemma Example2 : elim t_pre t_post.
Proof.
  exact (sound_dec_elim_Term t_pre t_post eq_refl).
Qed.
