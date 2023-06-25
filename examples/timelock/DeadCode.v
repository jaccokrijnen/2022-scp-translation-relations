From Coq Require Import
  Strings.String.
From PlutusCert Require Import
  PlutusIR
  DeadCode
  DeadCode.Decide.
From Timelock Require Import
  PreTerm
  PostTerm.

Open Scope string_scope.

(*
Eval cbv in t_pre.
Eval cbv in t_post.
*)
Eval cbv in dec_Term t_pre t_post.
