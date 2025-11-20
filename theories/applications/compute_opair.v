(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib
  Require Import Arith Lia Utf8.

From KruskalFinite
  Require Import finite choice decide.

Require Import notations.

Section compute_opair.

  (* Compute an ordered pair from a decider and the
     knowledge that there is one below n *)

  (* 𝕆𝕊 λ ∀∃ → ↔ ∧ ∨ *)

  Variables (P : rel₂ nat)
            (Pdec : ∀ i j, decider (P i j))
            (n : nat)
            (Hn : ∃ i j, i < j < n ∧ P i j).

  Let F c := ∃j, (∃i, (i,j) = c ∧ i < j) ∧ j < n.
  Let Q '(i,j) := P i j.

  Fact compute_opair : { i : _ & { j | i < j ∧ P i j } }.
  Proof.
    destruct (@fin_choice_t _ F (fun c => ~ Q c) Q)
      as [ H | ((i,j) & H1 & H2) ].
    + unfold F; fin auto.
    + intros [] _; simpl; decide swap; auto.
    + exfalso.
      destruct Hn as (i & j & (? & ?) & ?).
      apply (H (i,j)); simpl; auto.
      red; eauto.
    + exists i, j; split; auto.
      revert H1; intros (? & (? & [=] & ?) & ?); subst; auto.
  Qed.

End compute_opair.
