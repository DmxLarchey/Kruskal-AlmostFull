(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Utf8.

Require Import base notations lift pfx_rev good af.

Import ListNotations lift_notations.

Set Implicit Arguments.

Section af_good.

  Variable X : Type.

  Implicit Type (R : rel₂ X).

  Hint Resolve in_eq : core.

  Fact af_good_prefix R : af R → ∀f, ∃ₜ n, good R (pfx_rev f n).
  Proof.
    induction 1 as [ R HR | R _ IHR ]; intros f.
    + exists 2; constructor 1 with (f 0); auto.
    + destruct (IHR (f 0) (fun n => f (S n))) as (n & Hn).
      apply good_rel_lift in Hn.
      exists (S n); rewrite pfx_rev_S; auto.
  Qed.

  Fact af_good_pair R f : af R → ∃ₜ n, ∃ i j, i < j < n ∧ R (f i) (f j).
  Proof.
    intros H.
    destruct af_good_prefix with (1 := H) (f := f) as (n & Hn).
    exists n.
    apply good_pfx_rev in Hn as (? & ? & ? & ?); eauto.
  Qed.

End af_good.
