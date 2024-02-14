(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith Lia Utf8.

From KruskalTrees
  Require Import idx vec.

From KruskalFinite
  Require Import finite decide.

Require Import base notations compute_opair almost_full.

Import idx_notations vec_notations.

Set Implicit Arguments.

Section Dickson_lemma.

  Variable (k : nat) (f : nat -> vec nat k).

  (* The bound n below can be computed provided Base is Type (ie
     af predicate are informative), and then i and j can as well
     because _ ≤ _ : rel₂ nat is decidable *)

  Theorem Dickson_lemma : ∃ₜ n, ∃ i j, i < j < n ∧ ∀p, (f i)⦃p⦄ ≤ (f j)⦃p⦄.
  Proof. apply af_recursion with (R := @vec_fall2 _ _ le _), af_vec_fall2, af_le_nat. Qed.

  Theorem Dickson_lemma_strong : ∃ₜ i j, i < j ∧ ∀p, (f i)⦃p⦄ ≤ (f j)⦃p⦄.
  Proof.
    destruct Dickson_lemma as (n & Hn).
    destruct compute_opair with (2 := Hn) as (i & j & H); eauto.
    intros i j.
    decide auto; fin auto.
    intro; apply le_dec.
  Qed.

End Dickson_lemma.


