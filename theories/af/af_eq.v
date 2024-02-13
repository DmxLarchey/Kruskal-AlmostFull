(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Arith Lia Permutation Utf8.

Require Import base notations list_php lift af.

Import ListNotations lift_notations.

Set Implicit Arguments.

Fact eq_rel_lift_list X x y (l : list X) :
      eq⇈l x y ↔ x = y ∨ x ∈ l ∨ lhd l.
Proof.
  induction l as [ | a l IHl ] in x, y |- *; simpl.
  + rewrite lhd_nil_inv; tauto.
  + rewrite !IHl, lhd_cons_inv; tauto.
Qed.

(* If l has a duplicate then eq⇈l is full *)
Corollary list_has_dup_eq_rel_lift_full X (l : list X) : lhd l → ∀ x y, eq⇈l x y.
Proof. intros ? ? ?; apply eq_rel_lift_list; tauto. Qed.

#[local] Hint Resolve list_has_dup_eq_rel_lift_full : core.

Section af_eq_list.

  Variable (X : Type).
  Implicit Type (l m : list X).
  Variables (n : nat) (Hn : ∃m, ⌊m⌋ ≤ n ∧ ∀ x, x ∈ m).

  (* By the PHP, any list bigger than n has a duplicate *)
  Local Lemma eq_lift_list_full_af l : n < ⌊l⌋ → lhd l.
  Proof.
    intros H1.
    destruct Hn as (m & H2 & H3).
    apply php_short with (m := m); try lia.
    intros ? ?; auto.
  Qed.

  Hint Resolve incl_cons incl_nil_l eq_lift_list_full_af : core.

  Local Lemma af_eq_rel_lift_list k l : n < k+⌊l⌋ → af (eq⇈l).
  Proof.
    induction k as [ | k IHk ] in l |- *; simpl; intros Hl; auto.
    constructor 2; intro.
    apply (IHk (_::_)); simpl; auto; lia.
  Qed.

  Theorem af_eq_list : af (@eq X).
  Proof.
    apply af_eq_rel_lift_list
      with (l := []) (k := S n);
      auto; simpl; lia.
  Qed.

End af_eq_list.

Section afs_eq_list.

  Variable (X : Type) (P : rel₁ X).
  Implicit Types (l m : list X).
  Variables (n : nat) (Hn : ∃m, ⌊m⌋ ≤ n ∧ ∀x, P x → x ∈ m).

  (* By the PHP, any list bigger than n has a duplicate *)
  Local Lemma eq_lift_list_full_afs l :
        n < ⌊l⌋ → (∀x, x ∈ l → P x) → lhd l.
  Proof.
    intros H1 H2.
    destruct Hn as (m & H0 & H3).
    apply php_short with (m := m); try lia.
    intros ? ?; auto.
  Qed.

  Hint Resolve incl_cons incl_nil_l eq_lift_list_full_afs : core.

  Local Lemma afs_eq_rel_lift_list k l :
         n < k+⌊l⌋ → (∀x, x ∈ l → P x) → afs P (eq⇈l).
  Proof.
    induction k as [ | k IHk ] in l |- *; simpl; intros H1 H2; auto.
    constructor 2; intros ? ?.
    apply (IHk (_::_)); simpl; try lia; auto.
    intros ? [ <- | ]; auto.
  Qed.

  Theorem afs_eq_list : afs P eq.
  Proof.
    apply afs_eq_rel_lift_list
      with (l := []) (k := S n);
      auto; simpl; lia.
  Qed.

End afs_eq_list.

(** If X (resp. P) is covered by a list, then
    the identity is af on X (resp. afs on P) *)

Theorem afs_eq_fin_strong X (P : rel₁ X) :
       (∃ₜ n, ∃l, ⌊l⌋ ≤ n ∧ ∀x, P x → x ∈ l)
     → afs P eq.
Proof. intros []; eapply afs_eq_list; eauto. Qed.

Theorem afs_eq_fin X (P : rel₁ X) :
        (∃ₜ l, ∀x, P x → x ∈ l)
      → afs P eq.
Proof. intros []; apply afs_eq_fin_strong; eauto. Qed.

Theorem af_eq_fin_strong X :
        (∃ₜ n, ∃l, ⌊l⌋ ≤ n ∧ ∀x : X, x ∈ l)
      → @af X eq.
Proof. intros []; eapply af_eq_list; eauto. Qed.

Theorem af_eq_fin X :
        (∃ₜ l, ∀x : X, x ∈ l)
     -> @af X eq.
Proof. intros []; apply af_eq_fin_strong; eauto. Qed.

(** identity is included in any af/afs relation *)

Proposition afs_eq_lower X (P : rel₁ X) (R : rel₂ X) :
        afs P R → ∀x, P x → R x x.
Proof.
  intros H x Hx.
  apply afs_iff_af_sub_rel in H.
  destruct (af_af_rec_fun H (fun _ => exist _ x Hx))
    as (? & _ & _ & _ & ?); auto.
Qed.

Proposition af_eq_lower X R :
        @af X R → ∀x, R x x.
Proof. intros H x; apply af_iff_afs_True, afs_eq_lower with (x := x) in H; auto. Qed.


