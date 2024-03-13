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

From KruskalTrees
  Require Import list_utils tactics.

Require Import base notations list_php lift good bar af.

Import ListNotations lift_notations.

Set Implicit Arguments.

Section bar_lift_rel.

  Variable (X : Type).

  Implicit Type (R : rel₂ X).

  Hint Resolve good_rel_lift : core.

  Local Fact bar_lift_snoc R l x : bar (good R↑x) l → bar (good R) (l++[x]).
  Proof. induction 1; eauto. Qed.

  Local Fact good_snoc_bar_lift R x l : good R (l++[x]) → bar (good R↑x) l.
  Proof.
    intros H.
    constructor 2; intros y; constructor 1.
    apply good_app_inv in H as [ H | [ H | (u & v & H1 & [ <- | [] ] & H3) ] ].
    + constructor 2; revert H; apply good_mono; firstorder.
    + rewrite good_cons_inv, good_nil_inv in H; firstorder.
    + constructor 1 with u; simpl; auto.
  Qed.

  Hint Resolve bar_lift_snoc good_snoc_bar_lift : core.

  Theorem bar_rel_lift R x l : bar (good R↑x) l ⇄ₜ bar (good R) (l++[x]).
  Proof.
    split; auto.
    revert l; apply bar_app_ind; auto.
  Qed.

  Theorem bar_rel_lift_list R l m : bar (good R⇈m) l ⇄ₜ bar (good R) (l++m).
  Proof.
    revert l; induction m as [ | x m IHm ]; intros l.
    + rewrite <- app_nil_end; tauto.
    + change (R⇈(x::m)) with (R⇈m↑x).
      split; equiv with bar_rel_lift; equiv with IHm; rewrite app_ass; auto.
  Qed.

End bar_lift_rel.

Section bar_good_af.

  Variable (X : Type).

  Implicit Type (R T : rel₂ X).

  Hint Resolve rel_lift_list_In : core.

  Lemma bar_good_af R l : bar (good R) l → af (R⇈l).
  Proof.
    induction 1 as [ l Hl | ]; eauto.
    constructor 1.
    induction Hl; simpl; eauto.
  Qed.

  Local Lemma af_bar_good_rec T R : af T → ∀l, T ⊆₂ R⇈l → bar (good R) l.
  Proof.
    induction 1 as [ T HT | T _ IHT ]; intros l Hl.
    + constructor 2; intros u.
      constructor 2; intros v.
      constructor 1.
      change (v::u::l) with ([v;u]++l).
      apply good_rel_lift_list.
      constructor 1 with u; simpl; auto.
    + constructor 2; intros x.
      apply (IHT x).
      simpl; firstorder.
  Qed.

  Lemma af_bar_good R l : af R⇈l → bar (good R) l.
  Proof. intro; eapply af_bar_good_rec; eauto. Qed.

  Hint Resolve bar_good_af af_bar_good : core.

  Theorem af_iff_bar_good R l : af R⇈l ⇄ₜ bar (good R) l.
  Proof. split; auto. Qed.

  Corollary af_iff_bar_good_nil R : af R ⇄ₜ bar (good R) [].
  Proof. apply af_iff_bar_good with (l := []). Qed.

End bar_good_af.

Section bar_good_eq.

  Infix "~ₚ" := (@Permutation _) (at level 70, no associativity).

  Variable (X : Type).

  Implicit Type (l m : list X).

  Fact perm_good_eq l m : l ~ₚ m → good eq l → good eq m.
  Proof.
    induction 1 as [ | x l m H IH | x y l | ]; auto; rewrite !good_cons_inv.
    + generalize (fun x => @Permutation_in _ _ _ x H); firstorder.
    + intros [ (? & [[]|] & ->) | [ (? & ? & ->) | ] ]; simpl; eauto.
  Qed.

  Section finite.

    Variables (l : list X) (Hl : forall x, x ∈ l).

    (* Another statement of the PHP *)

    Local Fact good_eq_gt m : ⌊l⌋ < ⌊m⌋ → good eq m.
    Proof.
      intros H.
      destruct php_short with (2 := H) as (x & m' & Hm').
      + intros ? ?; auto.
      + apply perm_good_eq with (1 := Permutation_sym Hm').
        constructor 1 with x; simpl; auto.
    Qed.

    Local Lemma bar_good_eq_rec n : ∀m, ⌊l⌋ < ⌊m⌋ + n → bar (good eq) m.
    Proof.
      induction n as [ | n IHn ]; intros m Hm.
      + constructor 1; apply good_eq_gt; tlia.
      + constructor 2; intros x.
        apply IHn; simpl; lia.
    Qed.

    Local Lemma bar_good_eq_any m : bar (good eq) m.
    Proof. apply bar_good_eq_rec with (n := S ⌊l⌋); tlia. Qed.

  End finite.

  Theorem bar_good_eq_fin : (∃ₜ l, ∀x, x ∈ l) → bar (good (@eq X)) [].
  Proof. intros (l & Hl); apply bar_good_eq_any with (1 := Hl). Qed.

End bar_good_eq.
