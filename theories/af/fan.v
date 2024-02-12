(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Coq
  Require Import List Utf8.

From KruskalTrees
  Require Import tactics list_utils.

Require Import base notations fan.list_fan bar.

Import ListNotations.

Set Implicit Arguments.

Section fan_on_list.

  (* That proof of the FAN theorem is derived from Daniel Fridlender's paper *)

  Notation mono P := (∀ x l, P l → P (x::l)).

  Variables (X : Type) (P : list X → Prop) (HP : mono P).

  Local Fact P_mono_gen l m : P m → P (l++m).
  Proof. induction l; simpl; auto. Qed.

  Let FAN_from u := λ lw, Forall (λ v, P (v++u)) (list_fan lw).

  Local Fact FAN_from_mono u : mono (FAN_from u).
  Proof.
    unfold FAN_from; intros w lw H.
    apply list_fan_Forall.
    rewrite Forall_forall; intros x _.
    revert H; apply Forall_impl.
    intro; apply HP.
  Qed.

  Hint Resolve P_mono_gen FAN_from_mono : core.

  Local Fact bar_P_bar_FAN_from u : bar P u → bar (FAN_from u) [].
  Proof.
    induction 1 as [ u Hu | u Hu IHu ].
    + constructor 1; unfold FAN_from; simpl; auto.
    + constructor 2; intros w.
      induction w as [ | a w IHw ].
      * constructor 1; unfold FAN_from; simpl; auto.
      * specialize (IHu a).
        apply bar_app_nil in IHw.
        unfold FAN_from in IHw.
        generalize (@FAN_from_mono (a::u)); intros HV1.
        assert (mono (fun lw => FAN_from u (lw++w::nil))) as HV2.
        1: intros x ll; simpl; auto.
        generalize (bar_intersection HV1 HV2 IHu IHw); intros HV3; clear HV1 HV2.
        apply bar_app_nil.
        revert HV3; apply bar_mono.
        intros x [ H1 H2 ]; unfold FAN_from in *.
        rewrite Forall_forall; intros z; rewrite list_fan_middle_cons;
          revert z; apply Forall_forall.
        apply Forall_app; split; auto.
        rewrite Forall_forall; intros z; rewrite list_fan_sg_right;
          revert z; apply Forall_forall.
        rewrite Forall_map.
        revert H1; apply Forall_impl.
        intro; rewrite app_ass; auto.
  Qed.

  (* list_fan [[0;1];[3;4]] = [[0;3];[0;4];[1;3];[1;4]] *)

  Theorem fan_on_list : bar P [] → bar (λ l, Forall P (list_fan l)) [].
  Proof.
    intros H.
    generalize (bar_P_bar_FAN_from H).
    apply bar_mono.
    intros lw; unfold FAN_from.
    apply Forall_impl.
    intro; rewrite <- app_nil_end; auto.
  Qed.

End fan_on_list.
