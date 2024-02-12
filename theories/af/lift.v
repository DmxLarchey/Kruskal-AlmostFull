(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List.

Require Import notations.

Set Implicit Arguments.

Definition rel_lift X (R : rel₂ X) x := fun u v => R u v \/ R x u.
Definition sub_rel X (P : rel₁ X) (R : rel₂ X) : rel₂ (sig P) := fun x y => R (proj1_sig x) (proj1_sig y).

Arguments rel_lift {X} R /.
Arguments sub_rel {X} P R /.

Section lift.

  Variables (X : Type).

  Implicit Type R S : rel₂ X.

  Notation "R ↑ x" := (rel_lift R x) (at level 1, left associativity, format "R ↑ x").
  Reserved Notation "R ⇈ l" (at level 1, left associativity, format "R ⇈ l").

  Fixpoint rel_lift_list R l :=
    match l with
      | nil  => R
      | x::l => (R⇈l)↑x
    end
  where "R ⇈ l" := (rel_lift_list R l).

  Fact rel_lift_mono R S x : R ⊆₂ S -> R↑x ⊆₂ S↑x.
  Proof. firstorder. Qed.

  Fact rel_lift_list_inc R l : R ⊆₂ R⇈l.
  Proof. induction l; simpl; auto. Qed.

  Hint Resolve rel_lift_mono rel_lift_list_inc : core.

  Fact rel_lift_list_In R x y l : R y x -> y ∈ l -> forall z, R⇈l x z.
  Proof.
    intros H1 H2; induction l; simpl in H2 |- *; intros z; try tauto.
    destruct H2 as [ <- | ]; auto.
  Qed.

  Fact rel_lift_list_mono R S l : R ⊆₂ S -> R⇈l ⊆₂ S⇈l.
  Proof. induction l; simpl; auto; firstorder. Qed.

End lift.

Module lift_notations.

  Notation "R ↑ x" := (rel_lift R x) (at level 1, left associativity, format "R ↑ x").
  Notation "R ⇈ l" := (rel_lift_list R l) (at level 1, left associativity, format "R ⇈ l").
  Notation "R ⇓ P" := (sub_rel P R)  (at level 1, left associativity, format "R ⇓ P").

End lift_notations.

#[global] Hint Resolve rel_lift_mono
                       rel_lift_list_inc
                       rel_lift_list_mono : core.
