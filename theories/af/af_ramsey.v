(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Utf8.

Require Import base notations lift af.

Set Implicit Arguments.

Section af_intersection.

  (** This is Ramsey's theorem Coquand's style. See

        "Stop when you are Almost Full" (ITP 2012)
   *)

  Variable X : Type.

  Implicit Types (R T : rel₂ X).

  Ltac squeeze := unfold rel_lift; intros ? ?; (tauto || firstorder || fail).

  Local Lemma af_zero_inter_rec A B R :
                 af R
           → ∀C, (∀ x y, R x y → C x y ∨ A)
               → af (λ x y, C x y ∨ B)
               → af (λ x y, C x y ∨ A ∧ B).
  Proof.
    induction 1 as [ R HR | R HR1 HR2 ]; intros C HC HB.
    + apply af_mono with (2 := HB).
      intros x y []; auto.
      specialize (HR x y); apply HC in HR; tauto.
    + constructor 2; intros x.
      apply af_mono with (R := fun y z => (C y z \/ C x y) \/ A /\ B).
      1: squeeze.
      apply HR2 with x.
      1: intros ? ?; unfold rel_lift; intros [ ?%HC | ?%HC ]; tauto.
      apply af_mono with (2 := HB); firstorder.
  Qed.

  Local Lemma af_zero_inter R A B :
        af (λ x y, R x y ∨ A)
      → af (λ x y, R x y ∨ B)
      → af (λ x y, R x y ∨ A ∧ B).
  Proof.
    intros H.
    apply af_zero_inter_rec with (1 := H).
    intros; tauto.
  Qed.

  Local Lemma af_one_inter_rec A B R :
                  af R
            → ∀T, af T
            → ∀C, (∀ x y, R x y → C x y ∨ A x)
                → (∀ x y, T x y → C x y ∨ B x)
                → af (λ x y, C x y ∨ A x ∧ B x).
  Proof.
    induction 1 as [ R HR | R HR IHR ].
    1:{ intros T HT C Req Teq.
        eapply af_mono with (2 := HT).
        intros x y; generalize (Req x y) (Teq x y) (HR x y); tauto. }
    induction 1 as [ T HT | T HT IHT ].
    1: { intros C Req Teq.
         apply af_mono with (R := R).
         intros x y; generalize (HT x y) (Req x y) (Teq x y); tauto.
         constructor 2; apply HR. }
    intros C Req Teq.
    constructor 2; intros x.
    generalize (af_lift HT); intros HT'.
    apply af_mono with (R := fun y z : X => ((C y z \/ A y /\ B y) \/ C x y) \/ A x /\ B x).
    1: squeeze.
    apply af_zero_inter.
    + generalize (IHR x _ HT' (fun y z => C y z \/ C x y \/ A x)); intros G0.
      eapply af_mono.
      2:{ apply G0.
          intros y z; generalize (Req y z) (Req x y); unfold rel_lift; tauto.
          intros y z Hyz; generalize (Teq y z); tauto. }
      squeeze.
    + generalize (IHT x (fun y z => C y z \/ C x y \/ B x)); intros G0.
      eapply af_mono.
      2:{ apply G0.
          intros y z; generalize (Req y z) (Req x y); tauto.
          intros y z [ H1 | H1 ]; apply Teq in H1; tauto. }
      squeeze.
  Qed.

  Local Lemma af_one_inter R A B :
        af (λ x y, R x y ∨ A x)
      → af (λ x y, R x y ∨ B x)
      → af (λ x y, R x y ∨ A x ∧ B x).
  Proof.
    intros H1 H2.
    apply af_one_inter_rec with (1 := H1) (2 := H2); squeeze.
  Qed.

  Theorem af_inter R T : af R → af T → af (R ∩₂ T).
  Proof.
    intros HR HT.
    revert R HR T HT.
    induction 1 as [ R HR | R HR IHR ].
    1: intros T HT; apply af_mono with (2 := HT); squeeze.
    induction 1 as [ T HT | T HT IHT ].
    1: apply af_mono with (2 := af_lift HR); squeeze.
    constructor 2; intros x; unfold rel_lift.
    apply af_one_inter.
    + apply af_mono with (2 := IHR x _ (af_lift HT)); squeeze.
    + apply af_mono with (2 := IHT x); squeeze.
  Qed.

End af_intersection.
