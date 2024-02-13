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
           → ∀C, R ⊆₂ C ∪₂ (λ _ _, A)
               → af (λ x y, C x y ∨ B)
               → af (λ x y, C x y ∨ A ∧ B).
  Proof.
    induction 1 as [ R HR | R HR1 HR2 ]; intros C HC HB.
    + apply af_mono with (2 := HB).
      intros x y []; auto.
      generalize (HC _ _ (HR x y)); tauto.
    + constructor 2; intros a.
      apply af_mono with (R := fun x y => (C x y \/ C a x) \/ A /\ B).
      1: squeeze.
      apply HR2 with a.
      1: intros ? ?; unfold rel_lift; intros [ ?%HC | ?%HC ]; tauto.
      apply af_mono with (2 := HB); tauto.
  Qed.

  Local Lemma af_zero_inter R A B :
        af (λ x y, R x y ∨ A)
      → af (λ x y, R x y ∨ B)
      → af (λ x y, R x y ∨ A ∧ B).
  Proof. intro H; now apply af_zero_inter_rec with (1 := H). Qed.

  Local Lemma af_one_inter_rec A B R :
                  af R
            → ∀T, af T
            → ∀C, R ⊆₂ C ∪₂ (λ x _, A x)
                → T ⊆₂ C ∪₂ (λ x _, B x)
                → af (λ x y, C x y ∨ A x ∧ B x).
  Proof.
    induction 1 as [ R HR | R HR IHR ].
    1:{ intros T HT C HRC HTC.
        eapply af_mono with (2 := HT).
        intros x y; generalize (HRC x y) (HTC x y) (HR x y); tauto. }
    induction 1 as [ T HT | T HT IHT ].
    1: { intros C HRC HTC.
         apply af_mono with (R := R); eauto.
         intros x y; generalize (HT x y) (HRC x y) (HTC x y); tauto. }
    intros C HRC HTC.
    constructor 2; intros a.
    generalize (af_lift HT); intros HT'.
    apply af_mono with (R := fun x y => ((C x y \/ A x /\ B x) \/ C a x) \/ A a /\ B a).
    1: squeeze.
    apply af_zero_inter.
    + generalize (IHR a _ HT' (fun x y => C x y \/ C a x \/ A a)); intros G0.
      eapply af_mono.
      2:{ apply G0.
          + intros x y; generalize (HRC x y) (HRC a x); unfold rel_lift; tauto.
          + intros x y ?; generalize (HTC x y); tauto. }
      squeeze.
    + generalize (IHT a (fun x y => C x y \/ C a x \/ B a)); intros G0.
      eapply af_mono.
      2:{ apply G0.
          + intros x y; generalize (HRC x y) (HRC a x); tauto.
          + intros ? ? [ ?%HTC | ?%HTC ]; tauto. }
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
    intros HR HT; revert R HR T HT.
    induction 1 as [ R HR | R HR%af_lift IHR ].
    1: intro; apply af_mono; squeeze.
    induction 1 as [ T HT | T HT%af_lift IHT ].
    1: apply af_mono with (2 := HR); squeeze.
    constructor 2; intros a; unfold rel_lift.
    apply af_one_inter.
    + apply af_mono with (2 := IHR a _ HT); squeeze.
    + apply af_mono with (2 := IHT a); squeeze.
  Qed.

End af_intersection.
