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

Import lift_notations.

Set Implicit Arguments.

Section af_double_recb.

  Variables (X : Type) (P : rel₂ X -> rel₂ X -> Base)
            (HP0 : forall R T, (∀ x y, R x y) -> af T -> P R T)
            (HP1 : forall R T, af R -> (∀ x y, T x y) -> P R T)
            (HP2 : forall R T, (∀x, P (R↑x) (T↑x)) -> P R T).

  Theorem af_double_recb R T : af R -> af T -> P R T.
  Proof.
    induction 1 as [ R HR | R HR%af_lift IHR ] in T |- *; auto.
    induction 1 as [ T HT | T HT IHT ]; auto.
  Qed.

End af_double_recb.

Section af_intersection.

  (** This is Ramsey's theorem Coquand's style. See

        "Stop when you are Almost Full" (ITP 2012)
   *)

  Variable X : Type.

  Implicit Types (R T : rel₂ X).

  Ltac squeeze := unfold rel_lift; intros ? ?; (tauto || firstorder || fail).

  Local Lemma af_zero_inter_rec A B C R T :
                 af R
               → af T
               → R ⊆₂ C ∪₂ (λ _ _, A)
               → T ⊆₂ C ∪₂ (λ _ _, B)
               → af (λ x y, C x y ∨ A ∧ B).
  Proof.
    intros H1 H2; revert A B C; pattern R, T; revert R T H1 H2.
    apply af_double_recb.
    + intros R T HR HT A B C HRC HTC.
      apply af_mono with (2 := HT).
      intros x y []%HTC; auto.
      generalize (HRC _ _ (HR x y)); tauto.
    + intros R T HR HT A B C HRC HTC.
      apply af_mono with (2 := HR).
      intros x y []%HRC; auto.
      generalize (HTC _ _ (HT x y)); tauto.
    + intros R T IH A B C HRC HTC.
      constructor 2; intros a.
      apply af_mono with (R := fun x y => (C x y \/ C a x) \/ A /\ B).
      1: squeeze.
      apply IH with a.
      * intros ? ? [ ?%HRC | ?%HRC ]; tauto.
      * intros ? ? [ ?%HTC | ?%HTC ]; tauto.
  Qed.

  Local Lemma af_zero_inter R A B :
        af (λ x y, R x y ∨ A)
      → af (λ x y, R x y ∨ B)
      → af (λ x y, R x y ∨ A ∧ B).
  Proof. intros H1 H2; now apply af_zero_inter_rec with (1 := H1) (2 := H2). Qed.

  Local Lemma af_one_inter_rec_sym A B R :
                  af R
            → ∀T, af T
            → ∀C, R ⊆₂ C ∪₂ (λ x _, A x)
                → T ⊆₂ C ∪₂ (λ x _, B x)
                → af (λ x y, C x y ∨ A x ∧ B x).
  Proof.
   intros H1 T H2.
   pattern R, T; revert R T H1 H2.
   apply af_double_recb.
   + intros R T HR HT C HRC HTC.
     apply af_mono with (2 := HT).
     intros x y; generalize (HRC x y) (HTC x y) (HR x y); tauto.
   + intros R T HR HT C HRC HTC.
     apply af_mono with (2 := HR).
     intros x y; generalize (HRC x y) (HTC x y) (HT x y); tauto.
   + intros R T IH C HRC HTC.
     constructor 2; intros a.
     apply af_mono with (R := fun x y => ((C x y \/ A x /\ B x) \/ C a x) \/ A a /\ B a).
     1: squeeze.
     apply af_zero_inter.
     * specialize (IH a (fun x y => C x y \/ C a x \/ A a)).
       eapply af_mono; [ | apply IH ].
       - squeeze.
       - intros x y [ ?%HRC | ?%HRC ]; tauto.
       - intros x y [?%HTC|?%HTC]; try tauto.
  Admitted.

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
    induction 1 as [ T HT | T HT%af_lift IHT ].
    1: { intros C HRC HTC.
         apply af_mono with (R := R); eauto.
         intros x y; generalize (HT x y) (HRC x y) (HTC x y); tauto. }
    intros C HRC HTC.
    constructor 2; intros a.
    apply af_mono with (R := fun x y => ((C x y \/ A x /\ B x) \/ C a x) \/ A a /\ B a).
    1: squeeze.
    apply af_zero_inter.
    + generalize (IHR a _ HT (fun x y => C x y \/ C a x \/ A a)); intros G0.
      eapply af_mono; [ | apply G0 ].
      * squeeze.
      * intros x y; generalize (HRC x y) (HRC a x); unfold rel_lift; tauto.
      * intros x y ?; generalize (HTC x y); tauto.
    + generalize (IHT a (fun x y => C x y \/ C a x \/ B a)); intros G0.
      eapply af_mono; [ | apply G0 ].
      * squeeze.
      * intros x y; generalize (HRC x y) (HRC a x); tauto.
      * intros ? ? [ ?%HTC | ?%HTC ]; tauto.
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
