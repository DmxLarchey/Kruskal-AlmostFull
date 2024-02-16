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

(** This is Ramsey's theorem Coquand's style. See

      "Stop when you are Almost Full" (ITP 2012)

      and also

      http://www.cse.chalmers.se/~coquand/ramsey2.pdf 

    The proof below is a much cleaned up proof with a 
    symmetric treatement of R and T via af_double_induction 
    below. *)

Section af_double_induction.

  Variables (X : Type) (P : rel₂ X → rel₂ X → Base)
            (HP0 : ∀ (R T : rel₂ X), (∀ x y, R x y) → af T → P R T)
            (HP1 : ∀ (R T : rel₂ X), af R → (∀ x y, T x y) → P R T)
            (HP2 : ∀ R T, (∀x, P (R↑x) T) → (∀x, P R (T↑x)) → P R T).

  Local Theorem af_double_induction R T : af R → af T → P R T.
  Proof.
    induction 1 as [ | ? ?%af_lift ] in T |- *; auto.
    induction 1; auto.
  Qed.

End af_double_induction.

#[local] Tactic Notation "af" "induction" "as" ident(HR) ident(HT) :=
  match goal with
  | |- af ?R → af ?T → _ =>
     intros HR HT; pattern R, T; revert R T HR HT; apply af_double_induction; intros R T HR HT
  end.

Section af_intersection.

  Variable X : Type.

  Implicit Types (R T : rel₂ X).

  Ltac squeeze := unfold rel_lift; intros; (tauto || (try firstorder) || fail).

  Local Lemma af_zero_inter_rec A B R T :
              af R
            → af T
            → ∀C, R ⊆₂ C ∪₂ (λ _ _, A)
                → T ⊆₂ C ∪₂ (λ _ _, B)
                → af (λ x y, C x y ∨ A ∧ B).
  Proof.
    af induction as HR HT; intros C HRC HTC.
    + apply af_mono with (2 := HT).
      intros x y []%HTC; auto.
      generalize (HRC _ _ (HR x y)); squeeze.
    + apply af_mono with (2 := HR).
      intros x y []%HRC; auto.
      generalize (HTC _ _ (HT x y)); squeeze.
    + constructor 2; intros a.
      apply af_mono with (R := fun x y => (C x y \/ C a x) \/ A /\ B);
        [ squeeze | ].
      apply HR with a.
      * intros ? ? [ ?%HRC | ?%HRC ]; squeeze.
      * intros ? ? []%HTC; squeeze.
  Qed.

  Local Lemma af_zero_inter R A B :
        af (λ x y, R x y ∨ A)
      → af (λ x y, R x y ∨ B)
      → af (λ x y, R x y ∨ A ∧ B).
  Proof. intros H1 H2; now apply af_zero_inter_rec with (1 := H1) (2 := H2). Qed.

  Local Lemma af_one_inter_rec A B R T :
              af R
            → af T
            → ∀C, R ⊆₂ C ∪₂ (λ x _, A x)
                → T ⊆₂ C ∪₂ (λ x _, B x)
                → af (λ x y, C x y ∨ A x ∧ B x).
  Proof.
   af induction as HR HT; intros C HRC HTC.
   + apply af_mono with (2 := HT).
     intros x y; generalize (HRC x y) (HTC x y) (HR x y); squeeze.
   + apply af_mono with (2 := HR).
     intros x y; generalize (HRC x y) (HTC x y) (HT x y); squeeze.
   + constructor 2; intros a.
     apply af_mono with (R := fun x y => ((C x y \/ A x /\ B x) \/ C a x) \/ A a /\ B a);
       [ squeeze | ].
     apply af_zero_inter.
     * specialize (HR a (fun x y => C x y \/ C a x \/ A a)).
       eapply af_mono; [ | apply HR ].
       - squeeze.
       - intros ? ? [ ?%HRC | ?%HRC ]; squeeze.
       - intros ? ? []%HTC; squeeze.
     * specialize (HT a (fun x y => C x y \/ C a x \/ B a)).
       eapply af_mono; [ | apply HT ].
       - squeeze.
       - intros ? ? []%HRC; squeeze.
       - intros ? ? [ ?%HTC | ?%HTC ]; squeeze.
  Qed.

  Local Lemma af_one_inter R A B :
        af (λ x y, R x y ∨ A x)
      → af (λ x y, R x y ∨ B x)
      → af (λ x y, R x y ∨ A x ∧ B x).
  Proof.
    intros HA HB.
    apply af_one_inter_rec with (1 := HA) (2 := HB); squeeze.
  Qed.

  Theorem af_inter R T : af R → af T → af (R ∩₂ T).
  Proof.
    af induction as HR HT.
    + apply af_mono with (2 := HT); squeeze.
    + apply af_mono with (2 := HR); squeeze.
    + constructor 2; intros a.
      apply af_one_inter.
      * apply af_mono with (2 := HR a); squeeze.
      * apply af_mono with (2 := HT a); squeeze.
  Qed.

End af_intersection.
