(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Arith Permutation Utf8.

From KruskalTrees
  Require Import tactics list_utils.

Require Import base notations lift pfx_rev.

Import ListNotations lift_notations.

Set Implicit Arguments.

Section bar.

  Variable X : Type.

  Implicit Type (P Q : rel₁ (list X)) (f : nat → X).

  Inductive bar P : list X → Base :=
    | bar_stop l : P l → bar P l
    | bar_next l : (∀x, bar P (x::l)) → bar P l.

  Hint Constructors bar : core.

  Fact bar_mono P Q : P ⊆₁ Q -> bar P ⊆₁ bar Q.
  Proof. induction 2; eauto. Qed.

  Notation mono P := (∀ x l, P l → P (x::l)).

  Fact bar_inv_mono P : mono P → mono (bar P).
  Proof. induction 2; eauto. Qed.

  Section bar_app_ind.

    (** A generalized (non-dependent) induction principle for predicates
        of the form bar P (_++m) *)

    Variable (m : list X) (P : rel₁ (list X)) (Q : list X → Base)
             (HQ1 : ∀l, P (l++m) → Q l)
             (HQ2 : ∀l, (∀x, bar P (x::l++m))
                      → (∀x, Q (x::l))
                      → Q l).

    (** Instead of v = l++m, we use Leibniz equality 
        ∀K, K v → K (l++m) in Type and avoid
        singleton elimination (of identity) here.
        We could also use the identity in Type 
        instead of Prop to acheive the same *)

    Local Fact bar_ind_app v : bar P v → ∀l, (∀K, K v → K (l++m)) → Q l.
    Proof.
      induction 1 as [ v Hv | v Hv IHv ]; intros l Hl.
      + apply HQ1, Hl, Hv.
      + apply HQ2; intros x.
        * apply Hl with (K := fun l => bar P (x::l)); auto.
        * apply (IHv x (_::_)).
          intros K; apply Hl with (K := fun _ => K (_::_)).
    Qed.

    Theorem bar_app_ind l : bar P (l++m) → Q l.
    Proof. intros; eapply bar_ind_app; eauto. Qed.

  End bar_app_ind.

  (* With bar_app_ind, we get a vert simple proof here *)

  Lemma bar_app P u v : bar P (v++u) ⇄ₜ bar (λ w, P (w++u)) v.
  Proof.
    split.
    + apply bar_app_ind; eauto.
    + induction 1; eauto.
  Qed.

  Theorem bar_app_nil P u : bar P u ⇄ₜ bar (λ v, P (v++u)) [].
  Proof. split; equiv with bar_app; simpl; tauto. Qed.

  Section bar_pfx_rev.

    (* Same trick with Leibniz equality as above *)

    Local Fact bar_pfx_rec P l : bar P l → ∀ f n, (∀K, K l → K (pfx_rev f n)) → ∃ₜ m, n ≤ m ∧ P (pfx_rev f m).
    Proof.
      induction 1 as [ l Hl | l Hl IHl ]; intros f n Hn.
      + exists n; split; auto; apply Hn, Hl.
      + destruct (@IHl (f n) f (S n)) as (m & Hm & ?); simpl.
        * intros K; apply Hn with (K := fun _ => K (_::_)).
        * exists m; split; auto.
          apply le_trans with (2 := Hm), le_n_Sn.
    Qed.

    Lemma bar_pfx_rev P f : bar P [] → ∃ₜ n, P (pfx_rev f n).
    Proof.
      intros H.
      destruct bar_pfx_rec with (1 := H) (n := 0) (f := f)
        as (? & ? & ?); eauto.
    Qed.

  End bar_pfx_rev.

  Section bar_inter.

    Variables (P Q : rel₁ (list X))
              (HP : mono P) (HQ : mono Q).

    Theorem bar_intersection u : bar P u → bar Q u → bar (P ∩₁ Q) u.
    Proof. do 2 induction 1; eauto. Qed.

  End bar_inter.

End bar.

#[global] Hint Constructors bar : core.

Section bar_relmap.

  Variables (X Y : Type) (f : X → Y → Prop)
            (R : rel₁ (list X)) (T : rel₁ (list Y))
            (Hf : ∀y, ∃ₜ x, f x y)                     (** f is surjective *)
            (HRT : ∀ l m, Forall2 f l m → R l → T m)   (** f is a morphism form R to T *)
            .

  Theorem bar_relmap l m : Forall2 f l m → bar R l → bar T m.
  Proof.
    intros H1 H2; revert H2 m H1 T HRT.
    induction 1 as [ l Hl | l Hl IHl ]; intros m H1 T HRT.
    * constructor 1; revert Hl; apply HRT; auto.
    * constructor 2; intros y.
      destruct (Hf y) as (x & Hx).
      apply (IHl x); auto.
  Qed.

End bar_relmap.

Section bar_map.

  Variables (X Y : Type) (f : X → Y) (Hf : ∀y, ∃ₜ x, y = f x)
            (P : rel₁ (list X))
            (Q : rel₁ (list Y))
            (HPQ1 : ∀l, P l → Q (map f l))
            (HPQ2 : ∀l, Q (map f l) → P l).

  Lemma bar_map_inv l : bar Q (map f l) → bar P l.
  Proof.
    apply bar_relmap with (f := fun x y => x = f y); eauto.
    + intros ? ?.
      rewrite <- Forall2_map_right, Forall2_eq.
      intros ->; auto.
    + rewrite <- Forall2_map_right, Forall2_eq; auto.
  Qed.

  Lemma bar_map l : bar P l → bar Q (map f l).
  Proof.
    apply bar_relmap with (f := fun x y => f x = y); auto.
    + intros b; destruct (Hf b); eauto.
    + intros ? ?; rewrite <- Forall2_map_left, Forall2_eq; intros; subst; auto.
    + rewrite <- Forall2_map_left, Forall2_eq; auto.
  Qed.

End bar_map.

Section bar_map_fun.

  Variable (X Y : Type) (f : X → Y) (P : rel₁ (list Y)).

  Local Lemma bar_map_fun_rec l : bar P l → ∀m, (∀K, K l → K (map f m)) → bar (λ l, P (map f l)) m.
  Proof.
    induction 1 as [ | l Hl IHl ]; intros m Hm; eauto.
    + constructor 1; now apply Hm.
    + constructor 2; intro.
      apply IHl with (x := f x) (m := _::_).
      intros K; simpl.
      now apply Hm.
  Qed.

  Hint Resolve bar_map_fun_rec : core.

  Lemma bar_map_fun l : bar P (map f l) → bar (λ l, P (map f l)) l.
  Proof. eauto. Qed.

  Lemma bar_map_fun_nil : bar P [] → bar (λ l, P (map f l)) [].
  Proof. exact (bar_map_fun []). Qed.

End bar_map_fun.


