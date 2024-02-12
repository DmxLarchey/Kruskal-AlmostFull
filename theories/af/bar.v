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

  Implicit Type (P Q : list X → Prop) (f : nat → X).

  Inductive bar P : list X → Base :=
    | bar_stop l : P l → bar P l
    | bar_next l : (∀x, bar P (x::l)) → bar P l.

  Hint Constructors bar : core.

  Fact bar_mono P Q : P ⊆₁ Q -> bar P ⊆₁ bar Q.
  Proof. induction 2; eauto. Qed.

  Notation mono P := (∀ x l, P l → P (x::l)).

  Fact bar_inv_mono P : mono P -> mono (bar P).
  Proof. induction 2; eauto. Qed.

  Section bar_app_ind.

    (** A generalized (non-dependent) induction principle for predicates
        of the form bar P (_++m) *)

    Variable (m : list X) (P : list X → Prop) (Q : list X → Base)
             (HQ1 : ∀l, P (l++m) → Q l)
             (HQ2 : ∀l, (∀x, bar P (x::l++m))
                      → (∀x, Q (x::l))
                      → Q l).

    (** Instead of v = l++m, we use Leibniz equality and avoid
        singleton elimination (of identity) here. We could also
        use identity in Type instead of Prop *)

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

    Variables (P Q : list X → Prop)
              (HP : mono P) (HQ : mono Q).

    Theorem bar_intersection u : bar P u → bar Q u → bar (P ∩₁ Q) u.
    Proof. do 2 induction 1; eauto. Qed.

  End bar_inter.

End bar.

#[global] Hint Constructors bar : core.

Section bar_relmap.

  Variables (X Y : Type) (f : X → Y → Prop)
            (R : list X → Prop) (S : list Y → Prop)
            (Hf : ∀y, ∃ₜ x, f x y)                     (* f is surjective *)
            (HRS : ∀ l m, Forall2 f l m → R l → S m)   (* f is a morphism form R to S *)
            .

  Theorem bar_relmap l m : Forall2 f l m → bar R l → bar S m.
  Proof.
    intros H1 H2; revert H2 m H1 S HRS.
    induction 1 as [ l Hl | l Hl IHl ]; intros m H1 S HRS.
    * constructor 1; revert Hl; apply HRS; auto.
    * constructor 2; intros y.
      destruct (Hf y) as (x & Hx).
      apply (IHl x); auto.
  Qed.

End bar_relmap.

Section bar_map.

  Variables (A B : Type) (f : A → B) (Hf : ∀b, ∃ₜ a, b = f a)
            (P : list A -> Prop)
            (Q : list B -> Prop)
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

  Local Fact bar_map_fun_rec l : bar P l → ∀m, (∀K, K l → K (map f m)) → bar (λ l, P (map f l)) m.
  Proof.
    induction 1 as [ | l Hl IHl ]; intros m Hm; eauto.
    + constructor 1; now apply Hm.
    + constructor 2; intro.
      apply IHl with (x := f x) (m := _::_).
      intros K; simpl.
      now apply Hm.
  Qed.

  Hint Resolve bar_map_fun_rec : core.

  Fact bar_map_fun_nil : bar P [] → bar (λ l, P (map f l)) [].
  Proof. eauto. Qed.

End bar_map_fun.


