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
  Require Import list_utils.

Require Import base notations lift pfx_rev.

Import ListNotations lift_notations.

Set Implicit Arguments.

#[local] Hint Resolve in_or_app in_eq in_cons : core.

Section good_base.

  Variable X : Type.

  Implicit Type (R T : rel₂ X).

  (* Inductive characterization of a good list, ie
     l = [x1;...;xn] is good for R if R xi xj for some j < i,
     see good_iff_split below *)

  Inductive good R : list X → Prop :=
    | good_stop x y l : y ∈ l → R y x → good R (x::l)
    | good_skip x l : good R l → good R (x::l).

  Hint Constructors good : core.

  Fact good_mono R T : R ⊆₂ T → good R ⊆₁ good T.
  Proof. induction 2; eauto. Qed.

  Fact good_app_left R l m : good R m → good R (l++m).
  Proof. induction l; simpl; eauto. Qed.

  Fact good_app_right R l m : good R l → good R (l++m).
  Proof. induction 1; simpl; eauto. Qed.

  Hint Resolve good_app_left good_app_right : core.

  Fact good_snoc R x l y : x ∈ l → R y x → good R (l++[y]).
  Proof.
    intros H1 H2; apply in_split in H1 as (? & ? & ->).
    rewrite app_ass; simpl; eauto.
  Qed.

  Hint Resolve good_snoc : core.

  Fact good_rel_lift R l x : good R↑x l → good R (l++[x]).
  Proof. induction 1 as [ ? ? ? ? [] | ]; simpl; eauto. Qed.

  Hint Resolve good_rel_lift : core.

  Fact good_rel_lift_list R m l : good (R⇈l) m → good R (m++l).
  Proof.
    revert m; induction l as [ | x l IHl ]; simpl; intros m Hm.
    + now rewrite <- app_nil_end.
    + replace (m++x::l) with ((m++[x])++l); auto.
      now rewrite app_ass.
  Qed.

  Fact good_length R l : good R l → 2 <= ⌊l⌋.
  Proof. induction 1 as [ ? ? [] | ]; simpl in *; lia. Qed.

  Fact good_nil_inv R : good R [] ↔ False.
  Proof. split; inversion 1. Qed.

  Fact good_cons_inv R x l :
         good R (x::l) ↔ (∃y, y ∈ l ∧ R y x) ∨ good R l.
  Proof. split; [ inversion 1 | intros [ (? & ? & ?) | ] ]; eauto. Qed.

  Fact good_sg_inv R x : good R [x] ↔ False.
  Proof.
    split; try tauto.
    rewrite good_cons_inv, good_nil_inv.
    simpl; firstorder.
  Qed.

  Fact good_pair_inv R x y : good R [y;x] ↔ R x y.
  Proof.
    split.
    + rewrite good_cons_inv, good_sg_inv.
      intros [ (? & [ <- | [] ] & ?) | [] ]; auto.
    + constructor 1 with x; auto.
  Qed.

  Fact good_app_inv R l m :
       good R (l++m) ↔ good R l ∨ good R m ∨ ∃ x y, x ∈ l ∧ y ∈ m ∧ R y x.
  Proof.
    split.
    + induction l as [ | x l IHl ]; simpl; auto.
      intros [ (y & []%in_app_iff & ?) 
             | [ | [ | (y & z & ? & ? & ?) ] ]%IHl ]%good_cons_inv; eauto.
      * do 2 right; exists x, y; eauto.
      * do 2 right; exists y, z; eauto.
    + intros [ | [ | (? & ? & (? & ? & ->)%in_split & ? & ?) ] ]; auto.
      rewrite app_ass; simpl; eauto.
  Qed.

  Lemma good_iff_split R ll :
        good R ll ↔ ∃ l x m y r, R y x ∧ ll = l++x::m++y::r.
  Proof.
    split.
    + induction 1 as [ x y ? (l & r & ->)%in_split | x ll _ (l & a & m & b & r & ? & ->) ].
      * exists [], x, l, y, r; auto.
      * exists (x::l), a, m, b, r; auto.
    + intros (? & ? & ? & ? & ? & ? & ->); eauto.
  Qed.

  Fact good_rel_lift_rev R l x : good R (l++[x]) → ∀y, good R↑x (y::l).
  Proof.
    intros [ H | [ []%good_sg_inv | (a & b & ? & [ <- | [] ] & ?) ] ]%good_app_inv.
    + constructor 2; revert H; apply good_mono; left; auto.
    + constructor 1 with a; auto; right; auto.
  Qed.

  Lemma good_rel_lift_rev_iff R l x :
         good R (l++[x])
       ↔ good R↑x l
       ∨ match l with
         | []   => False
         | y::_ => R x y
         end.
  Proof.
    split.
    + intros [ H | [ []%good_sg_inv | (a & b & H1 & [ <- | [] ] & H3) ] ]%good_app_inv.
      * destruct l as [ | y l ].
        - now apply good_nil_inv in H.
        - apply good_cons_inv in H as [ (z & []) | H ].
          ++ left; constructor 1 with z; simpl; auto.
          ++ left; constructor 2; revert H; apply good_mono; simpl; tauto.
      * destruct l as [ | y l ]; auto.
        destruct H1 as [ <- | H ]; auto.
        left; constructor 1 with a; simpl; auto.
    + intros [ H | H ].
      * apply good_rel_lift in H; auto.
      * destruct l as [ | y l ]; try easy.
        simpl; constructor 1 with x; auto.
  Qed.

  Fact rel_lift_rel_iff_good R l x y :
          R⇈l x y ↔ good R l ∨ (∃z, z ∈ l ∧ R z x) ∨ R x y.
  Proof.
    induction l as [ | a l IHl ] in x, y |- *; simpl.
    + rewrite good_nil_inv; firstorder.
    + rewrite !IHl, good_cons_inv; split.
      * intros [ [ | [ (z & []) | ] ] | [ | [ (z & []) | ] ] ]; eauto.
        - right; left; exists z; auto.
        - right; left; exists a; eauto.
      * intros [ [ | ] | [ (z & [ <- | ] & ?) | ] ]; eauto.
        left; right; left; eauto.
  Qed.

  Fact good_pfx_rev R f n :
           good R (pfx_rev f n)
         ↔ ∃ i j, i < j < n ∧ R (f i) (f j).
  Proof.
    split.
    + induction n as [ | n IHn ]; simpl.
      * rewrite good_nil_inv; tauto.
      * rewrite good_cons_inv; intros [ (x & H1 & H2) | H ].
        - apply pfx_rev_spec in H1 as (j & H1 & <-).
          exists j, n; split; auto; lia.
        - apply IHn in H as (i & j & ? & ?); exists i, j; split; auto; lia.
    + intros (i & j & H1 & H2).
      replace n with ((n-j-1) + 1 + (j-i-1) + 1 + i) by lia.
      rewrite !pfx_rev_add, !app_ass; simpl.
      replace (j-i-1+1+i) with j by lia; eauto.
  Qed.

End good_base.

#[global] Hint Constructors good : core.
#[global] Hint Resolve good_app_left good_app_right : core.

Section good_sub_rel.

  Variable (X : Type) (P : rel₁ X) (R : rel₂ X).

  Fact good_sub_rel l : good R⇓P l
                      ↔ good R (map (@proj1_sig _ _) l)
                      ∧ Forall P (map (@proj1_sig _ _) l).
  Proof.
    split.
    + intros H; split.
      * induction H as [ (x&Hx) (y&Hy) l H1 H2 | (x&?) l H IH ]; simpl; auto.
        constructor 1 with y; auto; apply in_map_iff; exists (exist _ _ Hy); auto.
      * clear H; induction l as [ | [] ]; simpl; eauto.
    + intros [ H1 H2 ].
      induction l as [ | (x & Hx) l IH ].
      * apply good_nil_inv in H1 as [].
      * simpl in *.
        apply Forall_cons_inv in H2 as (_ & H2).
        apply good_cons_inv in H1 as [ (y & H3 & H4) | H1 ].
        - apply in_map_iff in H3 as (y' & E & H3).
          constructor 1 with y'; subst; auto.
        - constructor 2; auto.
  Qed.

  Fact good_map_proj1_sig l l' :
        map (@proj1_sig _ _) l = map (@proj1_sig _ _) l'
      → good R⇓P l
      → good R⇓P l'.
  Proof.
    intros H1 H2.
    apply good_sub_rel.
    rewrite <- H1.
    now apply good_sub_rel.
  Qed.

End good_sub_rel.

