(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Arith Lia Utf8.

From KruskalTrees
  Require Import tactics list_fall.

Require Import base notations list_utils.

Import ListNotations list_base_notations.

Set Implicit Arguments.

Section list_prod_t.

  Variable (X Y Z : Type) (f : X → Y → Z).

  Implicit Types (l : list X) (m : list Y).

  Definition list_prod l m := flat_map (λ x, map (f x) m) l.

  Fact In_t_list_prod_iff l m z : z ∈ₜ list_prod l m ⇄ₜ ∃ₜ x y, z = f x y ∧ₜ x ∈ₜ l ∧ₜ y ∈ₜ m.
  Proof.
    unfold list_prod; split; intros H.
    + apply In_t_flat_map_iff in H as (x & H1 & H2).
      apply In_t_map_iff in H2 as (k & H2 & ->); eauto.
    + destruct H as (x & y & -> & ? & ?).
      apply In_t_flat_map_iff; exists x;split; auto.
      apply In_t_map_iff; eauto.
  Qed.

  Fact list_prod_spec l m z : z ∈ list_prod l m ↔ ∃ x y, z = f x y ∧ x ∈ l ∧ y ∈ m.
  Proof.
    rewrite !In_t_In; split.
    + intros [ H ].
      apply In_t_list_prod_iff in H as (x & y & -> & ? & ?).
      exists x, y; rewrite !In_t_In; eauto.
    + intros (x & y & -> & H1 & H2); revert H1 H2.
      rewrite !In_t_In; intros [] []; exists.
      apply In_t_list_prod_iff; eauto.
  Qed.

  Fact list_prod_length l m : ⌊list_prod l m⌋ = ⌊l⌋*⌊m⌋.
  Proof.
    induction l; simpl; auto.
    rewrite app_length, map_length; lia.
  Qed.

End list_prod_t.

Fact map_list_prod X Y Z K (f : X → Y → Z) (g : Z → K) l m :
     map g (list_prod f l m) = list_prod (λ x y, g (f x y)) l m.
Proof.
  unfold list_prod.
  rewrite !flat_map_concat_map, concat_map.
  f_equal.
  rewrite map_map.
  apply map_ext.
  now intros; rewrite map_map.
Qed.

Fact list_prod_map X X' Y Y' Z (f : X' → Y' → Z) (g : X → X') (h : Y → Y') l m :
        list_prod f (map g l) (map h m)
      = list_prod (λ x y, f (g x) (h y)) l m.
Proof.
  unfold list_prod.
  rewrite !flat_map_concat_map.
  f_equal; rewrite map_map.
  apply map_ext.
  now intros; rewrite map_map.
Qed.

Section list_fan_t.

  (** list_fan is the list of choice sequences; see In_t_list_fan_iff *)

  Variable (X : Type).

  Fixpoint list_fan (lw : list (list X)) :=
    match lw with
    | [] => []::[]
    | w::lw => list_prod (@cons _) w (list_fan lw)
    end.

  Fact list_fan_length lw : ⌊list_fan lw⌋ = fold_right (λ x y, ⌊x⌋*y) 1 lw.
  Proof.
    induction lw as [ | w lw IHlw ]; simpl; auto.
    rewrite list_prod_length, <- IHlw; auto.
  Qed.

  Fact In_t_list_fan_iff w lw : w ∈ₜ list_fan lw ⇄ₜ Forall2_t In_t w lw.
  Proof.
    revert w; induction lw as [ | w1 lw IH ]; simpl.
    + intros w; split.
      * intros [ <- | [] ]; auto.
      * inversion 1; auto.
    + intros w; split; intros Hw.
      * apply In_t_list_prod_iff in Hw as (x & w' & -> & H1 & H2).
        apply IH in H2; auto.
      * destruct w as [ | x w ]; [ inversion Hw | ].
        apply Forall2_t_cons_inv in Hw as (H1 & H2).
        apply IH in H2.
        apply In_t_list_prod_iff; eauto.
  Qed.

  Fact list_fan_spec w lw : w ∈ list_fan lw ↔ Forall2 In w lw.
  Proof.
    split.
    + intros H; apply In_t_In in H as [ H ].
      apply In_t_list_fan_iff in H.
      induction H as [ | x y l m H ]; eauto;
      apply inhabits, In_t_In in H; eauto.
    + intros H.
      cut (inhabited (Forall2_t In_t w lw)).
      * intros [H']; now apply In_t_In; exists; apply In_t_list_fan_iff.
      * induction H as [ | x y l m H H1 [ IH1 ] ]; auto;
        apply In_t_In in H as [ H ]; exists; auto.
  Qed.

  Fact list_fan_app_t lw rw v :
            v ∈ₜ list_fan (lw++rw)
         ⇄ₜ v ∈ₜ list_prod app (list_fan lw) (list_fan rw).
  Proof.
    split; intros H.
    + apply In_t_list_prod_iff.
      apply In_t_list_fan_iff in H.
      apply Forall2_t_app_inv_r in H as (l & r & -> & H1 & H2).
      apply In_t_list_fan_iff in H1, H2; eauto.
    + apply In_t_list_prod_iff in H as (l & r & -> & H1 & H2).
      apply In_t_list_fan_iff in H1, H2.
      apply In_t_list_fan_iff; auto.
  Qed.

  Fact list_fan_nil_cons_t rw v :
            v ∈ₜ list_fan ([]::rw) ⇄ₜ ⊥ₜ.
  Proof. split; auto. Qed.

  Fact list_fan_cons_cons_t x w rw v :
            v ∈ₜ list_fan ((x::w)::rw)
         ⇄ₜ v ∈ₜ list_fan ([x]::rw)++list_fan (w::rw).
  Proof. simpl; rewrite <- app_nil_end; tauto. Qed.

  Fact list_fan_cons_sg_t x rw v :
            v ∈ₜ list_fan ([x]::rw)
         ⇄ₜ v ∈ₜ map (cons x) (list_fan rw).
  Proof. simpl; rewrite <- app_nil_end; tauto. Qed.

  Fact list_fan_middle_nil_t lw rw v :
            v ∈ₜ list_fan (lw++[]::rw) ⇄ₜ ⊥ₜ.
  Proof.
    split; try tauto; intros H.
    apply list_fan_app_t, In_t_list_prod_iff
      in H as (l & r & -> & H1 & H2).
    apply list_fan_nil_cons_t in H2; auto.
  Qed.

  Fact list_fan_middle_cons_t lw x w rw v :
            v ∈ₜ list_fan (lw++(x::w)::rw)
         ⇄ₜ v ∈ₜ list_fan (lw++[x]::rw)++list_fan (lw++w::rw).
  Proof.
    split; intros H.
    + apply list_fan_app_t, In_t_list_prod_iff
        in H as (l & r & -> & H1 & H2).
      apply list_fan_cons_cons_t,
            In_t_app_iff in H2.
      apply In_t_app_iff.
      destruct H2 as [ H2 | H2 ]; [ left | right ];
        apply list_fan_app_t, In_t_list_prod_iff; eauto.
    + apply In_t_app_iff in H as [ H | H ];
        apply list_fan_app_t, In_t_list_prod_iff in H
          as (l & r & -> & H1 & H2);
        apply list_fan_app_t, In_t_list_prod_iff;
        exists l, r; rsplit 2; auto;
        apply list_fan_cons_cons_t, In_t_app_iff; auto.
  Qed.

  Tactic Notation "from" "In_t" "with" constr(h) :=
    let H := fresh in rewrite !In_t_In; split; intros [H]; exists; revert H; apply h.

  Fact list_fan_middle_cons lw x w rw v :
             v ∈ list_fan (lw++(x::w)::rw)
           ↔ v ∈ list_fan (lw++[x]::rw)++list_fan (lw++w::rw).
  Proof. from In_t with list_fan_middle_cons_t. Qed.

  Fact list_fan_sg_middle_t lw x rw v :
            v ∈ₜ list_fan (lw++[x]::rw)
         ⇄ₜ v ∈ₜ list_prod (fun a b => a++[x]++b) (list_fan lw) (list_fan rw).
  Proof.
    split; intros H.
    + apply list_fan_middle_cons_t, In_t_app_iff in H as [ H | H ].
      2: apply list_fan_middle_nil_t in H as [].
      apply list_fan_app_t, In_t_list_prod_iff in H
        as (l & r & -> & H1 & H2).
      apply list_fan_cons_sg_t, In_t_map_iff in H2 as (r' & H2 & ->).
      apply In_t_list_prod_iff.
      exists l, r'; rsplit 2; auto.
    + apply In_t_list_prod_iff in H as (l & r & -> & H1 & H2).
      apply list_fan_middle_cons_t, In_t_app_iff; left.
      apply list_fan_app_t, In_t_list_prod_iff; exists l, (x::r); rsplit 2; auto.
      apply list_fan_cons_sg_t, In_t_map_iff; eauto.
  Qed.

  Fact list_fan_sg_right_t lw a v :
           v ∈ₜ list_fan (lw++[a]::nil)
        ⇄ₜ v ∈ₜ map (fun w => w++[a]) (list_fan lw).
  Proof.
    split; intros H.
    + apply list_fan_sg_middle_t, In_t_list_prod_iff in H
        as (l & r & -> & H1 & [ <- | [] ]).
      rewrite <- app_nil_end; apply In_t_map_iff; eauto.
    + apply In_t_map_iff in H as (l & ? & ->).
      apply list_fan_sg_middle_t, In_t_list_prod_iff.
      exists l, []; simpl; eauto.
  Qed.

  Fact list_fan_sg_right lw a v :
            v ∈ list_fan (lw++[a]::nil)
          ↔ v ∈ map (fun w => w++[a]) (list_fan lw).
  Proof. from In_t with list_fan_sg_right_t. Qed.

  Fact list_fan_forall (P : _ → Base) w lw :
             (∀a, a ∈ₜ w → ∀l, l ∈ₜ list_fan lw → P (a::l))
          ⇄ₜ (∀l, l ∈ₜ list_fan (w::lw) → P l).
  Proof.
    split; simpl.
    + intros H l Hl.
      apply In_t_list_prod_iff in Hl as (x & m & -> & H1 & H2); eauto.
    + intros H x Hx m Hm.
      apply H, In_t_list_prod_iff; eauto.
  Qed.

  Fact list_fan_Forall (P : _ → Prop) w lw :
             Forall (λ a, Forall (λ l, P (a::l)) (list_fan lw)) w
           ↔ Forall P (list_fan (w::lw)).
  Proof.
   rewrite !Forall_forall; split; intros H.
   + intros x; rewrite In_t_In; intros [G]; revert x G; apply list_fan_forall.
     intros a Ha l Hl.
     apply inhabits, In_t_In in Ha, Hl.
     apply H in Ha.
     rewrite Forall_forall in Ha; eauto.
   + intros x Hx; rewrite Forall_forall; intros l Hl.
     apply In_t_In in Hx as [ Hx ].
     apply In_t_In in Hl as [ Hl ].
     revert x Hx l Hl; apply list_fan_forall.
     intros l Hl; apply H, In_t_In; eauto.
  Qed.

End list_fan_t.

Fact map_map_list_fan X Y (f : X → Y) l :
     map (map f) (list_fan l) = list_fan (map (map f) l).
Proof.
  induction l as [ | x l IHl ]; simpl; auto.
  rewrite map_list_prod, <- IHl; simpl.
  now rewrite <- list_prod_map.
Qed.
