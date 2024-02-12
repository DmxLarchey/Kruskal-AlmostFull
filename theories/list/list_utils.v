(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Permutation.

Require Import notations base.

Import ListNotations.

Set Implicit Arguments.

#[local] Reserved Notation "x '∈ₜ' y" (at level 70, no associativity, format "x  ∈ₜ  y").
#[local] Reserved Notation "l '⊆ₜ' m" (at level 70, no associativity, format "l  ⊆ₜ  m").
#[local] Reserved Notation "x '~ₜ' y" (at level 70, no associativity, format "x  ~ₜ  y").

Section In_incl_perm_t.

  Variable (X : Type).

  Implicit Type (l : list X).

  Fixpoint In_t x l : Base :=
    match l with
      | []   => ⊥ₜ
      | y::l => y = x ∨ₜ x ∈ₜ l
    end
  where "x ∈ₜ l" := (In_t x l).

  Fact In_t_eq x l : x ∈ₜ x::l.
  Proof. simpl; auto. Qed.

  Fact In_t_cons x y l : x ∈ₜ l -> x ∈ₜ y::l.
  Proof. simpl; auto. Qed.

  Hint Resolve In_t_eq In_t_cons : core.

  Fact In_t_In x l : x ∈ l <-> inhabited (x ∈ₜ l).
  Proof.
    induction l as [ | y l IHl ]; simpl.
    + split; try easy; intros [ [] ].
    + rewrite IHl; split.
      * intros [ -> | [] ]; exists; auto.
      * intros [ [ <- | ] ]; auto.
  Qed.

  Fact In_t_app_iff x l m : x ∈ₜ l++m ⇄ₜ x ∈ₜ l ∨ₜ x ∈ₜ m.
  Proof. split; induction l; simpl; tauto. Qed.

  Inductive perm_t : list X -> list X -> Base :=
    | perm_t_nil : [] ~ₜ []
    | perm_t_skip x l m : l ~ₜ m -> x::l ~ₜ x::m
    | perm_t_swap x y l : x::y::l ~ₜ y::x::l
    | perm_t_trans l m k : l ~ₜ m -> m ~ₜ k -> l ~ₜ k
  where "x ~ₜ y" := (perm_t x y).

  Hint Constructors perm_t : core.

  Fact perm_t_refl l : l ~ₜ l.
  Proof. induction l; eauto. Qed.

  Hint Resolve perm_t_refl : core.

  Fact perm_t_middle x l r : x::l++r ~ₜ l++x::r.
  Proof. induction l; simpl; eauto. Qed.

  Fact perm_t_In_t l m x : l ~ₜ m -> x ∈ₜ l -> x ∈ₜ m.
  Proof.
    intros H; revert H x.
    induction 1; simpl; eauto; try tauto.
    intros ? []; auto.
  Qed.

End In_incl_perm_t.

#[global] Hint Constructors perm_t : core.

#[global] Hint Resolve In_t_eq In_t_cons
                       perm_t_refl perm_t_middle perm_t_In_t : core.

Arguments In_t {_}.
Arguments perm_t {_}.

Module list_base_notations.

  Infix "∈ₜ" := In_t.
  Notation "l ⊆ₜ m" := (forall x, x ∈ₜ l -> x ∈ₜ m).
  Infix "~ₜ" := perm_t.

End list_base_notations.

Import list_base_notations.

Section map.

  Variable (X Y : Type) (f : X -> Y).

  Fact In_t_map_iff l y : y ∈ₜ map f l ⇄ₜ ∃ₜ x, x ∈ₜ l ∧ₜ y = f x.
  Proof.
    revert y; induction l as [ | x l IHl ]; intros y; split; simpl; try tauto.
    + intros (_ & [] & _).
    + intros [ <- | H ]; eauto.
      apply IHl in H as (? & ? & ?); eauto.
    + intros (z & [ <- | ] & ->); eauto.
      right; apply IHl; eauto.
  Qed.

End map.

Section flat_map.

  Variable (X Y : Type) (f : X -> list Y).

  Implicit Type (l : list X).

  Fact In_t_flat_map_iff l y : y ∈ₜ flat_map f l ⇄ₜ ∃ₜ x, x ∈ₜ l ∧ₜ y ∈ₜ f x.
  Proof.
    induction l as [ | x l IHl ]; split; simpl.
    + intros [].
    + intros (x & [] & _).
    + intros H; apply In_t_app_iff in H as [ H | H ]; eauto.
      apply IHl in H as (z & ? & ?); eauto.
    + intros (z & [ <- | Hz ] & H); apply In_t_app_iff; eauto.
      right; apply IHl; eauto.
  Qed.

End flat_map.

Inductive Forall2_t {X Y} (R : X -> Y -> Base) : list X -> list Y -> Base :=
  | Forall2_t_nil : Forall2_t R [] []
  | Forall2_t_cons x l y m : R x y -> Forall2_t R l m -> Forall2_t R (x::l) (y::m).

#[global] Hint Constructors Forall2_t : core.

Fact Forall2_t_xchg X Y R l m :
      @Forall2_t X Y R l m ⇄ₜ Forall2_t (fun y x => R x y) m l.
Proof. split; induction 1; auto. Qed.

Section Forall2_t.

  Variable (X Y : Type) (R : X -> Y -> Base).

  Fact Forall2_t_app l1 r1 l2 r2 :
        Forall2_t R l1 r1
     -> Forall2_t R l2 r2
     -> Forall2_t R (l1++l2) (r1++r2).
  Proof. induction 1; simpl; eauto. Qed.

  Fact Forall2_t_cons_inv x l y m :
        Forall2_t R (x::l) (y::m) ⇄ₜ R x y ∧ₜ Forall2_t R l m.
  Proof.
    split.
    + inversion 1; auto.
    + intros []; auto.
  Qed.

  Fact Forall2_t_app_inv_r l r1 r2 :
         Forall2_t R l (r1++r2)
      -> ∃ₜ l1 l2, l = l1++l2
                ∧ₜ Forall2_t R l1 r1
                ∧ₜ Forall2_t R l2 r2.
  Proof.
    revert l; induction r1 as [ | y r1 IH ]; intros l.
    + exists [], l; eauto.
    + destruct l as [ | x l ]; [ inversion 1 | ]; simpl; intros H.
      apply Forall2_t_cons_inv in H as (H1 & H2).
      apply IH in H2 as (l1 & l2 & -> & H2 & H3).
      exists (x::l1), l2; eauto.
  Qed.

End Forall2_t.

Fact Forall2_t_app_inv_l X Y R l1 l2 r :
         @Forall2_t X Y R (l1++l2) r
      -> ∃ₜ r1 r2, r = r1++r2
                ∧ₜ Forall2_t R l1 r1
                ∧ₜ Forall2_t R l2 r2.
Proof.
  intros H.
  apply Forall2_t_xchg, Forall2_t_app_inv_r
    in H as (r1 & r2 & -> & H1 & H2).
  exists r1, r2; repeat split; auto; apply Forall2_t_xchg; auto.
Qed.

#[global] Hint Resolve Forall2_t_app : core.

