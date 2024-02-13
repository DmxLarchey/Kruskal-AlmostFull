(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith Lia List Permutation Relations Utf8.

Require Import base notations list_fan list_utils bar.

Import ListNotations list_base_notations.

Set Implicit Arguments.

#[local] Reserved Notation "x '⊳' y" (at level 70, no associativity, format "x  ⊳  y").
#[local] Reserved Notation "l '⌈' R '⌉' m" (at level 70, no associativity, format "l  ⌈ R ⌉  m").

#[local] Notation monotonic R P := (∀ x y, R x y → P x → P y).

Section path.

  Variable (X : Type) (R : X → X → Base).

  Fixpoint path n : X → X → Base :=
    match n with
    | 0   => eq
    | S n => fun x y => ∃ₜ z, path n x z ∧ₜ R z y
    end.

  Fact path_plus n m x y : path (n+m) x y ⇄ₜ ∃ₜ z, path n x z ∧ₜ path m z y.
  Proof.
    revert x y; induction m as [ | m IHn ]; intros x y; simpl.
    + replace (n+0) with n by lia; split.
      * exists y; auto.
      * intros (? & ? & <-); auto.
    + replace (n+S m) with (S (n+m)) by lia; simpl; split.
      * intros (z & H1 & H2).
        apply IHn in H1 as (u & ? & ?); eauto.
      * intros (z & ? & u & ? & ?).
        exists u; split; auto.
        apply IHn; eauto.
  Qed.

  Variable (P : X → Prop) (HP : monotonic R P).

  Fact monotonic_path n : monotonic (path n) P.
  Proof.
    induction n as [ | n IHn ]; simpl.
    + intros; subst; auto.
    + intros ? ? (? & ? & ?) ?; eauto.
  Qed.

End path.

Section bar_r.

  Variable (X : Type) (R : X → X → Base).

  Infix "⊳" := R.

  Implicit Type (P : X → Prop).

  Inductive bar_r	P : X → Base :=
    | bar_r_stop : P ⊆₁ bar_r P
    | bar_r_next x : R x ⊆₁ bar_r P → bar_r P x.

  Notation barᵣ := bar_r.

  Hint Constructors bar_r : core.

  Fact monotonic_bar_r P : monotonic R P → monotonic R (barᵣ P).
  Proof.
    intros H1 x y H2 H3; revert H3 y H2.
    induction 1; eauto.
  Qed.

  Theorem bar_r_rel_seq P (p : nat → X → Base) :
          (∀ n x, p n x → ∃ₜ y, p (S n) y ∧ₜ x ⊳ y)
         → ∀ x, p 0 x → barᵣ P x → ∃ₜ n y, P y ∧ₜ p n y.
  Proof.
    intros H1 x H3 H4; revert H4 p H3 H1.
    induction 1 as [ x Hx | x Hx IHx ]; intros p H1 H2.
    + exists 0, x; split; auto; apply H1; auto.
    + destruct H2 with (1 := H1) as (y & H3 & H4).
      destruct IHx
        with (1 := H4) (p := fun n => p (S n))
        as (? & []); eauto.
  Qed.

  Corollary bar_r_sequence P s : (∀n, s n ⊳ s (S n)) → barᵣ P (s 0) → ∃ₜ n, P (s n).
  Proof.
    intros H1 H2.
    destruct bar_r_rel_seq
      with (P := P) (p := fun n x => s n = x) (x := s 0)
      as (n & y & H3 & <-); eauto.
    intros; subst; eauto.
  Qed.

End bar_r.

#[local] Notation barᵣ := bar_r.
#[local] Hint Constructors bar_r : core.
#[local] Hint Resolve monotonic_bar_r : core.

Section bar_r_map.

  Variables (X Y : Type)
            (P : rel₁ X)
            (R : X → X → Base)
            (S : Y → Y → Base) 
            (f : Y → X)
            (Hf : ∀ x y, S x y → R (f x) (f y)).

  Local Fact bar_r_map_rec x : barᵣ R P x → ∀y, f y = x → barᵣ S (fun y => P (f y)) y.
  Proof. induction 1; intros ? <-; eauto. Qed.

  Hint Resolve bar_r_map_rec : core.

  Lemma bar_r_map y : barᵣ R P (f y) → barᵣ S (λ y, P (f y)) y.
  Proof. eauto. Qed.

End bar_r_map.

#[local] Definition is_tl {X} (l m : list X) :=
  match m with
  | []   => False
  | _::m => m = l
  end.

Section bar_r_iff_bar.

  Variable (X : Type).

  Implicit Type (l : list X) (P : list X → Prop).

  Fact bar_r_iff_bar P l : barᵣ is_tl P l ⇄ₜ bar P l.
  Proof.
    split.
    + induction 1 as [ | l Hl IHl ]; auto.
      constructor 2; intros x; apply IHl; simpl; auto.
    + induction 1 as [ l Hl | l Hl IHl ]; auto.
      constructor 2; intros [ | x m ]; simpl; [ intros [] | intros -> ]; auto.
  Qed.

End bar_r_iff_bar.

Section list_image.

  Variable (X : Type) (R : X → X → Base).

  Infix "⊳" := R.

  Implicit Type (l : list X).

  (* Notice the below definition, depending on Base := Type,
     could be informative and thus tell from which x 
     the y is an R-image of *)

  Definition list_image l m := ∀y, y ∈ₜ m → ∃ₜ x, x ∈ₜ l ∧ₜ x ⊳ y.

  Notation "l '⌈⊳⌉' m" := (list_image l m) (at level 70, no associativity, format "l  ⌈⊳⌉  m").

  Fact list_image_mono l1 l2 m1 m2 : l1 ⊆ₜ l2 → m2 ⊆ₜ m1 → l1 ⌈⊳⌉ m1 → l2 ⌈⊳⌉ m2.
  Proof. intros ? ? H y ?; destruct (H y) as (? & ? & ?); eauto. Qed.

  Fact list_image_cons_inv l y m : l ⌈⊳⌉ y::m → l ⌈⊳⌉ m.
  Proof. intros H ? ?; apply H; auto. Qed.

  Fact list_image_In_inv l y m : l ⌈⊳⌉ m → y ∈ₜ m → l ⌈⊳⌉ [y].
  Proof. intros H ? ? [ <- | [] ]; apply H; auto. Qed.

  Fact list_image_sg_inv x y : [x] ⌈⊳⌉ [y] → x ⊳ y.
  Proof. intros H; destruct (H y) as (? & [ <- | [] ] & ?); auto. Qed.

  Fact list_image_sg x y m : [x] ⌈⊳⌉ m → y ∈ₜ m → x ⊳ y.
  Proof. intros H1 H2; eapply list_image_sg_inv, list_image_In_inv; eauto. Qed.

  (* Critical lemma here *)
  Lemma list_image_split_inv l₁ l₂ m : l₁++l₂ ⌈⊳⌉ m → ∃ₜ m₁ m₂, m ~ₜ m₁++m₂ ∧ₜ l₁ ⌈⊳⌉ m₁ ∧ₜ l₂ ⌈⊳⌉ m₂.
  Proof.
    induction m as [ | x m IHm ]; intros H1.
    + exists nil, nil; repeat split; auto; intros ? [].
    + destruct IHm as (m1 & m2 & H3 & H4 & H5).
      * intros ? ?; apply H1; right; auto.
      * destruct (H1 x) as (y & H6 & H7); [ left; auto | ].
        apply In_t_app_iff in H6 as [ H6 | H6 ].
        - exists (x::m1), m2; repeat split; simpl; eauto.
          intros ? [ <- | ]; eauto.
        - exists m1, (x::m2); repeat split; auto.
          ++ apply perm_t_trans with (1 := perm_t_skip _ H3); auto.
          ++ intros ? [ <- | ]; eauto.
  Qed.

  Fact list_image_perm_t l m k : l ~ₜ m → l ⌈⊳⌉ k → m ⌈⊳⌉ k.
  Proof.
    induction 1 as [ | x l m H IH | x y l | ]; eauto.
    + intros H1 y Hy.
      apply H1 in Hy as (u & [ <- | ? ] & ?).
      * exists x; auto.
      * exists u; split; auto.
        apply perm_t_In_t with (x := u) in H; auto.
    + intros H1 z Hz.
      apply H1 in Hz as (u & ? & ?).
      exists u; split; auto; simpl in *; tauto.
  Qed.

  Variables (P : rel₁ X) (HP : monotonic R P).

  Fact monotonic_list_image : monotonic list_image (Forall P).
  Proof.
    intros l m H1; do 2 rewrite Forall_forall.
    intros H2 y Hy.
    apply In_t_In in Hy as [ Hy ].
    destruct (H1 _ Hy) as (x & Hx1 & Hx2).
    apply inhabits, In_t_In in Hx1.
    generalize (H2 _ Hx1); eauto.
  Qed.

  (* F is a FAN for R is it is a finitary branching sub-relation of R *)

  Definition is_FAN (F : X → X → Base) := F ⊆₂ R ∧ₜ ∀x, ∃ₜ l, ∀y, F x y ⇄ₜ y ∈ₜ l.

  Definition infinite_path (F : X → X → Base) (s : nat → X) := ∀n, F (s n) (s (S n)).

  Theorem FAN_list_image : ∀s : nat → X, infinite_path R s → ∀n, path list_image n [s 0] [s n].
  Proof.
    intros s H.
    induction n as [ | n IHn ]; simpl; trivial.
    exists [s n]; split; eauto.
    intros ? [ <- | [] ]; exists (s n); simpl; split; auto.
  Qed.

End list_image.

#[local] Notation "l ⌈ R ⌉ m" := (list_image R l m).

Section fan_rel.

  (** We give an original proof of a quite general formulation of the FAN theorem over
      general bar inductive predicate *)

  Variable (X : Type) (R : X → X → Base) (P : rel₁ X) (HP : monotonic R P).

  Hint Resolve list_image_perm_t monotonic_list_image In_t_In : core.

  Fact bar_r_list_image_perm_t l m :
            m ~ₜ l
          → barᵣ (list_image R) (Forall P) l
          → barᵣ (list_image R) (Forall P) m.
  Proof.
    intros H1 H2; revert H2 m H1.
    induction 1 as [ l Hl | l Hl IHl ]; intros m Hm.
    + constructor 1.
      revert Hl; rewrite !Forall_forall; intros Hl x Hx.
      apply In_t_In in Hx as [ Hx ].
      apply Hl.
      apply perm_t_In_t with (1 := Hm) in Hx.
      apply In_t_In; exists; auto.
    + constructor 2; intros k ?.
      apply IHl with k; eauto.
  Qed.

  (** The key lemma *)

  Lemma list_image_bar_r_app l m :
           barᵣ (list_image R) (Forall P) l
         → barᵣ (list_image R) (Forall P) m
         → barᵣ (list_image R) (Forall P) (l++m).
  Proof.
    intros Hl; revert Hl m.
    induction 1 as [ l Hl | l Hl IHl ]; intros r Hr.
    + revert r Hr l Hl.
      induction 1 as [ r Hr | r Hr IHr ]; intros l Hl.
      * constructor 1; apply Forall_app; auto.
      * constructor 2; intros m Hm.
        apply list_image_split_inv in Hm as (l' & r' & Hm & ? & ?).
        apply bar_r_list_image_perm_t with (1 := Hm).
        apply IHr; eauto.
    + constructor 2; intros m Hm.
      apply list_image_split_inv in Hm as (l' & r' & Hm & ? & ?).
      apply bar_r_list_image_perm_t with (1 := Hm).
      apply IHl; eauto.
  Qed.

  Let list_image_sg := @list_image_sg _ R.

  Hint Resolve list_image_mono
               list_image_cons_inv
               list_image_In_inv : core.

  (* If x is in the bar of Q then [x] is in the bar of (Forall Q)
     hence Q will be satisfied uniformly over all the iterates of
     the direct images of x, provided we only consider finitely
     many of them at each step *)

  Theorem fan_theorem x : barᵣ R P x → barᵣ (list_image R) (Forall P) [x].
  Proof.
    induction 1 as [ | x _ IHx ]; eauto.
    constructor 2; intros l.
    induction l; intro; eauto.
    apply list_image_bar_r_app with (l := [_]); eauto.
  Qed.

  Hint Resolve fan_theorem : core.

  Theorem fan_theorem_many l :
           (∀x, x ∈ₜ l → barᵣ R P x)
         → barᵣ (list_image R) (Forall P) l.
  Proof.
    induction l; intro; eauto.
    apply list_image_bar_r_app with (l := [_]); auto.
  Qed.

End fan_rel.

Fact fan_list_image_is_tl X (l m : list (list X)) :
         is_tl l m → list_fan l ⌈is_tl⌉ list_fan m.
Proof.
  revert m; intros [ | x m ]; [ intros [] | intros -> ].
  intros m Hm.
  apply In_t_list_fan_iff in Hm.
  destruct m as [ | b m ]; [ inversion Hm | ].
  apply Forall2_t_cons_inv in Hm as (Hm1 & Hm2).
  exists m; split; simpl; auto.
  apply In_t_list_fan_iff; auto.
Qed.

#[local] Hint Resolve fan_list_image_is_tl : core.

Section fan_on_list.

  (* Now we show how to deduce the FAN theorem as stated in Fridlender's paper
     from our "more general" fan theorem

     Remember list_fan is an exponentiation of lists: given
       [l₁;...;lₙ] it produces the list of paths of length n
       that cross each lᵢ, ie it the list of possible choices
       of one element for each lᵢ, ie

           [c₁;...;cₚ] ∈ list_fan [l₁;...;lₙ] iff p = n and cᵢ ∈ lᵢ for each i
   *)

  Variables (X : Type) (P : list X → Prop) (HP : ∀ x l, P l → P (x :: l)).

  Local Fact mono_P : monotonic is_tl P.
  Proof. intros ? [ | ] []; auto. Qed.

  Hint Resolve mono_P : core.

  (* We use list_fan as a relational morphism *)

  Theorem fan_on_list : bar P [] → bar (λ ll, Forall P (list_fan ll)) [].
  Proof.
    intros H; apply bar_r_iff_bar in H; apply bar_r_iff_bar.
    apply fan_theorem in H; eauto.
    revert H.
    change [[]] with (@list_fan X []) at 1.
    apply bar_r_map; auto.
  Qed.

End fan_on_list.

Definition finₜ X (P : X → Base) := ∃ₜ l, ∀ y, P y ⇄ₜ y ∈ₜ l.

Fact finₜ_equiv X (P Q : X → Base) : (∀ x : X, P x ⇄ₜ Q x) → finₜ P → finₜ Q.
Proof.
  intros H (l & Hl); exists l.
  intros y; split; intros H1.
  + now apply Hl, H.
  + now apply H, Hl.
Qed.

Section finₜ_compose.

  Variable (X Y : Type) (R : X → Y → Base) (P : Y → Base).

  (** A very useful lemma to compose finitary relations *)

  Lemma finₜ_compose :
             (∀y, P y → finₜ (λ x, R x y))
           → finₜ P
           → finₜ (λ x, ∃ₜ y, R x y ∧ₜ P y).
  Proof.
    intros H (lP & HP).
    apply finₜ_equiv with (P := fun x => ∃ₜ y, R x y ∧ₜ y ∈ₜ lP).
    + intros x; split; intros (y & ? & ?); exists y; split; auto; apply HP; auto.
    + cut (forall y, y ∈ₜ lP -> finₜ (fun x => R x y)).
      2: intros; apply H, HP; auto.
      clear P HP H.
      induction lP as [ | y lP IHlP ]; intros H.
      * exists nil; intros k; split.
        - intros (? & _ & []).
        - intros [].
      * destruct IHlP as (ll & Hll).
        - intros; apply H; simpl; auto.
        - destruct (H y) as (l & Hl); simpl; auto.
          exists (l++ll); intros x; split.
          ++ intros (y' & H1 & [ <- | H2 ]); apply In_t_app_iff; auto.
             ** left; apply Hl; auto.
             ** right; apply Hll; eauto.
          ++ intros G; apply In_t_app_iff in G as [ G | G ].
             ** exists y; split; auto; apply Hl; auto.
             ** apply Hll in G as (y' & ? & ?).
                exists y'; auto.
  Qed.

End finₜ_compose.

Section FAN.

  Variables (X : Type) (R : X → X → Base) (FAN : ∀x, ∃ₜ l, ∀y, R x y ⇄ₜ y ∈ₜ l).

  Local Fact finₜ_path n x : finₜ (path R n x).
  Proof.
    revert x; induction n as [ | n IHn ]; intros x.
    + exists [x]; intros y; simpl; tauto.
    + destruct (FAN x) as (l & Hl); simpl.
      apply finₜ_equiv with (P := fun y => ∃ₜ z, R z y ∧ₜ path R n x z).
      * firstorder.
      * apply finₜ_compose; auto; intros; apply FAN.
  Qed.

  Variables (P : X → Prop) (HP : monotonic R P) (x : X) (Hx : barᵣ R P x).

  Let p n l := ∀y, path R n x y ⇄ₜ y ∈ₜ l.

  Local Fact Hp0 : p 0 [x].
  Proof. intros y; simpl; tauto. Qed.

  Local Fact Hp1 n l : p n l -> ∃ₜ m, p (S n) m ∧ₜ l ⌈R⌉ m.
  Proof.
    intros Hl.
    destruct (finₜ_path (S n) x) as (m & Hm).
    exists m; split; auto.
    unfold p in Hl.
    intros y Hy.
    apply Hm in Hy; simpl in Hy.
    destruct Hy as (z & H3 & H4).
    apply Hl in H3.
    exists z; auto.
  Qed.

  Local Fact FAN1 : ∃ₜ n, ∀y, path R n x y → P y.
  Proof.
    destruct (@bar_r_rel_seq _ (list_image R) (Forall P) _ Hp1 _ Hp0 (fan_theorem HP Hx))
      as (n & Hn).
    exists n; intros y Hy.
    destruct Hn as (l & H1 & H2).
    apply H2, inhabits, In_t_In in Hy.
    revert y Hy; apply Forall_forall; auto.
  Qed.

  Theorem FAN_theorem : ∃ₜ n, ∀ m y, n ≤ m → path R m x y → P y.
  Proof.
    destruct FAN1 as (n & Hn).
    exists n.
    intros m y H1 H2.
    replace m with (n+(m-n)) in H2 by lia.
    apply path_plus in H2 as (z & H2 & H3).
    apply Hn in H2.
    revert H3 H2; apply monotonic_path; auto.
  Qed.

End FAN.

Check FAN_theorem.


