(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Utf8.

From KruskalTrees
  Require Import tactics.

Require Import base notations lift pfx_rev good.

Import ListNotations lift_notations.

Set Implicit Arguments.

Inductive af {X} (R : rel₂ X) : Base :=
  | af_full : (∀ x y, R x y) → af R
  | af_lift : (∀ x, af (R↑x)) → af R.

Inductive afs {X} (P : rel₁ X) (R : rel₂ X) : Base :=
  | afs_full : (∀ x y, P x → P y → R x y) → afs P R
  | afs_lift : (∀ x, P x → afs P (R↑x)) → afs P R.

Arguments af_full {_ _}.
Arguments af_lift {_ _}.

#[global] Hint Constructors af afs : core.

Fact af_mono X (R T : rel₂ X) : R ⊆₂ T → af R → af T.
Proof. intros H H1; revert H1 T H; induction 1; eauto. Qed.

Fact af_inv X (R : rel₂ X) : af R → ∀x, af (R↑x).
Proof. intros []; auto; constructor 1; simpl; eauto. Qed.

Fact afs_inv U X (R : rel₂ U) : afs X R → ∀x, X x → afs X (R↑x).
Proof. intros []; auto; constructor 1; simpl; eauto. Qed.

#[global] Hint Resolve af_mono : core.

Section afs_iff_af_sub_rel.

  Variables (X : Type) (P : rel₁ X).

  Local Fact af_sub_rel_afs_rec T : af T → ∀R, T ⊆₂ R⇓P → afs P R.
  Proof.
    induction 1 as [ T HT | T HT IHT ]; intros R HR.
    + constructor 1.
      intros x y Hx Hy.
      apply (HR (exist _ x Hx) (exist _ y Hy)); auto.
    + constructor 2; intros x Hx.
      apply (IHT (exist _ x Hx)).
      intros [] []; simpl.
      intros [ G | G ]; [ left | right ]; revert G; apply HR.
  Qed.

  Fact af_sub_rel_afs R : af R⇓P → afs P R.
  Proof. intros H; apply af_sub_rel_afs_rec with (T := R⇓P); auto. Qed.

  Fact afs_af_sub_rel R : afs P R → af R⇓P.
  Proof.
    induction 1 as [ R HR | R HR IHR ];
      [ constructor 1; intros [] | constructor 2 ]; intros []; simpl; eauto.
  Qed.

End afs_iff_af_sub_rel.

#[global] Hint Resolve af_sub_rel_afs afs_af_sub_rel : core.

Proposition afs_iff_af_sub_rel X P R : @afs X P R ⇄ₜ af R⇓P.
Proof. split; auto. Qed.

Section af_rel_morph.

  (** Ideal for transporting af to Σ-types because it is very hard
      to build surjective terms : X → { y : Y | P y } while surjective
      relations X → { y : Y | P y } → Prop are trivial to build

      One can show af R → af T by exhibiting a
      relational surjective morphism from R to T.
  *)

  Variables (X Y : Type) (f : X → Y → Prop)
            (R : rel₂ X) (T : rel₂ Y)
            (Hf : ∀y, ∃ₜ x, f x y)                                        (** f is surjective *)
            (HRT : ∀ x₁ x₂ y₁ y₂, f x₁ y₁ → f x₂ y₂ → R x₁ x₂ → T y₁ y₂)  (** f is a morphism form R to S *)
            .

  Theorem af_rel_morph : af R → af T.
  Proof.
    intros H; revert H T HRT.
    induction 1 as [ R HR | R HR IHR ]; intros T HT.
    + constructor 1; intros y1 y2.
      destruct (Hf y1); destruct (Hf y2); eauto.
    + constructor 2; intros z.
      destruct (Hf z) as (x0 & Hx0).
      apply IHR with (x := x0); firstorder.
  Qed.

End af_rel_morph.

Section afs_rel_morph.

  (** Like for af_relmap

      One can show afs P R → af Q T by exhibiting a
      relational surjective morphism from P/R to Q/T.

   *)

  Variables (X Y : Type) (f : X → Y → Prop)
            (P : rel₁ X) (Q : rel₁ Y)
            (Hf : ∀y, Q y → ∃ₜ x, P x ∧ f x y)
            (R : rel₂ X)  (T : rel₂ Y)
            (HRT : ∀ x₁ x₂ y₁ y₂,
                        P x₁ → P x₂ → Q y₁ → Q y₂
                      → f x₁ y₁ → f x₂ y₂ → R x₁ x₂ → T y₁ y₂).

  Theorem afs_rel_morph : afs P R → afs Q T.
  Proof.
    equiv with afs_iff_af_sub_rel.
    apply af_rel_morph with (f := fun x y => f (proj1_sig x) (proj1_sig y)).
    + intros (y & Hy).
      destruct Hf with (1 := Hy) as (x & Hx & ?).
      exists (exist _ x Hx); eauto.
    + intros [] [] [] []; simpl; eauto.
  Qed.

End afs_rel_morph.

Tactic Notation "af" "rel" "morph" uconstr(g) :=
  match goal with
    | |- af _ → af _ => apply af_rel_morph with (f := g)
    | |- afs _ _ → afs _ _ => apply afs_rel_morph with (f := g)
  end.

(** af rel morph is a very versatile tool *)

Fact afs_mono X (P Q : rel₁ X) (R T : rel₂ X) :
    Q ⊆₁ P
  → (∀ x y, Q x → Q y → R x y → T x y)
  → afs P R → afs Q T.
Proof.
  intros H1 H2.
  af rel morph eq; eauto.
  intros ? ? ? ? _ _ ? ? <- <-; eauto.
Qed.

#[global] Hint Resolve afs_mono : core.

Fact af_af_sub_rel X P (R : rel₂ X) : af R → af R⇓P.
Proof.
  af rel morph (fun x y => x = proj1_sig y).
  + intros []; simpl; eauto.
  + intros ? ? [] [] -> ->; simpl; auto.
Qed.

Fact af_iff_afs_True X (R : rel₂ X) : af R ⇄ₜ afs ⊤₁ R.
Proof.
  split; equiv with afs_iff_af_sub_rel.
  + apply af_af_sub_rel.
  + af rel morph (fun y x => x = proj1_sig y).
    * intros x; exists (exist _ x I); simpl; auto.
    * intros [] [] ? ?; simpl; intros; subst; auto.
Qed.

Fact af_lift_af_sub_rel X R (x₀ : X) : af R↑x₀ → af R⇓(λ x, ¬ R x₀ x).
Proof.
  af rel morph (fun x y => x = proj1_sig y).
  + intros []; simpl; eauto.
  + intros ? ? [] [] -> ->; simpl; tauto.
Qed.

Theorem af_recursion X : ∀ (R : rel₂ X), af R → ∀f, ∃ₜ n, ∃ i j, i < j < n ∧ R (f i) (f j).
Proof.
  refine (fix loop {R} a f { struct a } :=
    match a with
    | af_full h => _
    | af_lift h => let (n,hn) := loop (h (f 0)) (λ n, f (S n)) in _
    end).
  + exists 2. 
    abstract (exists 0, 1; split; auto).
  + exists (S n). 
    abstract (destruct hn as (i & j & Hij & [ H | H ]); 
      [ exists (S i), (S j) | exists 0, (S i) ]; split; auto; tlia).
Defined.

Section af_recursion_total.

  Variable (X : Type).
  Implicit Type (s : nat → X → Prop).

  Definition af_rec_total R :=
     ∀s, (∀n, ∃ₜ x, s n x)
       → ∃ₜ n, ∃ i j xᵢ xⱼ, i < j < n ∧ s i xᵢ ∧ s j xⱼ ∧ R xᵢ xⱼ.

  Definition af_rec_fun R :=
     ∀f : nat → X, ∃ₜ n, ∃ i j, i < j < n ∧ R (f i) (f j).

  (** clearly af R -> af_recursion_total -> af_recursion
      af_recursion -> af R requires choice somehow
      what about af_recursion_total -> af R ??
                 af_recursion -> af_recursion_total (choice here !!!)
 *)

  (* Any total relation nat -> X -> Prop (not just any term nat -> X)
     contains a good pair *)

  Theorem af_af_rec_total : af ⊆₁ af_rec_total.
  Proof.
    induction 1 as [ R HR | R HR IHR ]; intros s Hs.
    + destruct (Hs 0) as (x0 & ?).
      destruct (Hs 1) as (x1 & ?).
      exists 2, 0, 1, x0, x1; auto.
    + destruct (Hs 0) as (x0 & H0).
      destruct (IHR x0 (fun n => s (S n))) as (n & Hn); eauto.
      exists (S n).
      destruct Hn as (i & j & xi & xj & H1 & H2 & H3 & [H4 | H4]).
      * exists (S i), (S j), xi, xj; rsplit 3; auto; tlia.
      * exists 0, (S i), x0, xi; rsplit 3; auto; tlia.
  Qed.

  Theorem af_rec_total_af_rec_fun : af_rec_total ⊆₁ af_rec_fun.
  Proof.
    intros R HR f.
    destruct (HR (fun n x => x = f n)) as (n & Hn); eauto.
    exists n; destruct Hn as (? & ? & ? & ? & ? & -> & -> & ?); eauto.
  Qed.

  Theorem af_af_rec_fun : af ⊆₁ af_rec_fun.
  Proof. intros ? ?; apply af_rec_total_af_rec_fun, af_af_rec_total; auto. Qed.

End af_recursion_total.

