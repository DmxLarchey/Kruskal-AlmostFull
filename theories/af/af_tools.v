(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Arith Wellfounded Permutation Utf8.

From KruskalTrees
  Require Import tactics idx vec.

Require Import base notations lift af af_ramsey af_eq.

Import ListNotations idx_notations vec_notations lift_notations.

Set Implicit Arguments.

Fact af_True X : @af X ⊤₂.
Proof. constructor 1; auto. Qed.

Fact af_unit : @af unit eq.
Proof. constructor 1; intros [] []; auto. Qed.

(* idx n ~~ {1,...,n} *)
Fact af_idx n : @af (idx n) eq.
Proof.
  apply af_eq_fin.
  exists (idx_list _); apply idx_list_In.
Qed.

Fact af_le_nat : af le.
Proof.
  constructor 2; intro n.
  induction n as [ n IH ] using (well_founded_induction lt_wf).
  constructor 2; intros m.
  destruct (le_lt_dec n m) as [ | H ].
  + constructor 1; intros; simpl; auto.
  + generalize (IH _ H).
    apply af_mono; firstorder.
Qed.

Fact af_True_right X Y (R : rel₂ X) :
         af R
       → af (λ a b : X+Y,
               match a, b with
               | inl x, inl x' => R x x'
               | inr _, inr _  => True
               | _     , _     => False
               end).
Proof.
  induction 1 as [ R HR | R HR IHR ].
  + do 2 (constructor 2; intros []); constructor 1; intros [] []; simpl; auto.
  + constructor 2; intros [x|y].
    * generalize (IHR x); apply af_mono.
      intros [] []; simpl; tauto.
    * constructor 2; intros [x'|y'].
      - generalize (IHR x'); apply af_mono.
        intros [] []; simpl; tauto.
      - constructor 1; intros [] []; simpl; auto.
Qed.

Fact af_True_left X Y (R : rel₂ Y) :
         af R
       → af (λ a b : X+Y,
               match a, b with
               | inl _, inl _ => True
               | inr x, inr x' => R x x'
               | _     , _    => False
               end).
Proof.
  intros H.
  generalize (af_True_right X H).
  af rel morph (fun u v => match u with inl y => v = inr y | inr x => v = inl x end).
  + intros [x|y]; [ exists (inr x) | exists (inl y) ]; auto.
  + intros [] [] [] []; simpl; try easy.
    do 2 inversion 1; auto.
Qed.

Fact af_option X (R : rel₂ X) :
         af R
       → af (λ x y,
               match x, y with
               | Some x, Some y => R x y
               | None  , None   => True
               | _     , _      => False
               end).
Proof.
  intros HR.
  generalize (@af_True_right _ unit _ HR).
  af rel morph (fun x y => match x, y with inl x, Some y => x = y | inr _, None => True | _, _ => False end).
  + intros [ x | ]; [ exists (inl x) | exists (inr tt) ]; auto.
  + now intros [] [] [] [] ? ?; subst.
Qed.

Section af_product.

  (* We trivially get product, and below sums *)

  Variables (X Y : Type) (R : rel₂ X) (T : rel₂ Y) (HR : af R) (HT : af T).

  Let R' : rel₂ (X*Y) := λ '(x1,y1) '(x2,y2), R x1 x2.
  Let T' : rel₂ (X*Y) := λ '(x1,y1) '(x2,y2), T y1 y2.

  Local Fact HR' : af R'.
  Proof.
    revert HR.
    af rel morph (fun x y => x = fst y).
    + intros []; eauto.
    + intros ? ? [] []; simpl; intros; subst; auto.
  Qed.

  Local Fact HT' : af T'.
  Proof.
    revert HT.
    af rel morph (fun x y => x = snd y).
    + intros []; eauto.
    + intros ? ? [] []; simpl; intros; subst; auto.
  Qed.

  Lemma af_product : af (λ '(x₁,y₁) '(x₂,y₂), R x₁ x₂ ∧ T y₁ y₂).
  Proof.
    apply af_mono with (2 := af_inter HR' HT').
    intros [] []; simpl; auto.
  Qed.

End af_product.

Section af_sum.

  Variables (X Y : Type) (R : rel₂ X)  (T : rel₂ Y) (HR : af R) (HT : af T).

  Lemma af_sum : af (λ u v,
             match u, v with
             | inl x₁, inl x₂ => R x₁ x₂
             | inr y₁, inr y₂ => T y₁ y₂
             | _    , _      => False
             end).
  Proof.
    generalize (af_inter (af_True_right Y HR) (af_True_left X HT)).
    apply af_mono.
    intros [] []; simpl; tauto.
  Qed.

End af_sum.

Fact af_dep_sum n (X : idx n → Type) (R : ∀p, rel₂ (X p)) :
        (∀p, af (R p))
      → af (λ x y : sigT X,
            match x, y with
            | existT _ p x, existT _ q y => ∃e, @R q x↺e y
            end).
Proof.
  revert X R; induction n as [ | n IHn ]; intros X R HR.
  + constructor 1; intros []; idx invert all.
  + generalize (af_sum (HR idx_fst) (IHn _ _ (fun n => HR (idx_nxt n)))).
    af rel morph (fun u v =>
      match u, v with
        | inl x             , existT _ q y => exists e : idx_fst = q, x↺e = y
        | inr (existT _ p x), existT _ q y => exists e : idx_nxt p = q, eq_rect _ X x _ e = y
      end).
    * intros (p & x); idx invert p.
      - exists (inl x), eq_refl; auto.
      - exists (inr (existT _ p x)), eq_refl; auto.
    * intros [ x1 | (p1 & x1) ] [ x2 | (p2 & x2) ]
             (p3 & x3) (p4 & x4) (<- & H1) (<- & H2); simpl in *; try tauto.
      - exists eq_refl; simpl; subst; auto.
      - intros (<- & H3); simpl in *; exists eq_refl; simpl; subst; auto.
Qed.

Fact af_dep_product n (X : idx n → Type) (R : ∀p, rel₂ (X p)) :
        (∀p, af (R p))
      → af (λ u v : ∀p, X p, ∀p, @R p (u p) (v p)).
Proof.
  revert X R; induction n as [ | n IHn ]; intros X R HR.
  + constructor 1; intros; idx invert all.
  + generalize (af_product (HR idx_fst) (IHn _ _ (fun n => HR (idx_nxt n)))).
    af rel morph (fun '(a,x) y => a = y idx_fst /\ forall p : idx n, x p = y (idx_nxt p)).
    * intros y; exists (y idx_fst, fun p => y (idx_nxt p)); auto.
    * intros (a1,x1) (a2,x2) y1 y2 [-> H2] [-> H4] [H5 H6] p; idx invert p; auto.
      rewrite <- H2, <- H4; auto.
Qed.

Fact af_vec_fall2 n X (R : rel₂ X) : af R → af (@vec_fall2 _ _ R n).
Proof.
  intros H; generalize (@af_dep_product n _ _ (fun _ => H)).
  af rel morph (fun x y => forall p, x p = vec_prj y p).
  + intros y; exists (vec_prj y); auto.
  + intros x1 x2 y1 y2 H1 H2 H3 p.
    rewrite <- H1, <- H2; auto.
Qed.
