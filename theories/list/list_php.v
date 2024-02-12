(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import Arith Lia List Permutation Utf8.

Import ListNotations.

Set Implicit Arguments.

#[local] Infix "~ₚ" := (@Permutation _) (at level 70, no associativity).

#[local] Hint Constructors Permutation : core.
#[local] Hint Resolve Permutation_sym Permutation_middle Permutation_app
                      Permutation_sym Permutation_in : core.

#[local] Notation "⌊ l ⌋" := (length l) (at level 0, format "⌊ l ⌋").
#[local] Infix "∈" := In (at level 70, no associativity).
#[local] Infix "⊆" := incl (at level 70, no associativity).

#[global] Notation "'lhd' l" := (∃ x m, l ~ₚ x::x::m) (at level 1).

Section list_has_dup.

  Variable (X : Type).

  Implicit Types (l m : list X) (x : X).

  Fact lhd_nil_inv : lhd (@nil X) ↔ False.
  Proof.
    split; try easy.
    intros (x & m & Hm).
    now apply Permutation_nil in Hm.
  Qed.

  Hint Resolve in_eq : core.

  Fact lhd_cons_inv x l : lhd (x::l) ↔ x ∈ l ∨ lhd l.
  Proof.
    split.
    + intros (y & m & Hm).
      assert (y = x \/ x ∈ m) as [ -> | (l1 & l2 & ->)%in_split ].
      1:{ apply Permutation_in with (x := x) in Hm; auto.
          simpl in Hm; tauto. }
      * apply Permutation_cons_inv, Permutation_sym in Hm; eauto.
      * right; exists y, (l1++l2).
        apply Permutation_cons_inv with x,
              Permutation_trans with (1 := Hm),
              Permutation_sym,
              Permutation_middle with (l1 := _::_::_).
    + intros [ H | (y & m & Hm) ].
      * apply in_split in H as (l1 & l2 & ->).
        exists x, (l1++l2); eauto.
      * exists y, (x::m).
        apply perm_skip with (x := x) in Hm.
        apply perm_trans with (1 := Hm),
              perm_trans with (1 := perm_swap _ _ _); eauto.
  Qed.

End list_has_dup.

Section php_short.

  Variable (X : Type).

  Implicit Types (x : X) (l : list X).

  Hint Resolve incl_nil_l incl_cons
               in_eq in_cons incl_tl
               incl_refl incl_tran : core.

  Reserved Notation "x ↑ n" (at level 1, left associativity, format "x ↑ n").

  Fixpoint repeat x n :=
    match n with
      | 0   => []
      | S n => x::x↑n
    end
  where "x ↑ n" := (repeat x n).

  (* If l ⊆ x::m then, up to permutation, l splits
     in two parts, one consisting in a repetition of x,
     and the other contained in m. Notice that w/o
     a decider equality, we cannot ensure that l'
     does not contain x *)

  Lemma incl_cons_perm l x m : l ⊆ x::m → ∃ n l', l ~ₚ x↑n++l' ∧ l' ⊆ m.
  Proof.
    induction l as [ | y l IHl ].
    + exists 0, []; auto.
    + intros ([ <- | ] & (n & l' & [])%IHl)%incl_cons_inv.
      * exists (S n), l'; split; simpl; auto.
      * exists n, (y::l'); split; auto.
        rewrite <- Permutation_middle; auto.
  Qed.

  (* In the recursive case l ⊆ x::m,
     we get either
        - l ~ₚ l'    and l' ⊆ m (apply IH to l')
        - l ~ₚ x::l' and l' ⊆ m (apply IH to l')
        - l ~ₚ x::x::... and finished
   *)

  Theorem php_short l m : l ⊆ m → ⌊m⌋ < ⌊l⌋ → lhd l.
  Proof.
    revert l; induction m as [ | x m IHm ]; intros l H1 H2.
    + exfalso; revert H2; apply incl_l_nil in H1 as ->; lia.
    + apply incl_cons_perm in H1
        as ([ | [ | n ] ] & l' & H1 & H3);
        simpl in *; eauto;
        destruct (IHm _ H3) as (y & m' & ?).
      * apply Permutation_length in H1 as <-; lia.
      * exists y, m'; eauto.
      * revert H2; apply Permutation_length in H1 as ->; simpl; lia.
      * exists y, (x::m').
        apply perm_trans with (1 := H1); eauto.
  Qed.

End php_short.
