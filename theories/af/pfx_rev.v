(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Arith Lia.

Require Import notations.

Import ListNotations.

Set Implicit Arguments.

Section pfx_rev.

  Variable X : Type.

  Implicit Type (f : nat -> X).

  Fixpoint pfx_rev f n :=
    match n with
      | 0 => []
      | S n => f n :: pfx_rev f n
    end.

  Fact pfx_rev_spec f n x : x ∈ pfx_rev f n <-> exists j, j < n /\ f j = x.
  Proof.
    induction n as [ | n IHn ]; simpl.
    + split; [ | intros (? & ? & ?) ]; lia.
    + rewrite IHn; split.
      * intros [ <- | (j & ? & <-) ].
        - exists n; split; auto; lia.
        - exists j; split; auto; lia.
      * intros (j & H & <-).
        destruct (eq_nat_dec j n) as [ -> | ]; auto.
        right; exists j; split; auto; lia.
  Qed.

  Fact pfx_rev_length f n : ⌊pfx_rev f n⌋ = n.
  Proof. induction n; simpl; auto. Qed.

  Fact pfx_rev_add f a b : pfx_rev f (a+b) = pfx_rev (fun n => f (n+b)) a ++ pfx_rev f b.
  Proof. induction a; simpl; f_equal; auto. Qed.

  Definition pfx_rev_plus := pfx_rev_add.

  Fact pfx_rev_ext f g n : (forall i, i < n -> f i = g i) <-> pfx_rev f n = pfx_rev g n.
  Proof.
    revert f g; induction n as [ | n IHn ]; intros f g; simpl.
    + split; auto; lia.
    + split.
      * intros H; f_equal.
        - apply H; lia.
        - apply IHn; intros; apply H; lia.
      * inversion 1.
        rewrite <- IHn in H2.
        intros i Hi.
        destruct (le_lt_dec n i); auto.
        assert (i = n) as ->; auto; lia.
  Qed.

  Fact pfx_rev_S f n : pfx_rev f (S n) = pfx_rev (fun i => f (S i)) n ++ [ f 0 ].
  Proof.
    replace (S n) with (n+1) by lia; rewrite pfx_rev_plus; f_equal.
    apply pfx_rev_ext; intros; f_equal; lia.
  Qed.

  Fact pfx_rev_cons_inv f n x l : pfx_rev f (S n) = x::l -> f n = x /\ pfx_rev f n = l.
  Proof. simpl; inversion 1; auto. Qed.

  Fact pfx_rev_app_inv f n l m :
       pfx_rev f n = l++m -> pfx_rev (fun n => f (n+⌊m⌋)) ⌊l⌋ = l
                          /\ pfx_rev f ⌊m⌋ = m.
  Proof.
    revert l m; induction n as [ | n IHn ].
    + intros [] []; easy.
    + intros [ | x l ].
      * intros m; simpl; intros <-; simpl.
        rewrite pfx_rev_length; auto.
      * intros m H; simpl in H.
        apply pfx_rev_cons_inv in H as [ <- H ].
        destruct IHn with (1 := H) as [ <- <- ]; simpl; split; auto;
        rewrite !pfx_rev_length; auto.
        do 2 f_equal.
        apply f_equal with (f := @length _) in H.
        rewrite pfx_rev_length, app_length in H; auto.
  Qed.

End pfx_rev.
