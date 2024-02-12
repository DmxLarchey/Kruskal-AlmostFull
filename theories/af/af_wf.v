(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Relations Utf8.

Require Import base notations lift af.

Import lift_notations.

Set Implicit Arguments.

(** The statements and proofs below are cleaned up 
    and more automated versions of those in
      https://github.com/coq-community/almost-full *)

Section wf_af.

  Variables (X : Type).

  Implicit Type (R T : rel₂ X).

  Notation "x '-[' T ']*>' y" := (clos_refl_trans _ T x y) (at level 70, no associativity, format "x  -[ T ]*>  y").
  Notation "x '-[' T ']+>' y" := (clos_trans _ T x y) (at level 70, no associativity, format "x  -[ T ]+>  y").

  Hint Constructors clos_refl_trans clos_trans : core.
  Hint Resolve clos_rt_t : core.

  Fact crt_right T x y z : x -[T]*> y → T y z → x -[T]*> z.   Proof. eauto. Qed.
  Fact ct_right T x y z :  x -[T]*> y → T y z → x -[T]+> z.   Proof. eauto. Qed.

  Hint Resolve crt_right ct_right : core.

  (** When no such scheme exists:
       a T+/R cycle: x ~T~> ... ~T-> z ~R~> x
       a T* chain:   z ~T*~> y 
       branch at a specific point in the above cycle
      and R is almost full
      then y is accessible for T *)
  Lemma Acc_from_af R T y :
       af R 
     → (∀ x z, x -[T]+> z → R z x → z -[T]*> y → False)
     → Acc T y.
  Proof.
    induction 1 as [ R HR | R HR IHR ] in y |- *; intros Hy;
      constructor 1; intros x Hx.
    + destruct (Hy x y); eauto.
    + apply (IHR y).
      intros ? ? ? [] ?; eauto.
  Qed.

  Hint Resolve Acc_from_af : core.

  (* If there is no T+/R cycle: x ~T~> ... ~T~> _ ~R~> x 
     and R is almost full then T is wf *)
  Theorem wf_from_af R T :
       af R
     → (∀ x y, x -[T]+> y → R y x → False)
     → well_founded T.
  Proof. intros ? ? ?; eauto. Qed. 

  (* The strict order associated to wqo,
     ie af (hence refl) and transitive is wf *)  
  Corollary wf_from_wqo R :
       af R
     → transitive _ R
     → well_founded (λ x y, R x y ∧ ¬ R y x).
  Proof.
    intros H1 H2.
    apply wf_from_af with (1 := H1).
    intros x y H3%clos_trans_t1n_iff.
    induction H3 as [ | ? ? ? [] ];
      [ tauto | eauto ].
  Qed.

End wf_af.