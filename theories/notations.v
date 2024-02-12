(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith Lia List.

Arguments In {_}.
Arguments app {_}.

#[global] Infix "∈" := In (at level 70, no associativity).
#[global] Notation "⌊ l ⌋" := (length l) (at level 0, l at level 200, format "⌊ l ⌋").

(** For unary predicates (rel₁) or binary relations rel₂

    *   ⊥₁ and ⊥₂ : empty pred and rel
    *   ⊤₁ and ⊤₂ : full pred and rel
    *   ⊆₁ and ⊆₂ : inclusion
    *   ⧫ ; interstects / have are shared member
    *   ∪₁ and ∪₂ : union
    *   ∩₁ and ∩₂ : intersection
    *   ∘ : composition for binary relations

*)

#[global] Notation "'rel₁' X" := (X -> Prop) (at level 1).
#[global] Notation "'rel₂' X" := (X -> X -> Prop) (at level 1).

#[global] Notation "⊥₁" := (fun _ => False).
#[global] Notation "⊥₂" := (fun _ _ => False).

#[global] Notation "⊤₁" := (fun _ => True).
#[global] Notation "⊤₂" := (fun _ _ => True).

#[global] Notation "P '⊆₁' Q" := (forall x, P x -> Q x) (at level 70, no associativity, format "P  ⊆₁  Q").
#[global] Notation "P '⊆₂' Q" := (forall x y, P x y -> Q x y) (at level 70, no associativity, format "P  ⊆₂  Q").
#[global] Notation "P '⧫' Q" := (exists x, P x /\ Q x) (at level 70, no associativity, format "P  ⧫  Q").

#[global] Notation "P '∪₁' Q" := (fun x => P x \/ Q x) (at level 1, no associativity, format "P ∪₁ Q").
#[global] Notation "P '∪₂' Q" := (fun x y => P x y \/ Q x y) (at level 1, no associativity, format "P ∪₂ Q").
#[global] Notation "P '∩₁' Q" := (fun x => P x /\ Q x) (at level 1, no associativity, format "P ∩₁ Q").
#[global] Notation "P '∩₂' Q" := (fun x y => P x y /\ Q x y) (at level 1, no associativity, format "P ∩₂ Q").

#[global] Notation "Q '∘' P" := (fun x z => exists y, P x y /\ Q y z) (at level 1, left associativity, format "Q ∘ P").
#[global] Notation "P '∙' Q" := (fun x z => exists y, P x y /\ Q y z) (at level 1, left associativity, format "P ∙ Q").

(* Compatibility Layer accross different versions of Coq *)

Definition plus_assoc n m p : n + (m + p) = n + m + p.      Proof. lia. Qed.
Definition le_plus_l n m : n <= n + m.                      Proof. lia. Qed.
Definition le_plus_r n m : m <= n + m.                      Proof. lia. Qed.
Definition le_trans n m p : n <= m -> m <= p -> n <= p.     Proof. lia. Qed.
Definition le_n_Sn n : n <= S n.                            Proof. lia. Qed.
Definition lt_le_trans n m p : n <= m -> m <= p -> n <= p.  Proof. lia. Qed.
Definition lt_0_Sn n : 0 < S n.                             Proof. lia. Qed.
Definition lt_n_S n m : n < m -> S n < S m.                 Proof. lia. Qed.
Definition lt_S_n n m : S n < S m -> n < m.                 Proof. lia. Qed.
Definition lt_le_weak n m : n < m -> n <= m.                Proof. lia. Qed.
Definition lt_irrefl n : ~ n < n.                           Proof. lia. Qed.
Definition le_refl n : n <= n.                              Proof. lia. Qed.

Definition app_nil_end X (l : list X) : l = l ++ nil.
Proof. symmetry; apply app_nil_r. Qed.

Definition app_ass X (l m k : list X) : (l++m)++k = l++(m++k).
Proof. now rewrite app_assoc. Qed.
