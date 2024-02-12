(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(** This is a global switch for the whole code to be developed
    with either

     a) impredicative and non-informative af predicates, ie Base := Prop
     b) predicative and informative af predicates, ie Base := Type

    Comment out exactly one between base_prop or bas_type below
  *)

Require Export base_notations base_implem.

Import Base_Sums_Products.

#[global] Notation "⊥ₜ" := Absurd (only parsing) : type_scope.
#[global] Notation "x ∨ₜ y" := (NonDepSum x y) (only parsing) : type_scope.
#[global] Notation "x ∧ₜ y" := (NonDepProd x y) (only parsing) : type_scope.
#[global] Notation "P ⇄ₜ Q" := ((P -> Q) ∧ₜ (Q -> P))%type (only parsing) : type_scope.
#[global] Notation "∃ₜ x .. y , p" := (DepSum (fun x => .. (DepSum (fun y => p)) ..)) (only parsing) : type_scope.

