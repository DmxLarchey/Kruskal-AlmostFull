(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(** This implements a global switch for the whole library with either

     a) impredicative and non-informative af predicates, ie Base := Prop
     b) predicative and informative af predicates, ie Base := Type

    One can choose between a or b in the base_implem file which
    is a copy of either ../../implem/prop.v or ../../implem/type.v
    selected at compile time.

    Notice that the installed libraries:
    - KruskalAfProp sets Base := Prop
    - KruskalAfType sets Base := Type
    and the uniform *parsing only* notations below
    for "first order syntax".
  *)

Require Export base_notations base_implem.

Import Base_Sums_Products.

(* We have the following correspondance depending on Base := Prop or Type

      +------+-----------+---------+----------+--------------+
      | Base |   ⊥ₜ      |   ∨ₜ    |   ∧ₜ     |   ∃ₜ         |
      +------+-----------+---------+----------+--------------+
      | Prop | False     | ∨ / or  | ∧ / and  | ∃ / ex       |
      | Type | Empty_set | + / sum | * / prod | { & } / sigT |
      +------+-----------+---------+----------+--------------+

   So the notation covers both cases with a common syntax
*)

#[global] Notation "⊥ₜ" := Absurd (only parsing) : type_scope.
#[global] Notation "x ∨ₜ y" := (NonDepSum x y) (only parsing) : type_scope.
#[global] Notation "x ∧ₜ y" := (NonDepProd x y) (only parsing) : type_scope.
#[global] Notation "∃ₜ x .. y , p" := (DepSum (fun x => .. (DepSum (fun y => p)) ..)) (only parsing) : type_scope.

(* Notice that one CANNOT rewrite with ⇄ₜ when Base := Type so we choose
   the denotation ⇄ₜ for informative equivalence instead of ↔ₜ which could 
   otherwise be seen as more "natural". *)

#[global] Notation "P ⇄ₜ Q" := ((P -> Q) ∧ₜ (Q -> P))%type (only parsing) : type_scope.

