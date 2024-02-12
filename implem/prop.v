(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(** Base is the sort over which eg af and afs predicates are defined
    Here is the file that should be loaded for the impredicative
    and non informative version *)

#[global] Notation Base := Prop (only parsing).

Module Base_Sums_Products.

  Notation Absurd := False (only parsing).
  Notation DepSum := ex (only parsing).
  Notation NonDepSum := or (only parsing).
  Notation NonDepProd := and (only parsing).

End Base_Sums_Products.

