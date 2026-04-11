(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(** Base is the sort over which eg af and afs predicates are defined
    Here is the file that should be loaded for the predicative
    and informative version *)

#[global] Abbreviation Base := Type (only parsing).

Module Base_Sums_Products.

  Abbreviation Absurd := Empty_set (only parsing).
  Abbreviation DepSum := sigT (only parsing).
  Abbreviation NonDepSum := sum (only parsing).
  Abbreviation NonDepProd := prod (only parsing).

End Base_Sums_Products.