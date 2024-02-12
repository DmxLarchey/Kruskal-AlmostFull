(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(** This defines shared typesetting (but not display) notations for 
    Base := Prop or Base := Type *)

#[global] Reserved Notation "⊥ₜ" (at level 0).
#[global] Reserved Notation "x '∨ₜ' y" (at level 80, right associativity).
#[global] Reserved Notation "x '∧ₜ' y" (at level 80, right associativity).
#[global] Reserved Notation "P '⇄ₜ' Q" (at level 95, no associativity).
#[global] Reserved Notation "'∃ₜ' x .. y , p" (at level 200, x binder, right associativity).
