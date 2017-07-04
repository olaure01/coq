(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open EConstr
open Hints
open Tactypes

val e_assumption : unit Proofview.tactic

val registered_e_assumption : unit Proofview.tactic

val e_give_exact : ?flags:Unification.unify_flags -> constr -> unit Proofview.tactic

val prolog_tac : delayed_open_constr list -> int -> unit Proofview.tactic

val gen_eauto : ?debug:debug -> bool * int -> delayed_open_constr list ->
  hint_db_name list option -> unit Proofview.tactic

val eauto_with_bases :
  ?debug:debug ->
  bool * int ->
  delayed_open_constr list -> hint_db list -> Proof_type.tactic

val autounfold : hint_db_name list -> Locus.clause -> unit Proofview.tactic
val autounfold_tac : hint_db_name list option -> Locus.clause -> unit Proofview.tactic
val autounfold_one : hint_db_name list -> Locus.hyp_location option -> unit Proofview.tactic

val make_dimension : int option -> int option -> bool * int
