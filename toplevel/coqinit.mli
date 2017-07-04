(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Initialization. *)

val set_debug : unit -> unit

val set_rcfile : string -> unit

val no_load_rc : unit -> unit
val load_rcfile : Stateid.t -> Stateid.t

val push_include : string -> Names.DirPath.t -> bool -> unit
(** [push_include phys_path log_path implicit] *)

val push_ml_include : string -> unit

val init_load_path : unit -> unit
val init_library_roots : unit -> unit

val init_ocaml_path : unit -> unit

val get_compat_version : ?allow_old:bool -> string -> Flags.compat_version
