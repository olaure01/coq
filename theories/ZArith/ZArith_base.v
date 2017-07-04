(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Library for manipulating integers based on binary encoding.
    These are the basic modules, required by [Omega] and [Ring] for instance.
    The full library is [ZArith]. *)

Require Export BinNums.
Require Export BinPos.
Require Export BinNat.
Require Export BinInt.
Require Export Zcompare.
Require Export Zorder.
Require Export Zeven.
Require Export Zminmax.
Require Export Zmin.
Require Export Zmax.
Require Export Zabs.
Require Export Znat.
Require Export auxiliary.
Require Export ZArith_dec.
Require Export Zbool.
Require Export Zmisc.
Require Export Wf_Z.

Hint Resolve Z.le_refl Z.add_comm Z.add_assoc Z.mul_comm Z.mul_assoc Z.add_0_l
  Z.add_0_r Z.mul_1_l Z.add_opp_diag_l Z.add_opp_diag_r Z.mul_add_distr_l
  Z.mul_add_distr_r: zarith.

Require Export Zhints.
