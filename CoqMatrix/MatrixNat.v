(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on nat.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Import MatrixAll.


(* ######################################################################### *)
(** * Matrix theory on Nat *)

(** ** Export matrix theory on concrete elements *)

(** matrix theory with all models *)
Module MatrixAllNat := BasicMatrixTheory ElementTypeNat.
Module MatrixNat_DL := MatrixAllNat.DL.
Module MatrixNat_DP := MatrixAllNat.DP.
Module MatrixNat_DR := MatrixAllNat.DR.
Module MatrixNat_NF := MatrixAllNat.NF.
Module MatrixNat_SF := MatrixAllNat.SF.

(** Extended matrix theory *)
Module MatrixNat.

  Export MatrixNat_SF.

End MatrixNat.


(** ** Test *)
Section Test.
  Import MatrixNat.

  Let m1 := @l2m 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute m2l m1. *)
  (*      = [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]]
     : list (list ElementTypeNat.A) *)

  (* Compute m2l (mmap S m1). *)
  (*      = [[2; 3; 4]; [5; 6; 7]; [8; 9; 10]]
     : list (list ElementTypeNat.A) *)


  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : nat.
  Let m2 := @l2m 3 3 [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  (* Compute m2l m2. *)
  (*      = [[a11; a12; a13]; [a21; a22; a23]; [a31; a32; a33]]
     : list (list ElementTypeNat.A) *)

  (* Compute m2l (mmap S m2). *)
  (*      = [[S a11; S a12; S a13]; [S a21; S a22; S a23]; [S a31; S a32; S a33]]
     : list (list ElementTypeNat.A) *)

End Test.
