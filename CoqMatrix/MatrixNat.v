(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on nat.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require MatrixAll.

(* ######################################################################### *)
(** * Export matrix theory on concrete elements *)

Module MatrixAllNat.
  Include MatrixAll.
  Include BasicMatrixTheory ElementTypeNat.
  Open Scope nat_scope.
  Open Scope mat_scope.
End MatrixAllNat.

Module MatrixNat_DL.
  Include MatrixAllNat.DL.
  Open Scope nat_scope.
  Open Scope mat_scope.
End MatrixNat_DL.

Module MatrixNat_DP.
  Include MatrixAllNat.DP.
  Open Scope nat_scope.
  Open Scope mat_scope.
End MatrixNat_DP.

Module MatrixNat_DR.
  Include MatrixAllNat.DR.
  Open Scope nat_scope.
  Open Scope mat_scope.
End MatrixNat_DR.

Module MatrixNat_NF.
  Include MatrixAllNat.NF.
  Open Scope nat_scope.
  Open Scope mat_scope.
End MatrixNat_NF.

Module MatrixNat_SF.
  Include MatrixAllNat.SF.
  Open Scope nat_scope.
  Open Scope mat_scope.
End MatrixNat_SF.


(* ######################################################################### *)
(** * Extended matrix theory *)

(** Set a default model *)
Export MatrixNat_SF.


(** General usage, no need to select low-level model *)
Section Test.

  Let m1 := @l2m 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute m2l m1. *)
     (*   = [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] *)
     (* : list (list ElementTypeNat.A) *)

  (* Compute m2l (mmap S m1). *)
     (*   = [[2; 3; 4]; [5; 6; 7]; [8; 9; 10]] *)
     (* : list (list ElementTypeNat.A) *)

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : nat.
  Let m2 := @l2m 3 3 [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  (* Compute m2l m2. *)
  (*      = [[a11; a12; a13]; [a21; a22; a23]; [a31; a32; a33]]
     : list (list ElementTypeNat.A) *)

  (* Compute m2l (mmap S m2). *)
  (*      = [[S a11; S a12; S a13]; [S a21; S a22; S a23]; [S a31; S a32; S a33]]
     : list (list ElementTypeNat.A) *)

End Test.

(** Advanced usage, user can select favorite model *)
Section Test.
  Import MatrixNat_SF.
  Let m1 := @l2m 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute m2l m1. *)
  (* Compute m2l (mmap S m1). *)
  
End Test.
