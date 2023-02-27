(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Z.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Import MatrixAll.


(* ######################################################################### *)
(** * Export matrix theory on concrete elements *)

Module MatrixAllZ.
  Include RingMatrixTheory RingElementTypeZ.
  Open Scope Z_scope.
  Open Scope mat_scope.
End MatrixAllZ.
  
Module MatrixZ_DL.
  Include MatrixAllZ.DL.
  Open Scope Z_scope.
  Open Scope mat_scope.
End MatrixZ_DL.

Module MatrixZ_DP.
  Include MatrixAllZ.DP.
  Open Scope Z_scope.
  Open Scope mat_scope.
End MatrixZ_DP.

Module MatrixZ_DR.
  Include MatrixAllZ.DR.
  Open Scope Z_scope.
  Open Scope mat_scope.
End MatrixZ_DR.

Module MatrixZ_NF.
  Include MatrixAllZ.NF.
  Open Scope Z_scope.
  Open Scope mat_scope.
End MatrixZ_NF.

Module MatrixZ_SF.
  Include MatrixAllZ.SF.
  Open Scope Z_scope.
  Open Scope mat_scope.
End MatrixZ_SF.


(* ######################################################################### *)
(** * Extended matrix theory *)

(** Set a default model *)
Export MatrixZ_SF.


(** General usage, no need to select low-level model *)
Section Test.

  (* Import MatrixZ ZArith. *)
  (* Open Scope Z. *)
  (* Open Scope mat_scope. *)

  Let m1 := @l2m 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute m2l m1. *)
  (*      = [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]]
     : list (list RingElementTypeZ.A) *)

  (* Compute m2l (mmap Z.opp m1). *)
  (*      = [[-1; -2; -3]; [-4; -5; -6]; [-7; -8; -9]]
     : list (list RingElementTypeZ.A) *)

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : Z.
  Let m2 := @l2m 3 3 [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  (* Compute m2l m2. *)
  (*      = [[a11; a12; a13]; [a21; a22; a23]; [a31; a32; a33]]
     : list (list RingElementTypeZ.A) *)

  (* Eval cbn in m2l (mmap Z.opp m2). *)
  (*      = [[(- a11)%Z; (- a12)%Z; (- a13)%Z]; [(- a21)%Z; (- a22)%Z; (- a23)%Z];
        [(- a31)%Z; (- a32)%Z; (- a33)%Z]]
     : list (list RingElementTypeZ.A) *)

  Let m3 := mk_mat_3_3 10 11 12 13 14 15 16 17 18.
  (* Eval cbn in m2l (m2 * m2). *)
  (*      = [[Aadd (Amul a11 a11) (Aadd (Amul a12 a21) (Aadd (Amul a13 a31) A0));
         Aadd (Amul a11 a12) (Aadd (Amul a12 a22) (Aadd (Amul a13 a32) A0));
         Aadd (Amul a11 a13) (Aadd (Amul a12 a23) (Aadd (Amul a13 a33) A0))];
        [Aadd (Amul a21 a11) (Aadd (Amul a22 a21) (Aadd (Amul a23 a31) A0));
         Aadd (Amul a21 a12) (Aadd (Amul a22 a22) (Aadd (Amul a23 a32) A0));
         Aadd (Amul a21 a13) (Aadd (Amul a22 a23) (Aadd (Amul a23 a33) A0))];
        [Aadd (Amul a31 a11) (Aadd (Amul a32 a21) (Aadd (Amul a33 a31) A0));
         Aadd (Amul a31 a12) (Aadd (Amul a32 a22) (Aadd (Amul a33 a32) A0));
         Aadd (Amul a31 a13) (Aadd (Amul a32 a23) (Aadd (Amul a33 a33) A0))]]
     : list (list A) *)

  (* Eval cbn in m2l (m1 * m3). *)
  (*      = [[84; 90; 96]; [201; 216; 231]; [318; 342; 366]]
     : list (list A) *)

End Test.

(** Advanced usage, user can select favorite model *)
Section Test.
  Import MatrixZ_SF.
  Let m1 := @l2m 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute m2l m1. *)
  (* Compute m2l (mmap S m1). *)
  
End Test.
