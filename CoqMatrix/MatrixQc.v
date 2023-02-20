(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Qc.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Import MatrixAll.


(* ######################################################################### *)
(** * Matrix theory on Qc *)

(** ** Export matrix theory on concrete elements *)

(** matrix theory with all models *)
Module MatrixAllQc := DecidableFieldMatrixTheory DecidableFieldElementTypeQc.
Module MatrixQc_DL := MatrixAllQc.DL.
Module MatrixQc_DP := MatrixAllQc.DP.
Module MatrixQc_DR := MatrixAllQc.DR.
Module MatrixQc_NF := MatrixAllQc.NF.
Module MatrixQc_SF := MatrixAllQc.SF.
(* Module MatrixQc_FF := MatrixAllQc.FF. *)

(** Extended matrix theory *)
Module MatrixQc.
  Export MatrixQc_SF.

End MatrixQc.


(** ** Test *)
Section Test.
  Import MatrixQc QcExt.
  Open Scope mat_scope.

  Let m1 := @l2m 2 2 (Q2Qc_dlist [[0.1; 0.2]; [1.5; 3.4]]).

  (* Compute m2l (m1 * m1). *)
  (*      = [[{| this := 0.31; canon := Qred_involutive 0.310 |};
         {| this := 0.7; canon := Qred_involutive (875 # 1250) |}];
        [{| this := 21 # 4; canon := Qred_involutive (1050 # 200) |};
         {| this := 593 # 50; canon := Qred_involutive (2965 # 250) |}]]
     : list (list A) *)

End Test.
