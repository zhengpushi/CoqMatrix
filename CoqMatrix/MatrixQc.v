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
(** * Export matrix theory on concrete elements *)

Module MatrixAllQc.
  Include DecidableFieldMatrixTheory DecidableFieldElementTypeQc.
  Open Scope Q_scope.
  Open Scope Qc_scope.
  Open Scope mat_scope.
End MatrixAllQc.
  
Module MatrixQc_DL.
  Include MatrixAllQc.DL.
  Open Scope Q_scope.
  Open Scope Qc_scope.
  Open Scope mat_scope.
End MatrixQc_DL.

Module MatrixQc_DP.
  Include MatrixAllQc.DP.
  Open Scope Q_scope.
  Open Scope Qc_scope.
  Open Scope mat_scope.
End MatrixQc_DP.

Module MatrixQc_DR.
  Include MatrixAllQc.DR.
  Open Scope Q_scope.
  Open Scope Qc_scope.
  Open Scope mat_scope.
End MatrixQc_DR.

Module MatrixQc_NF.
  Include MatrixAllQc.NF.
  Open Scope Q_scope.
  Open Scope Qc_scope.
  Open Scope mat_scope.
End MatrixQc_NF.

Module MatrixQc_SF.
  Include MatrixAllQc.SF.
  Open Scope Q_scope.
  Open Scope Qc_scope.
  Open Scope mat_scope.
End MatrixQc_SF.


(* ######################################################################### *)
(** * Extended matrix theory *)

(** Set a default model *)
Export MatrixQc_SF.


(** General usage, no need to select low-level model *)
Section Test.

  Let m1 := @l2m 2 2 (Q2Qc_dlist [[0.1; 0.2]; [1.5; 3.4]]).

  (* Compute m2l (m1 * m1). *)
  (*      = [[{| this := 0.31; canon := Qred_involutive 0.310 |};
         {| this := 0.7; canon := Qred_involutive (875 # 1250) |}];
        [{| this := 21 # 4; canon := Qred_involutive (1050 # 200) |};
         {| this := 593 # 50; canon := Qred_involutive (2965 # 250) |}]]
     : list (list A) *)

End Test.
