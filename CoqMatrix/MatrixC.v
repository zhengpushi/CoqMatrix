(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on C.
  author    : ZhengPu Shi
  date      : 2023.03
*)

Require Import MatrixAll.


(* ######################################################################### *)
(** * Export matrix theory on concrete elements *)

Module MatrixAllC.
  Export Complex.
  Include EqDecidableFieldMatrixTheory BaseTypeC DecidableFieldElementTypeC.
  Open Scope C_scope.
  Open Scope mat_scope.
End MatrixAllC.
  
Module MatrixC_DL.
  Export Complex.
  Include MatrixAllC.DL.
  Open Scope C_scope.
  Open Scope mat_scope.
End MatrixC_DL.

Module MatrixC_DP.
  Export Complex.
  Include MatrixAllC.DP.
  Open Scope C_scope.
  Open Scope mat_scope.
End MatrixC_DP.

Module MatrixC_DR.
  Export Complex.
  Include MatrixAllC.DR.
  Open Scope C_scope.
  Open Scope mat_scope.
End MatrixC_DR.

Module MatrixC_NF.
  Export Complex.
  Include MatrixAllC.NF.
  Open Scope C_scope.
  Open Scope mat_scope.
End MatrixC_NF.

Module MatrixC_SF.
  Export Complex.
  Include MatrixAllC.SF.
  Open Scope C_scope.
  Open Scope mat_scope.
End MatrixC_SF.

Module MatrixC_FF.
  Export Complex.
  Include MatrixAllC.FF.
  Open Scope C_scope.
  Open Scope mat_scope.
End MatrixC_FF.


(* ######################################################################### *)
(** * Extended matrix theory *)

(** Set a default model *)
Export MatrixC_SF.


(** General usage, no need to select low-level model *)
Section test.  

  Let m1 := mat1 3.
  (* Compute m2l m1. *)
  (* Compute m2l (m1 * m1). *)
  
  Goal forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof. intros. apply madd_comm. Qed.

End test.

