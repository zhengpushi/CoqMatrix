(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on R.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Import MatrixAll.


(* ######################################################################### *)
(** * Export matrix theory on concrete elements *)

Module MatrixAllR.
  Export RExt.
  Include EqDecidableFieldMatrixTheory BaseTypeR DecidableFieldElementTypeR.
  Open Scope R_scope.
  Open Scope mat_scope.
End MatrixAllR.
  
Module MatrixR_DL.
  Export RExt.
  Include MatrixAllR.DL.
  Open Scope R_scope.
  Open Scope mat_scope.
End MatrixR_DL.

Module MatrixR_DP.
  Export RExt.
  Include MatrixAllR.DP.
  Open Scope R_scope.
  Open Scope mat_scope.
End MatrixR_DP.

Module MatrixR_DR.
  Export RExt.
  Include MatrixAllR.DR.
  Open Scope R_scope.
  Open Scope mat_scope.
End MatrixR_DR.

Module MatrixR_NF.
  Export RExt.
  Include MatrixAllR.NF.
  Open Scope R_scope.
  Open Scope mat_scope.
End MatrixR_NF.

Module MatrixR_SF.
  Export RExt.
  Include MatrixAllR.SF.
  Open Scope R_scope.
  Open Scope mat_scope.
End MatrixR_SF.

Module MatrixR_FF.
  Export RExt.
  Include MatrixAllR.FF.
  Open Scope R_scope.
  Open Scope mat_scope.
End MatrixR_FF.


(* ######################################################################### *)
(** * Extended matrix theory *)

(** Set a default model *)
Export MatrixR_SF.

(* Import Sequence. *)

(** Trace of a square matrix *)
Definition trace {n : nat} (m : smat n) :=
  seqsum (A0:=R0) (Aadd:=Rplus) (fun i => m!i!i) n.

(** Determinant of 3x3 matrix *)
Definition det3 (m : smat 3) : A :=
  (let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) := m2t_3x3 m in
   let b1 := (a11 * a22 * a33) in
   let b2 := (a12 * a23 * a31) in
   let b3 := (a13 * a21 * a32) in
   let c1 := (a11 * a23 * a32) in
   let c2 := (a12 * a21 * a33) in
   let c3 := (a13 * a22 * a31) in
   let b := (b1 + b2 + b3) in
   let c := (c1 + c2 + c3) in
   (b - c))%A.


(** General usage, no need to select low-level model *)
Section test.  

  Let m1 := mat1 3.
  (* Compute m2l m1. *)
  (* Compute m2l (m1 * m1). *)
  
  Goal forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof. intros. apply madd_comm. Qed.

End test.
