(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Q.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Import MatrixAll.


(* ######################################################################### *)
(** * Export matrix theory on concrete elements *)

Module MatrixAllQ.
  Include DecidableFieldMatrixTheory DecidableFieldElementTypeQ.
  Open Scope Q_scope.
  Open Scope mat_scope.
End MatrixAllQ.
  
Module MatrixQ_DL.
  Include MatrixAllQ.DL.
  Open Scope Q_scope.
  Open Scope mat_scope.
End MatrixQ_DL.

Module MatrixQ_DP.
  Include MatrixAllQ.DP.
  Open Scope Q_scope.
  Open Scope mat_scope.
End MatrixQ_DP.

Module MatrixQ_DR.
  Include MatrixAllQ.DR.
  Open Scope Q_scope.
  Open Scope mat_scope.
End MatrixQ_DR.

Module MatrixQ_NF.
  Include MatrixAllQ.NF.
  Open Scope Q_scope.
  Open Scope mat_scope.
End MatrixQ_NF.

Module MatrixQ_SF.
  Include MatrixAllQ.SF.
  Open Scope Q_scope.
  Open Scope mat_scope.
End MatrixQ_SF.


(* ######################################################################### *)
(** * Extended matrix theory *)

(** Set a default model *)
Export MatrixQ_SF.


(** General usage, no need to select low-level model *)
Section Test.
  (* Compute m2l (mat1 4). *)
  (*      = [[1; 0; 0; 0]; [0; 1; 0; 0]; [0; 0; 1; 0]; [0; 0; 0; 1]]
     : list (list A) *)

End Test.


(** Advanced usage, user can select favorite model *)

(** DL *)
Section Test.
  Import MatrixQ_DL.
  
  Let m1 := mat1 3.
  (* Compute @m2l 3 3 m1. *)
  (* Compute @m2l 3 3 (m1 * m1). *)
  (* Compute @m2l 3 3 (m1 * mat0 3 3). *)

  Goal forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof. intros. apply madd_comm. Qed.
End Test.

(** DP *)
Section Test.
  Import MatrixQ_DP.
  
  Let m1 := mat1 3.
  (* Compute @m2l 3 3 m1. *)
  (* Compute @m2l 3 3 (m1 * m1). *)
  (* Compute @m2l 3 3 (m1 * mat0 3 3). *)

  Goal forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof. intros. apply madd_comm. Qed.
End Test.

(** NF *)
Section Test.
  Import MatrixQ_NF.
  
  Let m1 := mat1 3.
  (* Compute @m2l 3 3 m1. *)
  (* Compute @m2l 3 3 (m1 * m1). *)
  (* Compute @m2l 3 3 (m1 * mat0 3 3). *)

  (** (i,j) <- i * 1.0 + j * 0.1 *)
  Let m2 : mat 3 3 := (fun i j => nat2Q i * 1.0 + nat2Q j * 0.1)%Q.
  (* Compute m2l m2. *)
  (* Compute m2l (@mmul 3 3 3 m2 m2). *)
  (*  = [[0.500000000000; 0.530000000000; 0.560000000000];
        [3.500000000000; 3.830000000000; 4.160000000000];
        [6.500000000000; 7.130000000000; 7.760000000000]]
     : list (list A) *)

  Goal forall r c (m1 m2 : mat r c), (m1 + m2) == (m2 + m1).
  Proof.
    (* lma. apply commutative. (* this tactic is enough too. *) *)
    intros. apply madd_comm.
  Qed.
End Test.

(** SF *)
Section Test.
  Import MatrixQ_SF.
  
  Let m1 := mat1 3.
  (* Compute @m2l 3 3 m1. *)
  (* Compute @m2l 3 3 (m1 * m1). *)
  (* Compute @m2l 3 3 (m1 * mat0 3 3). *)

  (** (i,j) <- i * 1.0 + j * 0.1 *)
  Let m2 : mat 3 3 := mk_mat (fun i j => nat2Q i * 1.0 + nat2Q j * 0.1)%Q.
  (* Compute m2l m2. *)
  (* Compute m2l (m2 * m2). *)
  (*  = [[0.500000000000; 0.530000000000; 0.560000000000];
        [3.500000000000; 3.830000000000; 4.160000000000];
        [6.500000000000; 7.130000000000; 7.760000000000]]
     : list (list A) *)

  Goal forall r c (m1 m2 : mat r c), (m1 + m2) == (m2 + m1).
  Proof.
    (* lma. apply commutative. (* this tactic is enough too. *) *)
    intros. apply madd_comm.
  Qed.

End Test.

(** Use different implementations same time, show conversion *)
Section Test.
  Import MatrixAllQ.
  
  Definition m1 : DR.mat 3 3 := DR.mk_mat_3_3 1 2 3 4 5 6 7 8 9.
  (* Compute dr2nf m1. *)
  (* Compute dr2dp m1. *)
  (* Compute dr2dl m1. *)
  
  Definition m2 : DP.mat 3 3 := dr2dp m1.
  (* Compute dp2dr m2. *)
  (* Compute dp2nf m2. *)
  (* Compute dp2dl m2. *)
  
  Definition m3 : DL.mat 3 3 := dp2dl m2.
  (* Compute dl2dr m3. *)
  (* Compute dl2nf m3. *)
  (* Compute dl2dp m3. *)
  
  Definition m4 : NF.mat 3 3 := dl2nf m3.
  (* Compute nf2dr m4. *)
  (* Compute nf2dp m4. *)
  (* Compute nf2dl m4. *)
  
  (* Definition m5 : FF.mat 3 3 := nf2ff m4. *)
  (* The evaluation on FF is crashed! *)
End Test.
