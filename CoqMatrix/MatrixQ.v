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
(** * Matrix theory on Q *)


(** ** Export matrix theory on concrete elements *)

(** matrix theory with all models *)
Module MatrixAllQ := DecidableFieldMatrixTheory DecidableFieldElementTypeQ.
Module MatrixQ_DL := MatrixAllQ.DL.
Module MatrixQ_DP := MatrixAllQ.DP.
Module MatrixQ_DR := MatrixAllQ.DR.
Module MatrixQ_NF := MatrixAllQ.NF.
Module MatrixQ_SF := MatrixAllQ.SF.
(* Module MatrixQ_FF := MatrixAllQ.FF. *)

(** Extended matrix theory *)
Module MatrixQ.
  Export MatrixQ_SF.

End MatrixQ. 


(** ** Test *)
Section Test.
  Import MatrixQ QArith.
  
  (* Compute m2l (mat1 4). *)
  (*      = [[1; 0; 0; 0]; [0; 1; 0; 0]; [0; 0; 1; 0]; [0; 0; 0; 1]]
     : list (list A) *)

End Test.

(** test DL *)
Module Usage_DL.
  
  Import MatrixQ_DL.
  Import QExt List ListNotations.
  
  Open Scope Q_scope.
  Open Scope mat_scope.
  
  Example m1 := mat1 3.
  (* Compute @m2l 3 3 m1. *)
  (* Compute @m2l 3 3 (m1 * m1). *)
  (* Compute @m2l 3 3 (m1 * mat0 3 3). *)

  Example ex1 : forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof.
    intros. apply madd_comm.
  Qed.
  
End Usage_DL.

(** test DP *)
Module Usage_DP.
  
  Import MatrixQ_DP.
  Import QExt List ListNotations.
  
  Open Scope Q_scope.
  Open Scope mat_scope.
  
  Example m1 := mat1 3.
  (* Compute @m2l 3 3 m1. *)
  (* Compute @m2l 3 3 (m1 * m1). *)
  (* Compute @m2l 3 3 (m1 * mat0 3 3). *)

  Example ex1 : forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof.
    intros. apply madd_comm.
  Qed.
  
End Usage_DP.

(** test NF *)
Module Demo_usage_NF.
  
  Import MatrixQ_NF.
  Import QExt List ListNotations.
  
  Open Scope Q_scope.
  Open Scope mat_scope.
  
  Example m1 := mat1 3.
  (* Compute @m2l 3 3 m1. *)
  (* Compute @m2l 3 3 (m1 * m1). *)
  (* Compute @m2l 3 3 (m1 * mat0 3 3). *)

  (** (i,j) <- i * 1.0 + j * 0.1 *)
  Example m2 : mat 3 3 := (fun i j => nat2Q i * 1.0 + nat2Q j * 0.1)%Q.
  (* Compute m2l m2. *)
  (* Tips, NF model need to specify the dimension when perform a computation *)
  (* Compute @m2l 3 3 (@mmul 3 3 3 m2 m2). *)
  (*  = [[0.500000000000; 0.530000000000; 0.560000000000];
        [3.500000000000; 3.830000000000; 4.160000000000];
        [6.500000000000; 7.130000000000; 7.760000000000]]
     : list (list A) *)

  Example ex1 : forall r c (m1 m2 : mat r c), (m1 + m2) == (m2 + m1).
  Proof.
    (* lma. apply commutative. (* this tactic is enough too. *) *)
    intros. apply madd_comm.
  Qed.

End Demo_usage_NF.

(** test SF *)
Module Demo_usage_SF.
  
  Import MatrixQ_SF.
  Import QExt List ListNotations.
  
  Open Scope Q_scope.
  Open Scope mat_scope.
  
  Example m1 := mat1 3.
  (* Compute @m2l 3 3 m1. *)
  (* Compute @m2l 3 3 (m1 * m1). *)
  (* Compute @m2l 3 3 (m1 * mat0 3 3). *)

  (** (i,j) <- i * 1.0 + j * 0.1 *)
  Example m2 : mat 3 3 := mk_mat (fun i j => nat2Q i * 1.0 + nat2Q j * 0.1)%Q.
  (* Compute m2l m2. *)
  (* Compute m2l (m2 * m2). *)
  (*  = [[0.500000000000; 0.530000000000; 0.560000000000];
        [3.500000000000; 3.830000000000; 4.160000000000];
        [6.500000000000; 7.130000000000; 7.760000000000]]
     : list (list A) *)

  Example ex1 : forall r c (m1 m2 : mat r c), (m1 + m2) == (m2 + m1).
  Proof.
    (* lma. apply commutative. (* this tactic is enough too. *) *)
    intros. apply madd_comm.
  Qed.

End Demo_usage_SF.

(** test FF *)
Module Demo_usage_FF.
(*
  Import QcExt List ListNotations.
  Import MatrixQc_FF.
  
  Open Scope Q.
  Open Scope Qc.
  Open Scope mat_scope.
  
  Example m1 := mat1 5.
(*   Compute m2l m1.
  Compute m2l (m1 * m1)%M. *)
  
  Coercion Q2Qc : Q >-> Qc.
  
  (** (i,j) <- i * 1.0 + j * 0.1 *)
(*   Example m2 : M 5 5 := @mk_mat Qc _ _ 
    (fun i j => (nat2Q i) + (nat2Q j) * 0.1)%Qc. *)
(*   Compute m2l m2.
  Compute m2l (m2 * m2)%M. (* todo: Check that why so many 0 *) *)
  
  Example ex1 : forall r c (m1 m2 : M r c), madd m1 m2 = madd m2 m1.
  Proof.
    intros. apply madd_comm.
  Qed.

 *)
End Demo_usage_FF.

(** Use different implementations same time, show conversion *)
Module Demo_usage_All.

  Import MatrixAllQ.
  
  Import Coq.Vectors.Vector VectorNotations List ListNotations.
  Open Scope Q.
  
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
  
End Demo_usage_All.
