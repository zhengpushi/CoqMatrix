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
(** * Matrix theory on R *)

Module MatrixAllQc := DecidableFieldMatrixTheory DecidableFieldElementTypeQc.
Module MatrixQc_DL := MatrixAllQc.DL.
Module MatrixQc_DP := MatrixAllQc.DP.
Module MatrixQc_DR := MatrixAllQc.DR.
Module MatrixQc_NF := MatrixAllQc.NF.
Module MatrixQc_SF := MatrixAllQc.SF.
(* Module MatrixQc_FF := MatrixAllQc.FF. *)
Section Test.
  Import MatrixQc_DL QcExt.
  Open Scope mat_scope.

  Let m1 := @l2m 2 2 (Q2Qc_dlist [[0.1; 0.2]; [1.5; 3.4]]).

  (* Compute m2l (m1 * m1). *)
  (*      = [[{| this := 0.31; canon := Qred_involutive 0.310 |};
         {| this := 0.7; canon := Qred_involutive (875 # 1250) |}];
        [{| this := 21 # 4; canon := Qred_involutive (1050 # 200) |};
         {| this := 593 # 50; canon := Qred_involutive (2965 # 250) |}]]
     : list (list A) *)

End Test.


(** ** Export matrix theory on concrete elements *)

(** matrix theory with all models *)
Module MatrixAllR := DecidableFieldMatrixTheory DecidableFieldElementTypeR.
Module MatrixR_DL := MatrixAllR.DL.
Module MatrixR_DP := MatrixAllR.DP.
Module MatrixR_DR := MatrixAllR.DR.
Module MatrixR_NF := MatrixAllR.NF.
Module MatrixR_SF := MatrixAllR.SF.
(* Module MatrixR_FF := MatrixAllR.FF. *)

Module EqMatrixAllR := EqDecidableFieldMatrixTheory BaseTypeR
                         DecidableFieldElementTypeR.
Module MatrixR_DL_Eq := EqMatrixAllR.DL.
Module MatrixR_DP_Eq := EqMatrixAllR.DP.
Module MatrixR_DR_Eq := EqMatrixAllR.DR.
Module MatrixR_NF_Eq := EqMatrixAllR.NF.
Module MatrixR_SF_Eq := EqMatrixAllR.SF.
Module MatrixR_FF_Eq := EqMatrixAllR.FF.

(** Extended matrix theory *)
Module MatrixR.

  Export RExt.
  Import Sequence.
  
  (** General matrix theory *)
  Export MatrixR_SF_Eq.

  (** Trace of a square matrix *)
  Definition trace {n : nat} (m : smat n) :=
    seqsum (A0:=R0) (Aadd:=Rplus) (fun i => m @ i # i) n.

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

End MatrixR.


(** ** Test *)
Section test.  
  Import MatrixR.
  (* Import RExt List ListNotations. *)
  Open Scope R.
  Open Scope mat_scope.

  Notation "0" := R0.
  Notation "1" := R1.
  
  Example m1 := mat1 3.
  (* Compute m2l m1. *)
  (* Compute m2l (m1 * m1). *)
  
  Example ex1 : forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof.
    intros. apply madd_comm.
  Qed.

End test.

