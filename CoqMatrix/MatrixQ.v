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


(** Test for Inversion matrix *)
Module Test_for_Inversion.
  
  (* Symbols *)
  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : Q.
  Variable b1 b2 b3 : Q.
  
  (* Number/Symbol matrix of 2x2 *)
  Definition m20 := mk_mat_2_2 1 2 3 4.
  Definition m21 := mk_mat_2_2 a11 a12 a21 a22.
  
  (* Number/Symbol matrix of 3x3 *)
  Definition m30 := mk_mat_3_3 1 2 3 4 5 6 7 8 10.
  Definition m30_1 := mk_mat_3_3
                        1.25 3.47 4.86
                        8.12 9.85 12.34
                        21.34 0.73 2.35.
  Definition m31 := mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.
  
  (* Remainder (余子式) *)
  (* Compute (m2l (submat m30 0 1)). *)
  (* Compute (m2l (submat m31 2 1)). *)
  
  (* Determinant *)
  (* Compute det m20. *)
  (* Compute det m30. *)
  (* Eval cbn in det m21. *)
  (* Eval cbn in det m31. *)
  
  (* Cramer rule *)
  Definition v31 := mk_mat_3_1 b1 b2 b3.
  (* Compute (m2l m30). *)
  (* Compute (m2l (mchgcol m30 2 v31)). *)
  (* Eval cbn in det (mchgcol m30 2 v31). *)
  (* Eval cbn in cramerRule m30 v31. *)
  
  (* Adj *)
  (* Compute (m2l (madj m20)). *)
  (* Compute (m2l (madj m30)). *)
  
  (* Inverse matrix *)
  (* Compute (m2l (minv m20)). *)
  (* Compute (m2l (minv m30)). *)
  (* Compute (m2l (minv m30_1)). *)
  (* matlab answer of "inv m30" is:
   -0.1109    0.0361    0.0396
   -1.9153    0.7902   -0.1885
    1.6018   -0.5735    0.1244
    our answer is corect too.
   *)
  (* Eval cbn in (m2l (minv m21)). *)
  (* Eval cbn in (m2l (minv m31)). *)


  (** 同济大学，线性代数（第五版），page25, 习题一 *)
  (** 数值矩阵部分，使用特定的域会便于计算，但涉及到符号时，会展开为复杂的表达式，
      不便于符号矩阵的证明 *)
  Module Exercise_Ch1_Number.

    (** 同济大学，线性代数（第五版），page22, 例14 *)
    Section example14.
      Let D := mk_mat_4_4 
                 2 1 (-5) 1
                 1 (-3) 0 (-6)
                 0 2 (-1) 2
                 1 4 (-7) 6.
      Let b := mk_mat_4_1 8 9 (-5) 0.
      
      (* Compute (m2l (cramerRule D b)). *)
    End example14.
    
    Section example15.
      Let D := mk_mat_4_4 
                 1 1 1 1
                 1 2 4 8
                 1 3 9 27
                 1 4 16 64.
      Let b := mk_mat_4_1 3 4 3 (-3).
      
      (* Compute (m2l (cramerRule D b)). *)
    End example15.

    (** ex1 *)
    Section ex_1.
      (* Compute (det (mk_mat_3_3 2 0 1 1 (-4) (-1) (-1) 8 3)). *)

      Variable a b c : Q.
      (* Eval cbn in det (mk_mat_3_3 a b c b c a c a b). *)
      (* ToDo: 不在证明模式时，如何利用Coq环境化简上述表达式？ *)
    End ex_1.
  End Exercise_Ch1_Number.

End Test_for_Inversion.

