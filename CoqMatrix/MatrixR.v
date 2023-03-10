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


(** General usage, no need to select low-level model *)
Section test.  

  Let m1 := mat1 3.
  (* Compute m2l m1. *)
  (* Compute m2l (m1 * m1). *)
  
  Goal forall r c (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof. intros. apply madd_comm. Qed.

End test.


(** Symbol matrix *)
Module Exercise_Ch1_Symbol.

  Notation "0" := (A0)%A.
  Notation "1" := (A1)%A.
  Notation "2" := (A1 + A1)%A.
  Notation "3" := (A1 + 2)%A.
  
  (** Power function on A *)
  Fixpoint Apow (a : A) (n : nat) :=
    match n with
    | 0 => A1
    | S n' => (a * (Apow a n'))%A
    end.
  Infix "^" := (Apow).

  Example ex6_1 : forall a b : A,
      let m := (mk_mat_3_3 (a*a) (a*b) (b*b) (2*a) (a+b) (2*b) 1 1 1)%A in
      (det m == (a - b)^3)%A.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Example ex6_2 : forall a b x y z : A,
      let m1 := (mk_mat_3_3
                   (a*x+b*y) (a*y+b*z) (a*z+b*x)
                   (a*y+b*z) (a*z+b*x) (a*x+b*y)
                   (a*z+b*x) (a*x+b*y) (a*y+b*z))%A in
      let m2 := mk_mat_3_3 x y z y z x z x y in
      (det m1 == (a^3 + b^3) * det m2)%A.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Example ex6_3 : forall a b e d : A,
      let m := (mk_mat_4_4
                  (a*a) ((a+1)^2) ((a+2)^2) ((a+3)^2)
                  (b*b) ((b+1)^2) ((b+2)^2) ((b+3)^2)
                  (e*e) ((e+1)^2) ((e+2)^2) ((e+3)^2)
                  (d*d) ((d+1)^2) ((d+2)^2) ((d+3)^2))%A in
      (det m == 0)%A.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Example ex6_4 : forall a b e d : A,
      let m := (mk_mat_4_4
                  1 1 1 1
                  a b e d
                  (a^2) (b^2) (e^2) (d^2)
                  (a^4) (b^4) (e^4) (d^4))%A in
      (det m == (a-b)*(a-e)*(a-d)*(b-e)*(b-d)*(e-d)*(a+b+e+d))%A.
  Proof.
    intros. cbv. ring.
  Qed.
  
  (** 6.(5), it is an infinite structure, need more work, later... *)

End Exercise_Ch1_Symbol.
