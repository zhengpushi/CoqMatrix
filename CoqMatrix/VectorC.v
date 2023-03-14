(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector theory on C.
  author    : ZhengPu Shi
  date      : 2023.3

 *)

Require Import VectorAll.
Require MatrixC.
(* Export HierarchySetoid. *)
(* Export ListNotations. *)
(* Export TupleExt. *)



(* ######################################################################### *)
(** * Export vector theory on concrete elements *)

Module VectorAllC.
  Include DecidableFieldVectorTheory DecidableFieldElementTypeC.
  Open Scope C_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorAllC.
  
Module VectorC_DL.
  Include VectorAllC.DL.
  Open Scope C_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorC_DL.

Module VectorC_DP.
  Include VectorAllC.DP.
  Open Scope C_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorC_DP.

Module VectorC_DR.
  Include VectorAllC.DR.
  Open Scope C_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorC_DR.

Module VectorC_NF.
  Include VectorAllC.NF.
  Open Scope C_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorC_NF.

Module VectorC_SF.
  Include VectorAllC.SF.
  Open Scope C_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorC_SF.


(* ######################################################################### *)
(** * Extended matrix theory *)

(** Export matrix theory on C type *)
Export MatrixC.

(** Set a default model *)
Export VectorC_SF.


(** ** Test *)
Section Test.
  Open Scope C.

  (* Compute v2l (@l2v 3 [1;0;1]). *)

  Notation "0" := R0.
  Notation "1" := R1.
  
  Let v1 := @l2v 5 (map INC (seq 0 5)).
  (* Compute v2l v1. *)
  (* Compute vdot v1 v1. *)

End Test.
