(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector theory on Q.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Import VectorAll.


(* ######################################################################### *)
(** * Export vector theory on concrete elements *)

Module VectorAllQ.
  Include DecidableFieldVectorTheory DecidableFieldElementTypeQ.
  Open Scope Q_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorAllQ.
  
Module VectorQ_DL.
  Include VectorAllQ.DL.
  Open Scope Q_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorQ_DL.

Module VectorQ_DP.
  Include VectorAllQ.DP.
  Open Scope Q_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorQ_DP.

Module VectorQ_DR.
  Include VectorAllQ.DR.
  Open Scope Q_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorQ_DR.

Module VectorQ_NF.
  Include VectorAllQ.NF.
  Open Scope Q_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorQ_NF.

Module VectorQ_SF.
  Include VectorAllQ.SF.
  Open Scope Q_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorQ_SF.


(* ######################################################################### *)
(** * Extended matrix theory *)

(** Set a default model *)
Export VectorQ_SF.


(** General usage, no need to select low-level model *)
Section Test.
  (* Compute v2l (@l2v 3 [1;2;3]). *)
  
End Test.

(** Advanced usage, user can select favorite model *)

(* NF *)
Section Test.
  Import VectorQ_NF.
  
  Let v1 := @l2v 5 (map nat2Q (seq 0 5)).
  (* Compute v2l v1. *)
  (* Compute vdot v1 v1. *)
  (** (i) <- i * 0.1 *)
  Let v2 : vec 50 := fun i j => ((nat2Q i) * 0.1)%Q.
  (* Compute v2l v2. *)
  (* Compute vdot v2 v2. *)
End Test.

(* DL *)
Section Test.
  Import VectorQ_DL.

  Let v1 := @l2v 5 (List.map nat2Q (seq 0 5)%nat).
  (* Compute v2l v1. *)
  (* Compute vdot v1 v1. *)
  
End Test.

(* DP *)
Section Test.
  Import VectorQ_DP.
  
  Let v1 := @l2v 5 (map nat2Q (seq 0 5)).
  (* Compute v1. *)
  (* Compute v2l v1. *)
  (* Compute vdot v1 v1. *)
  
End Test.


(** Use different implementations same time, show conversion *)
Section Test.
  Import VectorAllQ.
  
  Definition v1 : DR.vec 5 := DR.l2v [1; 2; 3; 4; 5].
  (* Compute dr2nf v1. *)
  (* Compute dr2dp v1. *)
  (* Compute dr2dl v1. *)
  
  Definition v2 : NF.vec 5 := dr2nf v1.
  (* Compute nf2dr v2. *)
  (* Compute nf2dp v2. *)
  (* Compute nf2dl v2. *)

  Definition v3 : DP.vec 5 := nf2dp v2.
  (* Compute dp2dr v3. *)
  (* Compute dp2nf v3. *)
  (* Compute dp2dl v3. *)
  
  Definition v4 : DL.vec 5 := dr2dl v1.
  (* Compute dl2dr v4. *)
  (* Compute dl2nf v4. *)
  (* Compute dl2dp v4. *)
  
End Test.
