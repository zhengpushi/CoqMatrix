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
(** * Vector theory on Q *)

(** ** Export vector theory on concrete elements *)

(** vector theory with all models *)
Module VectorAllQ := DecidableFieldVectorTheory DecidableFieldElementTypeQ.
Module VectorQ_DL := VectorAllQ.DL.
Module VectorQ_DP := VectorAllQ.DP.
Module VectorQ_DR := VectorAllQ.DR.
Module VectorQ_NF := VectorAllQ.NF.
Module VectorQ_SF := VectorAllQ.SF.

(** Extended vector theory *)
Module VectorQ.
  Export VectorQ_SF.

End VectorQ.


(** ** Test *)
Section Test.
  Import VectorQ.
  Open Scope Q.
  (* Compute v2l (@l2v 3 [1;2;3]). *)
  
End Test.

(** test FUN *)
Module Demo_usage_NF.
  
  Import QcExt List ListNotations.
  Import VectorQ_NF.
  
  Open Scope Q.
  Open Scope mat_scope.
  
  Example v1 := @l2v 5 (map nat2Q (seq 0 5)).
  (* Compute v2l v1. *)
  (* Compute vdot v1 v1.   *)
  (** (i) <- i * 0.1 *)
  Example v2 : vec 50 := fun i j => ((nat2Q i) * 0.1)%Q.
  (* Compute v2l v2. *)
  (* Compute vdot v2 v2. *)
End Demo_usage_NF.

(** test VDL *)
Module Demo_usage_DL.
  
  Import QExt List ListNotations.
  Import VectorQ_DL.
  
  Open Scope Q.
  Open Scope mat_scope.
  
  Example v1 := @l2v 5 (map nat2Q (seq 0 5)).
  (* Compute v2l v1. *)
  (* Compute vdot v1 v1. *)
  
End Demo_usage_DL.

(** test VDP *)
Module Demo_usage_DP.
  
  Import QExt List ListNotations.
  Import VectorQ_DP.
  
  Open Scope Q.
  Open Scope mat_scope.
  
  Example v1 := @l2v 5 (map nat2Q (seq 0 5)).
  (* Compute v2l v1. *)
  (* Compute vdot v1 v1. *)
  
End Demo_usage_DP.


(** Use different implementations same time, show conversion *)
Module Demo_usage_Mixed.

  Import VectorAllQ.
  
  Import Coq.Vectors.Vector VectorNotations List ListNotations.
  Open Scope Q.
  
  (* 这里 list Q 不能自动转换为 list Qc，有没有什么好办法？ *)
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
  
End Demo_usage_Mixed.
