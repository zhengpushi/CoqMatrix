(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Entrance for access all vector.
  author    : ZhengPu Shi
  date      : 2021.12
 *)


Require Export ElementType VectorTheory.

Require Import
  DepPair.VectorTheoryDP
  DepList.VectorTheoryDL
  DepRec.VectorTheoryDR
  NatFun.VectorTheoryNF
(* FinFun.VectorTheoryFF *)
.



(* ######################################################################### *)
(** * Collection of all implementations for basic vector theory *)
Module BasicVectorTheory (E : ElementType).

  (** export base element, contain: types, definitions, notations, etc.  *)
  Export E.
  
  (* ======================================================================= *)
  (** ** Short name for concrete implementations *)
  Module DP <: BasicVectorTheory E := BasicVectorTheoryDP E.
  Module DL <: BasicVectorTheory E := BasicVectorTheoryDL E.
  Module DR <: BasicVectorTheory E := BasicVectorTheoryDR E.
  Module NF <: BasicVectorTheory E := BasicVectorTheoryNF E.
  (* Module FF <: BasicVectorTheory E := BasicVectorTheoryFF E. *)


  (* ======================================================================= *)
  (** ** Conversion between different implementations *)

  (** DR -- NF *)
  Definition dr2nf {n} (v : DR.vec n) : NF.vec n := NF.l2v (DR.v2l v).
  Definition nf2dr {n} (v : NF.vec n) : DR.vec n := DR.l2v (NF.v2l v).

(*
  Lemma dr2nf_nf2dr_id : forall n (v : NF.vec n), NF.veq (dr2nf (nf2dr v)) v.
  Proof.
    intros. unfold dr2nf,nf2dr. rewrite DR.v2l_l2v_id.
    apply NF.l2v_v2l_id; auto. apply NF.v2l_length.
  Qed.
  
  Lemma nf2dr_dr2nf_id : forall n (v : DR.vec n), 
      nf2dr (dr2nf v) = v.
  Proof.
    intros. unfold dr2nf,nf2dr. rewrite NF.v2l_l2v_id.
    apply DR.l2v_v2l_id. apply DR.v2l_length.
  Qed.
 *)
  
  (** VLL -- VDP *)
  Definition dr2dp {n} (v : DR.vec n) : DP.vec n := DP.l2v (DR.v2l v).
  Definition dp2dr {n} (v : DP.vec n) : DR.vec n := DR.l2v (DP.v2l v).
(*  
  Lemma dr2dp_dp2dr_id : forall n (v : DP.vec n), 
      dr2dp (dp2dr v) = v.
  Proof.
    intros. unfold dr2dp,dp2dr. rewrite DR.v2l_l2v_id.
    apply DP.l2v_v2l_id; auto. apply DP.v2l_length.
  Qed.
  
  Lemma dp2dr_dr2dp_id : forall n (v : DR.vec n), 
      dp2dr (dr2dp v) = v.
  Proof.
    intros. unfold dr2dp,dp2dr. rewrite DP.v2l_l2v_id.
    apply DR.l2v_v2l_id. apply DR.v2l_length.
  Qed.
 *)
  
  (** VLL -- VDL *)
  Definition dr2dl {n} (v : DR.vec n) : DL.vec n := DL.l2v (DR.v2l v).
  Definition dl2dr {n} (v : DL.vec n) : DR.vec n := DR.l2v (DL.v2l v).
(*
  Lemma dr2dl_dl2dr_id : forall n (v : DL.vec n), 
      dr2dl (dl2dr v) = v.
  Proof.
    intros. unfold dr2dl,dl2dr. rewrite DR.v2l_l2v_id.
    apply DL.l2v_v2l_id. apply DL.v2l_length.
  Qed.
  
  Lemma dl2dr_dr2dl_id : forall n (v : DR.vec n), 
      dl2dr (dr2dl v) = v.
  Proof.
    intros. unfold dr2dl,dl2dr. rewrite DL.v2l_l2v_id.
    apply DR.l2v_v2l_id. apply DR.v2l_length.
  Qed.
 *)
  
  (** FUN -- VDP *)
  Definition nf2dp {n} (v : NF.vec n) : DP.vec n := DP.l2v (NF.v2l v).
  Definition dp2nf {n} (v : DP.vec n) : NF.vec n := NF.l2v (DP.v2l v).
(*
  Lemma nf2dp_dp2nf_id : forall n (v : DP.vec n), 
      nf2dp (dp2nf v) = v.
  Proof.
    intros. unfold nf2dp,dp2nf. rewrite NF.v2l_l2v_id.
    apply DP.l2v_v2l_id. apply DP.v2l_length.
  Qed.
  
  Lemma dp2nf_nf2dp_id : forall n (v : NF.vec n), 
      dp2nf (nf2dp v) = v.
  Proof.
    intros. unfold dp2nf,nf2dp. rewrite DP.v2l_l2v_id.
    apply NF.l2v_v2l_id; auto. apply NF.v2l_length.
  Qed.
 *)
  
  (** FUN -- VDL *)
  Definition nf2dl {n} (v : NF.vec n) : DL.vec n := DL.l2v (NF.v2l v).
  Definition dl2nf {n} (v : DL.vec n) : NF.vec n := NF.l2v (DL.v2l v).
  
(*
  Lemma nf2dl_dl2nf_id : forall n (v : DL.vec n), 
      nf2dl (dl2nf v) = v.
  Proof.
    intros. unfold nf2dl,dl2nf. rewrite NF.v2l_l2v_id.
    apply DL.l2v_v2l_id. apply DL.v2l_length.
  Qed.
  
  Lemma dl2nf_nf2dl_id : forall n (v : NF.vec n), 
      dl2nf (nf2dl v) = v.
  Proof.
    intros. unfold nf2dl,dl2nf. rewrite DL.v2l_l2v_id.
    apply NF.l2v_v2l_id; auto. apply NF.v2l_length.
  Qed.
 *)
  
  (** DP -- DL *)
  Definition dp2dl {n} (v : DP.vec n) : DL.vec n := DL.l2v (DP.v2l v).
  Definition dl2dp {n} (v : DL.vec n) : DP.vec n := DP.l2v (DL.v2l v).

(*
  Lemma dp2dl_dl2dp_id : forall n (v : DL.vec n), 
      dp2dl (dl2dp v) = v.
  Proof.
    intros. unfold dp2dl,dl2dp. rewrite DP.v2l_l2v_id.
    apply DL.l2v_v2l_id. apply DL.v2l_length.
  Qed.
  
  Lemma dl2dp_dp2dl_id : forall n (v : DP.vec n), 
      dl2dp (dp2dl v) = v.
  Proof.
    intros. unfold dp2dl,dl2dp. rewrite DL.v2l_l2v_id.
    apply DP.l2v_v2l_id; auto. apply DP.v2l_length.
  Qed.
  
 *)
End BasicVectorTheory.


(* ######################################################################### *)
(** * Collection of all implementations for ring vector theory *)
Module RingVectorTheory (E : RingElementType).

  (** export base element, contain: types, definitions, notations, etc.  *)
  Export E.
  
  (* ======================================================================= *)
  (** ** Short name for concrete implementations *)
  Module DP
  (* <: RingVectorTheory E *)
    := RingVectorTheoryDP E.
  Module DL
  (* <: RingVectorTheory E *)
    := RingVectorTheoryDL E.
  Module DR
  (* <: RingVectorTheory E *)
    := RingVectorTheoryDR E.
  Module NF
  (* <: RingVectorTheory E *)
    := RingVectorTheoryNF E.
  (* Module FF <: RingVectorTheory E := RingVectorTheoryFF E. *)

  (** Basic vector theory, contain conversion and properties *)
  Module Export All := BasicVectorTheory E.

End RingVectorTheory.


(* ######################################################################### *)
(** * Collection of all different implementations (Concrete Module) *)
  
(** Note: different data type derived different vector theory.
    Nat   : basic vector theory
    Z     : ring vector theory
    Q     : field vector theroy
    Qc    : field vector theroy
    R     : field vector theory
*)

(** Vector based on nat *)
Module VectorAllNat := BasicVectorTheory ElementTypeNat.
Module VectorNat_DR := VectorAllNat.DR.
Module VectorNat_DP := VectorAllNat.DP.
Module VectorNat_DL := VectorAllNat.DL.
Module VectorNat_NF := VectorAllNat.NF.
(* Compute @l2v 3 [1;2;3]. *)

(** Vector based on Z *)
Module VectorAllZ := RingVectorTheory RingElementTypeZ.
Module VectorZ_DR := VectorAllZ.DR.
Module VectorZ_DP := VectorAllZ.DP.
Module VectorZ_DL := VectorAllZ.DL.
Module VectorZ_NF := VectorAllZ.NF.
(* Compute @l2v 3 [1;2;3]. *)

(** Vector based on Q *)
Module VectorAllQ := RingVectorTheory RingElementTypeQ.
Module VectorQ_DR := VectorAllQ.DR.
Module VectorQ_DP := VectorAllQ.DP.
Module VectorQ_DL := VectorAllQ.DL.
Module VectorQ_NF := VectorAllQ.NF.

(** Vector based on Qc *)
Module VectorAllQc := RingVectorTheory RingElementTypeQc.
Module VectorQc_DR := VectorAllQc.DR.
Module VectorQc_DP := VectorAllQc.DP.
Module VectorQc_DL := VectorAllQc.DL.
Module VectorQc_NF := VectorAllQc.NF.

(** Vector based on R *)
Module VectorAllR := RingVectorTheory RingElementTypeR.
Module VectorR_DR := VectorAllR.DR.
Module VectorR_DP := VectorAllR.DP.
Module VectorR_DL := VectorAllR.DL.
Module VectorR_NF := VectorAllR.NF.


(* ######################################################################### *)
(** * Usage demo *)

(** test VLL *)
Module Demo_usage_DR.
  
  Import VectorR_DR.
  Import RExt List ListNotations.
  Open Scope R.
  Open Scope mat_scope.

  Notation "0" := R0.
  Notation "1" := R1.
  
  Example v1 := @l2v 5 (map nat2R (seq 0 5)).
  (* Compute v2l v1. *)
  (* Compute vdot v1 v1. *)
End Demo_usage_DR.

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
  Example v2 : vec 50 := fun i j => (nat2Q i) * 0.1.
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

