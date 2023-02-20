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
  SafeNatFun.VectorTheorySF
(* FinFun.VectorTheoryFF *)
.


(* ######################################################################### *)
(** * Collection of all implementations for basic vector theory *)
Module BasicVectorTheory (E : ElementType).

  (** export base element, contain: types, definitions, notations, etc.  *)
  Export E.
  
  (* ======================================================================= *)
  (** ** Short name for concrete implementations *)
  Module DL <: BasicVectorTheory E := BasicVectorTheoryDL E.
  Module DP <: BasicVectorTheory E := BasicVectorTheoryDP E.
  Module DR <: BasicVectorTheory E := BasicVectorTheoryDR E.
  Module NF <: BasicVectorTheory E := BasicVectorTheoryNF E.
  Module SF <: BasicVectorTheory E := BasicVectorTheorySF E.
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
  Module DL
  (* <: RingVectorTheory E *)
    := RingVectorTheoryDL E.
  Module DP
  (* <: RingVectorTheory E *)
    := RingVectorTheoryDP E.
  Module DR
  (* <: RingVectorTheory E *)
    := RingVectorTheoryDR E.
  Module NF
  (* <: RingVectorTheory E *)
    := RingVectorTheoryNF E.
  Module SF
  (* <: RingVectorTheory E *)
    := RingVectorTheorySF E.
  (* Module FF <: RingVectorTheory E := RingVectorTheoryFF E. *)

  (** Basic vector theory, contain conversion and properties *)
  Module Export Basic := BasicVectorTheory E.

End RingVectorTheory.


(* ######################################################################### *)
(** * Collection of all implementations for decidable-field vector theory *)
Module DecidableFieldVectorTheory (E : DecidableFieldElementType).

  (** export base element, contain: types, definitions, notations, etc.  *)
  Export E.
  
  (* ======================================================================= *)
  (** ** Short name for concrete implementations *)
  Module DL := DecidableFieldVectorTheoryDL E.
  Module DP := DecidableFieldVectorTheoryDP E.
  Module DR := DecidableFieldVectorTheoryDR E.
  Module NF := DecidableFieldVectorTheoryNF E.
  Module SF := DecidableFieldVectorTheorySF E.
  (* Module FF := DecidableFieldVectorTheoryFF E. *)

  (** Basic vector theory, contain conversion and properties *)
  Module Export Basic := BasicVectorTheory E.

End DecidableFieldVectorTheory.
