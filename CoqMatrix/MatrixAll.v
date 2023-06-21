(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Entrance for access all matrix.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export ElementType MatrixTheory.

(** These exported models will be available in final matrix theory files. *)
Require Export BasicConfig FuncExt HierarchySetoid.

Require Import
  DepPair.MatrixTheoryDP
  DepList.MatrixTheoryDL
  DepRec.MatrixTheoryDR
  NatFun.MatrixTheoryNF
  SafeNatFun.MatrixTheorySF
  (* FinFun.MatrixTheoryFF *)
  .

(* ######################################################################### *)
(** * Collection of all implementations for basic matrix theory *)
Module BasicMatrixTheory (E : ElementType).

  (** export base element, contain: types, definitions, notations, etc.  *)
  Export E.
  
  (* ======================================================================= *)
  (** ** Short name for concrete implementations *)
  Module DL <: BasicMatrixTheory E := BasicMatrixTheoryDL E.
  Module DP <: BasicMatrixTheory E := BasicMatrixTheoryDP E.
  Module DR <: BasicMatrixTheory E := BasicMatrixTheoryDR E.
  Module NF <: BasicMatrixTheory E := BasicMatrixTheoryNF E.
  Module SF <: BasicMatrixTheory E := BasicMatrixTheorySF E.
  (* Module FF <: BasicMatrixTheory E := BasicMatrixTheoryFF E. *)


  (* ======================================================================= *)
  (** ** Conversion between different implementations *)
  
  (** *** DL -- DP *)
  Definition dl2dp {r c} (m : DL.mat r c) : DP.mat r c := DP.l2m (DL.m2l m).
  Definition dp2dl {r c} (m : DP.mat r c) : DL.mat r c := DL.l2m (DP.m2l m).
  
  Lemma dp2dl_bij {r c} : Bijective (Aeq:=DP.meq)(Beq:=DL.meq) (@dp2dl r c).
  Proof.
    unfold dp2dl. constructor;constructor;intros.
    - apply DL.l2m_inj; auto with mat. apply DP.m2l_inj; auto.
    - exists (DP.l2m (DL.m2l b)).
      rewrite DP.m2l_l2m_id; auto with mat. apply DL.l2m_m2l_id.
  Qed.
  
  Corollary dp2dl_surj {r c} : Surjective (Beq:=DL.meq) (@dp2dl r c).
  Proof.
    destruct (@dp2dl_bij r c); auto.
  Qed.
  
  Lemma dl2dp_bij {r c} : Bijective (Aeq:=DL.meq)(Beq:=DP.meq) (@dl2dp r c).
  Proof.
    unfold dl2dp. constructor;constructor;intros.
    - apply DP.l2m_inj; auto with mat. apply DL.m2l_inj; auto.
    - exists (DL.l2m (DP.m2l b)).
      rewrite DL.m2l_l2m_id; auto with mat. apply DP.l2m_m2l_id.
  Qed.
  
  Corollary dl2dp_surj {r c} : Surjective (Beq:=DP.meq) (@dl2dp r c).
  Proof.
    destruct (@dl2dp_bij r c); auto.
  Qed.
  
  Lemma dp2dl_dl2dp_id : forall r c (m : DL.mat r c), DL.meq (dp2dl (dl2dp m)) m.
  Proof.
    intros. unfold dp2dl,dl2dp. rewrite DP.m2l_l2m_id; auto with mat.
    apply DL.l2m_m2l_id; auto with mat.
  Qed.
  
  Lemma dl2dp_dp2dl_id : forall r c (m : DP.mat r c), DP.meq (dl2dp (dp2dl m)) m.
  Proof.
    intros. unfold dp2dl,dl2dp. rewrite DL.m2l_l2m_id; auto with mat.
    apply DP.l2m_m2l_id; auto with mat.
  Qed.


  (** *** DL -- DR *)
  Definition dr2dl {r c} (m : DR.mat r c) : DL.mat r c := DL.l2m (DR.m2l m).
  Definition dl2dr {r c} (m : DL.mat r c) : DR.mat r c := DR.l2m (DL.m2l m).

  Lemma dr2dl_bij {r c} : Bijective (Aeq:=DR.meq)(Beq:=DL.meq) (@dr2dl r c).
  Proof.
    unfold dr2dl. constructor;constructor;intros.
    - apply DL.l2m_inj; auto with mat.
    - exists (DR.l2m (DL.m2l b)).
      rewrite DR.m2l_l2m_id; auto with mat. apply DL.l2m_m2l_id.
  Qed.
  
  Corollary dr2dl_surj {r c} : Surjective (Beq:=DL.meq) (@dr2dl r c).
  Proof.
    destruct (@dr2dl_bij r c); auto.
  Qed.
  
  Lemma dl2dr_bij {r c} : Bijective (Aeq:=DL.meq)(Beq:=DR.meq) (@dl2dr r c).
  Proof.
    unfold dl2dr. constructor;constructor;intros.
    - apply DR.l2m_inj; auto with mat. apply DL.m2l_inj; auto.
    - exists (DL.l2m (DR.m2l b)).
      rewrite DL.m2l_l2m_id; auto with mat. apply DR.l2m_m2l_id.
  Qed.
  
  Corollary dl2dr_surj {r c} : Surjective (Beq:=DR.meq) (@dl2dr r c).
  Proof.
    destruct (@dl2dr_bij r c); auto.
  Qed.
  
  Lemma dr2dl_dl2dr_id : forall r c (m : DL.mat r c), DL.meq (dr2dl (dl2dr m)) m.
  Proof.
    intros. unfold dr2dl,dl2dr. rewrite DR.m2l_l2m_id.
    apply DL.l2m_m2l_id. apply DL.m2l_length. apply DL.m2l_width.
  Qed.
  
  Lemma dl2dr_dr2dl_id : forall r c (m : DR.mat r c), DR.meq (dl2dr (dr2dl m)) m.
  Proof.
    intros. unfold dr2dl,dl2dr. rewrite DL.m2l_l2m_id.
    apply DR.l2m_m2l_id. apply DR.m2l_length. apply DR.m2l_width.
  Qed.


  (** *** DL -- NF *)
  Definition nf2dl {r c} (m : NF.mat r c) : DL.mat r c := DL.l2m (NF.m2l m).
  Definition dl2nf {r c} (m : DL.mat r c) : NF.mat r c := NF.l2m (DL.m2l m).
  
  Lemma nf2dl_bij {r c} : Bijective (Aeq:=NF.meq)(Beq:=DL.meq) (@nf2dl r c).
  Proof.
    unfold nf2dl. constructor;constructor;intros.
    - apply DL.l2m_inj; auto with mat. apply NF.m2l_inj; auto.
    - exists (NF.l2m (DL.m2l b)).
      rewrite NF.m2l_l2m_id; auto with mat. apply DL.l2m_m2l_id.
  Qed.
  
  Corollary nf2dl_surj {r c} : Surjective (Beq:=DL.meq) (@nf2dl r c).
  Proof.
    destruct (@nf2dl_bij r c); auto.
  Qed.
  
  Lemma dl2nf_bij {r c} : Bijective (Aeq:=DL.meq)(Beq:=NF.meq) (@dl2nf r c).
  Proof.
    unfold dl2nf. constructor;constructor;intros.
    - apply NF.l2m_inj; auto with mat. apply DL.m2l_inj; auto.
    - exists (DL.l2m (NF.m2l b)).
      rewrite DL.m2l_l2m_id; auto with mat. apply NF.l2m_m2l_id.
  Qed.
  
  Corollary dl2nf_surj {r c} : Surjective (Beq:=NF.meq) (@dl2nf r c).
  Proof.
    destruct (@dl2nf_bij r c); auto.
  Qed.
  
  Lemma nf2dl_dl2nf_id : forall r c (m : DL.mat r c), DL.meq (nf2dl (dl2nf m)) m.
  Proof.
    intros. unfold nf2dl,dl2nf. rewrite NF.m2l_l2m_id; auto with mat.
    apply DL.l2m_m2l_id.
  Qed.
  
  Lemma dl2nf_nf2dl_id : forall r c (m : NF.mat r c), NF.meq (dl2nf (nf2dl m)) m.
  Proof.
    intros. unfold nf2dl,dl2nf. rewrite DL.m2l_l2m_id; auto with mat.
    apply NF.l2m_m2l_id; auto.
  Qed.


  (** *** DL -- SF *)
  Definition sf2dl {r c} (m : SF.mat r c) : DL.mat r c := DL.l2m (SF.m2l m).
  Definition dl2sf {r c} (m : DL.mat r c) : SF.mat r c := SF.l2m (DL.m2l m).
  
  Lemma sf2dl_bij {r c} : Bijective (Aeq:=SF.meq)(Beq:=DL.meq) (@sf2dl r c).
  Proof.
    unfold sf2dl. constructor;constructor;intros.
    - apply DL.l2m_inj; auto with mat. apply SF.m2l_inj; auto.
    - exists (SF.l2m (DL.m2l b)).
      rewrite SF.m2l_l2m_id; auto with mat. apply DL.l2m_m2l_id.
  Qed.
  
  Corollary sf2dl_surj {r c} : Surjective (Beq:=DL.meq) (@sf2dl r c).
  Proof.
    destruct (@sf2dl_bij r c); auto.
  Qed.
  
  Lemma dl2sf_bij {r c} : Bijective (Aeq:=DL.meq)(Beq:=SF.meq) (@dl2sf r c).
  Proof.
    unfold dl2sf. constructor;constructor;intros.
    - apply SF.l2m_inj; auto with mat. apply DL.m2l_inj; auto.
    - exists (DL.l2m (SF.m2l b)).
      rewrite DL.m2l_l2m_id; auto with mat. apply SF.l2m_m2l_id.
  Qed.
  
  Corollary dl2sf_surj {r c} : Surjective (Beq:=SF.meq) (@dl2sf r c).
  Proof.
    destruct (@dl2sf_bij r c); auto.
  Qed.
  
  Lemma sf2dl_dl2sf_id : forall r c (m : DL.mat r c), DL.meq (sf2dl (dl2sf m)) m.
  Proof.
    intros. unfold sf2dl,dl2sf. rewrite SF.m2l_l2m_id; auto with mat.
    apply DL.l2m_m2l_id.
  Qed.
  
  Lemma dl2sf_sf2dl_id : forall r c (m : SF.mat r c), SF.meq (dl2sf (sf2dl m)) m.
  Proof.
    intros. unfold sf2dl,dl2sf. rewrite DL.m2l_l2m_id; auto with mat.
    apply SF.l2m_m2l_id; auto.
  Qed.


  (** *** DP -- DR *)
  Definition dr2dp {r c} (m : DR.mat r c) : DP.mat r c := DP.l2m (DR.m2l m).
  Definition dp2dr {r c} (m : DP.mat r c) : DR.mat r c := DR.l2m (DP.m2l m).
  
  (** dr2dp is a proper morphism *)
  Lemma dr2dp_aeq_mor : forall r c, Proper (@DR.meq r c ==> @DP.meq r c) dr2dp.
  Proof.
    unfold Proper, respectful. intros. unfold dr2dp. rewrite H. easy.
  Qed.
  Global Existing Instance dr2dp_aeq_mor.
  
  (** dp2dr is a proper morphism *)
  Lemma dp2dr_aeq_mor : forall r c, Proper (@DP.meq r c ==> @DR.meq r c) dp2dr.
  Proof.
    unfold Proper, respectful. intros. unfold dp2dr. rewrite H. easy.
  Qed.
  Global Existing Instance dp2dr_aeq_mor.

  Lemma dr2dp_bij {r c} : Bijective (Aeq:=DR.meq)(Beq:=DP.meq) (@dr2dp r c).
  Proof.
    unfold dr2dp. constructor;constructor;intros.
    - apply DP.l2m_inj; auto with mat.
    - exists (DR.l2m (DP.m2l b)).
      rewrite DR.m2l_l2m_id; auto with mat. apply DP.l2m_m2l_id.
  Qed.
  
  Corollary dr2dp_surj {r c} : Surjective (Beq:=DP.meq) (@dr2dp r c).
  Proof.
    destruct (@dr2dp_bij r c); auto.
  Qed.
  
  Lemma dp2dr_bij {r c} : Bijective (Aeq:=DP.meq)(Beq:=DR.meq) (@dp2dr r c).
  Proof.
    unfold dp2dr. constructor;constructor;intros.
    - apply DR.l2m_inj; auto with mat. apply DP.m2l_inj; auto.
    - exists (DP.l2m (DR.m2l b)).
      rewrite DP.m2l_l2m_id; auto with mat. apply DR.l2m_m2l_id.
  Qed.
  
  Corollary dp2dr_surj {r c} : Surjective (Beq:=DR.meq) (@dp2dr r c).
  Proof.
    destruct (@dp2dr_bij r c); auto.
  Qed.
  
  Lemma dr2dp_dp2dr_id : forall r c (m : DP.mat r c), DP.meq (dr2dp (dp2dr m)) m.
  Proof.
    intros. unfold dr2dp,dp2dr. rewrite DR.m2l_l2m_id; auto with mat.
    apply DP.l2m_m2l_id.
  Qed.
  
  Lemma dp2dr_dr2dp_id : forall r c (m : DR.mat r c), DR.meq (dp2dr (dr2dp m)) m.
  Proof.
    intros. unfold dr2dp,dp2dr. rewrite DP.m2l_l2m_id; auto with mat.
    apply DR.l2m_m2l_id.
  Qed.

  
  (** *** DP -- NF *)
  Definition nf2dp {r c} (m : NF.mat r c) : DP.mat r c := DP.l2m (NF.m2l m).
  Definition dp2nf {r c} (m : DP.mat r c) : NF.mat r c := NF.l2m (DP.m2l m).

  Lemma nf2dp_bij {r c} : Bijective (Aeq:=NF.meq)(Beq:=DP.meq) (@nf2dp r c).
  Proof.
    unfold nf2dp. constructor;constructor;intros.
    - apply DP.l2m_inj; auto with mat. apply NF.m2l_inj; auto.
    - exists (NF.l2m (DP.m2l b)).
      rewrite NF.m2l_l2m_id; auto with mat. apply DP.l2m_m2l_id.
  Qed.
  
  Corollary nf2dp_surj {r c} : Surjective (Beq:=DP.meq) (@nf2dp r c).
  Proof.
    destruct (@nf2dp_bij r c); auto.
  Qed.
  
  Lemma dp2nf_bij {r c} : Bijective (Aeq:=DP.meq) (Beq:=NF.meq) (@dp2nf r c).
  Proof.
    unfold dp2nf. constructor;constructor;intros.
    - apply NF.l2m_inj; auto with mat. apply DP.m2l_inj; auto.
    - exists (DP.l2m (NF.m2l b)).
      rewrite DP.m2l_l2m_id; auto with mat. apply NF.l2m_m2l_id.
  Qed.
  
  Corollary dp2nf_surj {r c} : Surjective (Beq:=NF.meq) (@dp2nf r c).
  Proof.
    destruct (@dp2nf_bij r c); auto.
  Qed.
  
  Lemma nf2dp_dp2nf_id : forall r c (m : DP.mat r c), DP.meq (nf2dp (dp2nf m)) m.
  Proof.
    intros. unfold nf2dp,dp2nf. rewrite NF.m2l_l2m_id.
    apply DP.l2m_m2l_id. apply DP.m2l_length. apply DP.m2l_width.
  Qed.
  
  Lemma dp2nf_nf2dp_id : forall r c (m : NF.mat r c), NF.meq (dp2nf (nf2dp m)) m.
  Proof.
    intros. unfold dp2nf,nf2dp. rewrite DP.m2l_l2m_id.
    apply NF.l2m_m2l_id; auto. apply NF.m2l_length. apply NF.m2l_width.
  Qed.

  
  (** *** DP -- SF *)
  Definition sf2dp {r c} (m : SF.mat r c) : DP.mat r c := DP.l2m (SF.m2l m).
  Definition dp2sf {r c} (m : DP.mat r c) : SF.mat r c := SF.l2m (DP.m2l m).

  Lemma sf2dp_bij {r c} : Bijective (Aeq:=SF.meq)(Beq:=DP.meq) (@sf2dp r c).
  Proof.
    unfold sf2dp. constructor;constructor;intros.
    - apply DP.l2m_inj; auto with mat. apply SF.m2l_inj; auto.
    - exists (SF.l2m (DP.m2l b)).
      rewrite SF.m2l_l2m_id; auto with mat. apply DP.l2m_m2l_id.
  Qed.
  
  Corollary sf2dp_surj {r c} : Surjective (Beq:=DP.meq) (@sf2dp r c).
  Proof.
    destruct (@sf2dp_bij r c); auto.
  Qed.
  
  Lemma dp2sf_bij {r c} : Bijective (Aeq:=DP.meq) (Beq:=SF.meq) (@dp2sf r c).
  Proof.
    unfold dp2sf. constructor;constructor;intros.
    - apply SF.l2m_inj; auto with mat. apply DP.m2l_inj; auto.
    - exists (DP.l2m (SF.m2l b)).
      rewrite DP.m2l_l2m_id; auto with mat. apply SF.l2m_m2l_id.
  Qed.
  
  Corollary dp2sf_surj {r c} : Surjective (Beq:=SF.meq) (@dp2sf r c).
  Proof.
    destruct (@dp2sf_bij r c); auto.
  Qed.
  
  Lemma sf2dp_dp2sf_id : forall r c (m : DP.mat r c), DP.meq (sf2dp (dp2sf m)) m.
  Proof.
    intros. unfold sf2dp,dp2sf. rewrite SF.m2l_l2m_id.
    apply DP.l2m_m2l_id. apply DP.m2l_length. apply DP.m2l_width.
  Qed.
  
  Lemma dp2sf_sf2dp_id : forall r c (m : SF.mat r c), SF.meq (dp2sf (sf2dp m)) m.
  Proof.
    intros. unfold dp2sf,sf2dp. rewrite DP.m2l_l2m_id.
    apply SF.l2m_m2l_id; auto. apply SF.m2l_length. apply SF.m2l_width.
  Qed.
  

  (** *** DR -- NF *)
  Definition dr2nf {r c} (m : DR.mat r c) : NF.mat r c := NF.l2m (DR.m2l m).
  Definition nf2dr {r c} (m : NF.mat r c) : DR.mat r c := DR.l2m (NF.m2l m).
  
  Lemma dr2nf_bij {r c} : Bijective (Aeq:=DR.meq)(Beq:=NF.meq) (@dr2nf r c).
  Proof.
    unfold dr2nf. constructor;constructor; intros.
    - apply NF.l2m_inj; auto with mat.
    - exists (DR.l2m (NF.m2l b)).
      rewrite DR.m2l_l2m_id; auto with mat. apply NF.l2m_m2l_id.
  Qed.
  
  Corollary dr2nf_surj {r c} : Surjective (Beq:=NF.meq) (@dr2nf r c).
  Proof.
    destruct (@dr2nf_bij r c); auto.
  Qed.
  
  Lemma nf2dr_bij {r c} : Bijective (Aeq:=NF.meq)(Beq:=DR.meq) (@nf2dr r c).
  Proof.
    unfold nf2dr. constructor;constructor; intros.
    - apply DR.l2m_inj; auto with mat. apply NF.m2l_inj; auto.
    - exists (NF.l2m (DR.m2l b)).
      rewrite NF.m2l_l2m_id; auto with mat. apply DR.l2m_m2l_id.
  Qed.
  
  Corollary nf2dr_surj {r c} : Surjective (Beq:=DR.meq) (@nf2dr r c).
  Proof.
    destruct (@nf2dr_bij r c); auto.
  Qed.

  Lemma dr2nf_nf2dr_id : forall r c (m : NF.mat r c), NF.meq (dr2nf (nf2dr m)) m.
  Proof.
    intros. unfold dr2nf,nf2dr. rewrite DR.m2l_l2m_id; auto with mat.
    apply NF.l2m_m2l_id.
  Qed.
  
  Lemma nf2dr_dr2nf_id : forall r c (m : DR.mat r c), DR.meq (nf2dr (dr2nf m)) m.
  Proof.
    intros. unfold dr2nf,nf2dr. rewrite NF.m2l_l2m_id.
    apply DR.l2m_m2l_id; auto with mat. (* ToDo: why not completely finish it? *)
    apply DR.m2l_length. apply DR.m2l_width.
  Qed.


  (** *** DR -- SF *)
  Definition dr2sf {r c} (m : DR.mat r c) : SF.mat r c := SF.l2m (DR.m2l m).
  Definition sf2dr {r c} (m : SF.mat r c) : DR.mat r c := DR.l2m (SF.m2l m).
  
  Lemma dr2sf_bij {r c} : Bijective (Aeq:=DR.meq)(Beq:=SF.meq) (@dr2sf r c).
  Proof.
    unfold dr2sf. constructor;constructor; intros.
    - apply SF.l2m_inj; auto with mat.
    - exists (DR.l2m (SF.m2l b)).
      rewrite DR.m2l_l2m_id; auto with mat. apply SF.l2m_m2l_id.
  Qed.
  
  Corollary dr2sf_surj {r c} : Surjective (Beq:=SF.meq) (@dr2sf r c).
  Proof.
    destruct (@dr2sf_bij r c); auto.
  Qed.
  
  Lemma sf2dr_bij {r c} : Bijective (Aeq:=SF.meq)(Beq:=DR.meq) (@sf2dr r c).
  Proof.
    unfold sf2dr. constructor;constructor; intros.
    - apply DR.l2m_inj; auto with mat. apply SF.m2l_inj; auto.
    - exists (SF.l2m (DR.m2l b)).
      rewrite SF.m2l_l2m_id; auto with mat. apply DR.l2m_m2l_id.
  Qed.
  
  Corollary sf2dr_surj {r c} : Surjective (Beq:=DR.meq) (@sf2dr r c).
  Proof.
    destruct (@sf2dr_bij r c); auto.
  Qed.

  Lemma dr2sf_sf2dr_id : forall r c (m : SF.mat r c), SF.meq (dr2sf (sf2dr m)) m.
  Proof.
    intros. unfold dr2sf,sf2dr. rewrite DR.m2l_l2m_id; auto with mat.
    apply SF.l2m_m2l_id.
  Qed.
  
  Lemma sf2dr_dr2sf_id : forall r c (m : DR.mat r c), DR.meq (sf2dr (dr2sf m)) m.
  Proof.
    intros. unfold dr2sf,sf2dr. rewrite SF.m2l_l2m_id.
    apply DR.l2m_m2l_id; auto with mat. (* ToDo: why not completely finish it? *)
    apply DR.m2l_length. apply DR.m2l_width.
  Qed.


  (** *** NF -- SF *)
  Definition nf2sf {r c} (m : NF.mat r c) : SF.mat r c := SF.l2m (NF.m2l m).
  Definition sf2nf {r c} (m : SF.mat r c) : NF.mat r c := NF.l2m (SF.m2l m).
  
  Lemma nf2sf_bij {r c} : Bijective (Aeq:=NF.meq)(Beq:=SF.meq) (@nf2sf r c).
  Proof.
    unfold nf2sf. constructor;constructor; intros.
    - apply SF.l2m_inj; auto with mat. apply NF.m2l_inj; auto.
    - exists (NF.l2m (SF.m2l b)).
      rewrite NF.m2l_l2m_id; auto with mat. apply SF.l2m_m2l_id.
  Qed.
  
  Corollary nf2sf_surj {r c} : Surjective (Beq:=SF.meq) (@nf2sf r c).
  Proof.
    destruct (@nf2sf_bij r c); auto.
  Qed.
  
  Lemma sf2nf_bij {r c} : Bijective (Aeq:=SF.meq)(Beq:=NF.meq) (@sf2nf r c).
  Proof.
    unfold sf2nf. constructor;constructor; intros.
    - apply NF.l2m_inj; auto with mat. apply SF.m2l_inj; auto.
    - exists (SF.l2m (NF.m2l b)).
      rewrite SF.m2l_l2m_id; auto with mat. apply NF.l2m_m2l_id.
  Qed.
  
  Corollary sf2nf_surj {r c} : Surjective (Beq:=NF.meq) (@sf2nf r c).
  Proof.
    destruct (@sf2nf_bij r c); auto.
  Qed.

  Lemma nf2sf_sf2nf_id : forall r c (m : SF.mat r c), SF.meq (nf2sf (sf2nf m)) m.
  Proof.
    intros. unfold nf2sf,sf2nf. rewrite NF.m2l_l2m_id; auto with mat.
    apply SF.l2m_m2l_id.
  Qed.
  
  Lemma sf2nf_nf2sf_id : forall r c (m : NF.mat r c), NF.meq (sf2nf (nf2sf m)) m.
  Proof.
    intros. unfold nf2sf,sf2nf. rewrite SF.m2l_l2m_id.
    apply NF.l2m_m2l_id; auto with mat. (* ToDo: why not completely finish it? *)
    apply NF.m2l_length. apply NF.m2l_width.
  Qed.
  

  (* (** *** DR -- FF *) *)
  (* Definition dr2ff {r c} (m : DR.mat r c) : FF.mat r c := FF.l2m (DR.m2l m). *)
  (* Definition ff2dr {r c} (m : FF.mat r c) : DR.mat r c := DR.l2m (FF.m2l m). *)
  
  (* Lemma dr2ff_bij {r c} : bijective (@dr2ff r c). *)
  (* Proof. *)
  (*   unfold dr2ff. unfold bijective,injective,surjective. split; intros. *)
  (*   - apply FF.l2m_inj; auto with mat. apply DR.m2l_inj; auto. *)
  (*   - exists (DR.l2m (FF.m2l b)). *)
  (*     rewrite DR.m2l_l2m_id; auto with mat. apply FF.l2m_m2l_id. *)
  (* Qed. *)
  
  (* Corollary dr2ff_surj {r c} : surjective (@dr2ff r c). *)
  (* Proof. *)
  (*   destruct (@dr2ff_bij r c); auto. *)
  (* Qed. *)
  
  (* Lemma ff2dr_bij {r c} : bijective (@ff2dr r c). *)
  (* Proof. *)
  (*   unfold ff2dr. unfold bijective,injective,surjective. split; intros. *)
  (*   - apply DR.l2m_inj; auto with mat. apply FF.m2l_inj; auto. *)
  (*   - exists (FF.l2m (DR.m2l b)). *)
  (*     rewrite FF.m2l_l2m_id; auto with mat. apply DR.l2m_m2l_id. *)
  (* Qed. *)
  
  (* Corollary ff2dr_surj {r c} : surjective (@ff2dr r c). *)
  (* Proof. *)
  (*   destruct (@ff2dr_bij r c); auto. *)
  (* Qed. *)
  
  (* Lemma dr2ff_ff2dr_id : forall r c (m : FF.mat r c), dr2ff (ff2dr m) = m. *)
  (* Proof. *)
  (*   intros. unfold dr2ff,ff2dr. rewrite DR.m2l_l2m_id. *)
  (*   apply FF.l2m_m2l_id; auto. apply FF.m2l_length. apply FF.m2l_width. *)
  (* Qed. *)
  
  (* Lemma ff2dr_dr2ff_id : forall r c (m : DR.mat r c), ff2dr (dr2ff m) = m. *)
  (* Proof. *)
  (*   intros. unfold dr2ff,ff2dr. rewrite FF.m2l_l2m_id. *)
  (*   apply DR.l2m_m2l_id. apply DR.m2l_length. apply DR.m2l_width. *)
  (* Qed. *)
  
  (* (** *** NF -- FF *) *)
  (* Definition nf2ff {r c} (m : NF.mat r c) : FF.mat r c := FF.l2m (NF.m2l m). *)
  (* Definition ff2nf {r c} (m : FF.mat r c) : NF.mat r c := NF.l2m (FF.m2l m). *)

  (* Lemma nf2ff_bij {r c} : bijective (@nf2ff r c). *)
  (* Proof. *)
  (*   unfold nf2ff. unfold bijective,injective,surjective. split; intros. *)
  (*   - apply FF.l2m_inj; auto with mat. apply NF.m2l_inj; auto. *)
  (*   - exists (NF.l2m (FF.m2l b)). *)
  (*     rewrite NF.m2l_l2m_id; auto with mat. apply FF.l2m_m2l_id. *)
  (* Qed. *)
  
  (* Corollary nf2ff_surj {r c} : surjective (@nf2ff r c). *)
  (* Proof. *)
  (*   destruct (@nf2ff_bij r c); auto. *)
  (* Qed. *)
  
  (* Lemma ff2nf_bij {r c} : bijective (@ff2nf r c). *)
  (* Proof. *)
  (*   unfold ff2nf. unfold bijective,injective,surjective. split; intros. *)
  (*   - apply NF.l2m_inj; auto with mat. apply FF.m2l_inj; auto. *)
  (*   - exists (FF.l2m (NF.m2l b)). *)
  (*     rewrite FF.m2l_l2m_id; auto with mat. apply NF.l2m_m2l_id. *)
  (* Qed. *)
  
  (* Corollary ff2nf_surj {r c} : surjective (@ff2nf r c). *)
  (* Proof. *)
  (*   destruct (@ff2nf_bij r c); auto. *)
  (* Qed. *)
  
  (* Lemma nf2ff_dp2nf_id : forall r c (m : FF.mat r c), nf2ff (ff2nf m) = m. *)
  (* Proof. *)
  (*   intros. unfold nf2ff,ff2nf. rewrite NF.m2l_l2m_id. *)
  (*   apply FF.l2m_m2l_id. apply FF.m2l_length. apply FF.m2l_width. *)
  (* Qed. *)
  
  (* Lemma ff2nf_nf2ff_id : forall r c (m : NF.mat r c), ff2nf (nf2ff m) = m. *)
  (* Proof. *)
  (*   intros. unfold ff2nf,nf2ff. rewrite FF.m2l_l2m_id. *)
  (*   apply NF.l2m_m2l_id; auto. apply NF.m2l_length. apply NF.m2l_width. *)
  (* Qed. *)
  
  (* (** *** FF -- DP *) *)
  (* Definition ff2dp {r c} (m : FF.mat r c) : DP.mat r c := DP.l2m (FF.m2l m). *)
  (* Definition dp2ff {r c} (m : DP.mat r c) : FF.mat r c := FF.l2m (DP.m2l m). *)

  (* Lemma ff2dp_bij {r c} : bijective (@ff2dp r c). *)
  (* Proof. *)
  (*   unfold ff2dp. unfold bijective,injective,surjective. split; intros. *)
  (*   - apply DP.l2m_inj; auto with mat. apply FF.m2l_inj; auto. *)
  (*   - exists (FF.l2m (DP.m2l b)). *)
  (*     rewrite FF.m2l_l2m_id; auto with mat. apply DP.l2m_m2l_id. *)
  (* Qed. *)
  
  (* Corollary ff2dp_surj {r c} : surjective (@ff2dp r c). *)
  (* Proof. *)
  (*   destruct (@ff2dp_bij r c); auto. *)
  (* Qed. *)
  
  (* Lemma dp2ff_bij {r c} : bijective (@dp2ff r c). *)
  (* Proof. *)
  (*   unfold dp2ff. unfold bijective,injective,surjective. split; intros. *)
  (*   - apply FF.l2m_inj; auto with mat. apply DP.m2l_inj; auto. *)
  (*   - exists (DP.l2m (FF.m2l b)). *)
  (*     rewrite DP.m2l_l2m_id; auto with mat. apply FF.l2m_m2l_id. *)
  (* Qed. *)
  
  (* Corollary dp2ff_surj {r c} : surjective (@dp2ff r c). *)
  (* Proof. *)
  (*   destruct (@dp2ff_bij r c); auto. *)
  (* Qed. *)
  
  (* Lemma ff2dp_dp2ff_id : forall r c (m : DP.mat r c), ff2dp (dp2ff m) = m. *)
  (* Proof. *)
  (*   intros. unfold ff2dp,dp2ff. rewrite FF.m2l_l2m_id. *)
  (*   apply DP.l2m_m2l_id. apply DP.m2l_length. apply DP.m2l_width. *)
  (* Qed. *)
  
  (* Lemma dp2ff_ff2dp_id : forall r c (m : FF.mat r c), dp2ff (ff2dp m) = m. *)
  (* Proof. *)
  (*   intros. unfold dp2ff,ff2dp. rewrite DP.m2l_l2m_id. *)
  (*   apply FF.l2m_m2l_id; auto. apply FF.m2l_length. apply FF.m2l_width. *)
  (* Qed. *)
  
  (* (** *** FF -- DL *) *)
  (* Definition ff2dl {r c} (m : FF.mat r c) : DL.mat r c := DL.l2m (FF.m2l m). *)
  (* Definition dl2ff {r c} (m : DL.mat r c) : FF.mat r c := FF.l2m (DL.m2l m). *)

  (* Lemma ff2dl_bij {r c} : bijective (@ff2dl r c). *)
  (* Proof. *)
  (*   unfold ff2dl. unfold bijective,injective,surjective. split; intros. *)
  (*   - apply DL.l2m_inj; auto with mat. apply FF.m2l_inj; auto. *)
  (*   - exists (FF.l2m (DL.m2l b)). *)
  (*     rewrite FF.m2l_l2m_id; auto with mat. apply DL.l2m_m2l_id. *)
  (* Qed. *)
  
  (* Corollary ff2dl_surj {r c} : surjective (@ff2dl r c). *)
  (* Proof. *)
  (*   destruct (@ff2dl_bij r c); auto. *)
  (* Qed. *)
  
  (* Lemma dl2ff_bij {r c} : bijective (@dl2ff r c). *)
  (* Proof. *)
  (*   unfold dl2ff. unfold bijective,injective,surjective. split; intros. *)
  (*   - apply FF.l2m_inj; auto with mat. apply DL.m2l_inj; auto. *)
  (*   - exists (DL.l2m (FF.m2l b)). *)
  (*     rewrite DL.m2l_l2m_id; auto with mat. apply FF.l2m_m2l_id. *)
  (* Qed. *)
  
  (* Corollary dl2ff_surj {r c} : surjective (@dl2ff r c). *)
  (* Proof. *)
  (*   destruct (@dl2ff_bij r c); auto. *)
  (* Qed. *)
  
  (* Lemma ff2dl_dl2ff_id : forall r c (m : DL.mat r c), ff2dl (dl2ff m) = m. *)
  (* Proof. *)
  (*   intros. unfold ff2dl,dl2ff. rewrite FF.m2l_l2m_id. *)
  (*   apply DL.l2m_m2l_id. apply DL.m2l_length. apply DL.m2l_width. *)
  (* Qed. *)
  
  (* Lemma dl2ff_ff2dl_id : forall r c (m : FF.mat r c), dl2ff (ff2dl m) = m. *)
  (* Proof. *)
  (*   intros. unfold dl2ff,ff2dl. rewrite DL.m2l_l2m_id. *)
  (*   apply FF.l2m_m2l_id; auto. apply FF.m2l_length. apply FF.m2l_width. *)
  (* Qed. *)
  
End BasicMatrixTheory.


  
(* ######################################################################### *)
(** * Collection of all implementations for ring matrix theory *)
Module RingMatrixTheory (E : RingElementType).

  (** export base element, contain: types, definitions, notations, etc.  *)
  Export E.
  
  (* ======================================================================= *)
  (** ** Short name for concrete implementations *)
  Module DL <: RingMatrixTheory E := RingMatrixTheoryDL E.
  Module DP <: RingMatrixTheory E := RingMatrixTheoryDP E.
  Module DR <: RingMatrixTheory E := RingMatrixTheoryDR E.
  Module NF <: RingMatrixTheory E := RingMatrixTheoryNF E.
  Module SF <: RingMatrixTheory E := RingMatrixTheorySF E.
  (* Module FF <: RingMatrixTheory E := RingMatrixTheoryFF E. *)

  (** Basic matrix theory, contain conversion and properties *)
  Module Export All := BasicMatrixTheory E.

  (* ======================================================================= *)
  (** ** Homomorphic relation *)

  (** DR.madd and DP.madd is homomorphic relation over dr2dp *)
  Lemma hom_madd_dr2dp : forall (r c:nat),
      Homomorphic DR.madd DP.madd All.dr2dp (Beq:=@DP.meq r c).
  Proof.
    intros. constructor. intros.
    unfold dr2dp.
    rewrite (homomorphic (Homomorphic:=DR.m2l_madd_homo r c)).
    rewrite <- DP.l2m_madd_homo; auto with mat. easy.
  Qed.

  (* Lemma hom_madd_dr2sf : forall r c,  *)
  (*   Homomorphic DR.madd (@SF.madd r c) (@dr2sf r c) (Beq:=@SF.meq r c). *)
  (* Proof. *)
  (*   intros. constructor. intros. *)
  (*   unfold dr2sf. *)
  (*   rewrite (homomorphic (Homomorphic:=DR.m2l_madd_homo r c)). *)
  (*   rewrite <- DR.l2m_madd_homo; auto with mat. easy. *)
  (* Qed. *)
  
(*   Lemma hom_madd_dr2ff : forall r c,  *)
(*     Homomorphic DR.madd FF.madd (@dr2ff r c). *)
(*   Proof. *)
(*     intros r c m1 m2. destruct m1 as [d1 H1 W1], m2 as [d2 H2 W2]. *)
(*     unfold dr2ff. simpl. *)
(*     unfold matmap2dl. simpl. *)
(* (* (*     apply FF.meq_iff. intros i j Hi Hj. simpl. *) *)
(*     unfold dmap2. rewrite map2_nth. *)
(*     - rewrite map2_nth; auto. *)
(*       rewrite (width_imply_nth_length _ i c); auto. rewrite H1; auto. *)
(*       rewrite (width_imply_nth_length _ i c); auto. rewrite H2; auto. *)
(*     - subst; auto. *)
(*     - subst; auto. rewrite H2; auto. *)
(*   Qed. *)
(*  *)   *)
(*   Admitted. *)
  
  Lemma hom_madd_dp2dr : forall r c,
      Homomorphic DP.madd DR.madd (@dp2dr r c) (Beq:=@DR.meq r c).
  Proof.
  (*   intros r c m1 m2. *)
  (*   unfold dp2dr. apply DR.meq_iff. simpl. *)
  (*   unfold DR.l2m, Matrix.matmap2dl. simpl. *)
  (*   repeat rewrite Matrix.l2m_aux_eq; *)
  (*   try apply DP.m2l_length; *)
  (*   try apply DP.m2l_width. *)
  (*   apply DP.m2l_madd_homo. *)
    (* Qed. *)
    Admitted.
  
  Lemma hom_mmul_dr2dp : forall n,
      Homomorphic DR.mmul DP.mmul (@dr2dp n n) (Beq:=@DP.meq n n).
  Proof.
    (* intros n m1 m2. destruct m1 as [d1 H1 W1], m2 as [d2 H2 W2]. *)
    (* unfold dr2dp. simpl. *)
  Admitted.
  
  Lemma hom_mmul_dp2dr : forall n,
      Homomorphic DP.mmul DR.mmul (@dp2dr n n) (Beq:=@DR.meq n n).
  Proof.
    (* intros n m1 m2. *)
(*      destruct m1 as [d1 H1 W1], m2 as [d2 H2 W2]. *)
(*     unfold dr2dp. simpl. *)
    Admitted.
  
End RingMatrixTheory.


  
(* ######################################################################### *)
(** * Collection of all implementations for decidable field matrix theory *)
Module DecidableFieldMatrixTheory (E : DecidableFieldElementType).

  Export E.

  (* ======================================================================= *)
  (** ** Short name for concrete implementations *)
  Module DL <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryDL E.
  Module DP <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryDP E.
  Module DR <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryDR E.
  Module NF <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryNF E.
  Module SF <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheorySF E.
  (* Module FF <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryFF E. *)

  (** basic matrix theory, contain conversion and properties *)
  Module Export BasicMT := BasicMatrixTheory E.

  (**  ring matrix theory, contain conversion and properties *)
  Module Export RingMT := RingMatrixTheory E.

End DecidableFieldMatrixTheory.



(* ######################################################################### *)
(** * Collection of all implementations for eq decidable field matrix theory *)

(** Note: because FF module only support a special decidable field matrix theory,
    that means only support eq version. So, this module is designed for this
    purpose. *)

Module EqDecidableFieldMatrixTheory (B: BaseType) (E: EqDecidableFieldElementType B).

  Export E.
  
  (* ======================================================================= *)
  (** ** Short name for concrete implementations *)
  Module DL <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryDL E.
  Module DP <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryDP E.
  Module DR <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryDR E.
  Module NF <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryNF E.
  Module SF <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheorySF E.
  (* Module FF <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryFF B E. *)

  (** basic matrix theory, contain conversion and properties *)
  Module Export BasicMT := BasicMatrixTheory E.

  (**  ring matrix theory, contain conversion and properties *)
  Module Export RingMT := RingMatrixTheory E.

  (* ======================================================================= *)
  (** ** Homomorphic relation *)

End EqDecidableFieldMatrixTheory.

