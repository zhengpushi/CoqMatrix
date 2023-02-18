(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Entrance for access all matrix.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export ElementType MatrixTheory.

Require Import
  DepPair.MatrixTheoryDP
  DepList.MatrixTheoryDL
  DepRec.MatrixTheoryDR
  NatFun.MatrixTheoryNF
  SafeNatFun.MatrixTheorySF
  FinFun.MatrixTheoryFF
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

  Lemma hom_madd_dr2nf : forall r c, 
    Homomorphic DR.madd (@NF.madd r c) (@dr2nf r c) (Beq:=@NF.meq r c).
  Proof.
  (*   intros r c m1 m2. destruct m1 as [d1 H1 W1], m2 as [d2 H2 W2]. *)
  (*   unfold dr2nf. simpl. *)
  (*   unfold matmap2dl. simpl. *)
  (*   apply NF.meq_iff. intros i j Hi Hj. simpl. *)
  (*   unfold dmap2. rewrite map2_nth. *)
  (*   - rewrite map2_nth; auto. *)
  (*     rewrite (width_imply_nth_length _ i c); auto. rewrite H1; auto. *)
  (*     rewrite (width_imply_nth_length _ i c); auto. rewrite H2; auto. *)
  (*   - subst; auto. *)
  (*   - subst; auto. rewrite H2; auto. *)
    (* Qed. *)
    Admitted.
  
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

  (* ======================================================================= *)
  (** ** Short name for concrete implementations *)
  Module DL <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryDL E.
  Module DP <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryDP E.
  Module DR <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryDR E.
  Module NF <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryNF E.
  Module SF <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheorySF E.
  Module FF <: DecidableFieldMatrixTheory E := DecidableFieldMatrixTheoryFF B E.

  (** basic matrix theory, contain conversion and properties *)
  Module Export BasicMT := BasicMatrixTheory E.

  (**  ring matrix theory, contain conversion and properties *)
  Module Export RingMT := RingMatrixTheory E.

  (* ======================================================================= *)
  (** ** Homomorphic relation *)

End EqDecidableFieldMatrixTheory.



(* ######################################################################### *)
(** * Collection of all different implementations (Concrete Module) *)

(** Note: different data type derived different matrix theory.
    Nat   : basic matrix theory
    Z     : ring matrix theory
    Q     : field matrix theroy
    Qc    : field matrix theroy
    R     : field matrix theory
*)

(** *** Matrix based on Nat *)
Module MatrixAllNat := BasicMatrixTheory ElementTypeNat.
Module MatrixNat_DL := MatrixAllNat.DL.
Module MatrixNat_DP := MatrixAllNat.DP.
Module MatrixNat_DR := MatrixAllNat.DR.
Module MatrixNat_NF := MatrixAllNat.NF.
Module MatrixNat_SF := MatrixAllNat.SF.

Section Test.
  Import MatrixNat_DR.

  Let m1 := @l2m 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute m2l m1. *)
  (*      = [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]]
     : list (list ElementTypeNat.A) *)

  (* Compute m2l (mmap S m1). *)
  (*      = [[2; 3; 4]; [5; 6; 7]; [8; 9; 10]]
     : list (list ElementTypeNat.A) *)


  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : nat.
  Let m2 := @l2m 3 3 [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  (* Compute m2l m2. *)
  (*      = [[a11; a12; a13]; [a21; a22; a23]; [a31; a32; a33]]
     : list (list ElementTypeNat.A) *)

  (* Compute m2l (mmap S m2). *)
  (*      = [[S a11; S a12; S a13]; [S a21; S a22; S a23]; [S a31; S a32; S a33]]
     : list (list ElementTypeNat.A) *)

End Test.


(** *** Matrix based on Z *)
Module MatrixAllZ := RingMatrixTheory RingElementTypeZ.
Module MatrixZ_DL := MatrixAllZ.DL.
Module MatrixZ_DP := MatrixAllZ.DP.
Module MatrixZ_DR := MatrixAllZ.DR.
Module MatrixZ_NF := MatrixAllZ.NF.
Module MatrixZ_SF := MatrixAllZ.SF.

Section Test.
  Import MatrixZ_DP ZArith.
  Open Scope Z.
  Open Scope mat_scope.

  Let m1 := @l2m 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute m2l m1. *)
  (*      = [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]]
     : list (list RingElementTypeZ.A) *)

  (* Compute m2l (mmap Z.opp m1). *)
  (*      = [[-1; -2; -3]; [-4; -5; -6]; [-7; -8; -9]]
     : list (list RingElementTypeZ.A) *)

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : Z.
  Let m2 := @l2m 3 3 [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  (* Compute m2l m2. *)
  (*      = [[a11; a12; a13]; [a21; a22; a23]; [a31; a32; a33]]
     : list (list RingElementTypeZ.A) *)

  (* Eval cbn in m2l (mmap Z.opp m2). *)
  (*      = [[(- a11)%Z; (- a12)%Z; (- a13)%Z]; [(- a21)%Z; (- a22)%Z; (- a23)%Z];
        [(- a31)%Z; (- a32)%Z; (- a33)%Z]]
     : list (list RingElementTypeZ.A) *)

  Let m3 := mk_mat_3_3 10 11 12 13 14 15 16 17 18.
  (* Eval cbn in m2l (m2 * m2). *)
  (*      = [[Aadd (Amul a11 a11) (Aadd (Amul a12 a21) (Aadd (Amul a13 a31) A0));
         Aadd (Amul a11 a12) (Aadd (Amul a12 a22) (Aadd (Amul a13 a32) A0));
         Aadd (Amul a11 a13) (Aadd (Amul a12 a23) (Aadd (Amul a13 a33) A0))];
        [Aadd (Amul a21 a11) (Aadd (Amul a22 a21) (Aadd (Amul a23 a31) A0));
         Aadd (Amul a21 a12) (Aadd (Amul a22 a22) (Aadd (Amul a23 a32) A0));
         Aadd (Amul a21 a13) (Aadd (Amul a22 a23) (Aadd (Amul a23 a33) A0))];
        [Aadd (Amul a31 a11) (Aadd (Amul a32 a21) (Aadd (Amul a33 a31) A0));
         Aadd (Amul a31 a12) (Aadd (Amul a32 a22) (Aadd (Amul a33 a32) A0));
         Aadd (Amul a31 a13) (Aadd (Amul a32 a23) (Aadd (Amul a33 a33) A0))]]
     : list (list A) *)

  (* Eval cbn in m2l (m1 * m3). *)
  (*      = [[84; 90; 96]; [201; 216; 231]; [318; 342; 366]]
     : list (list A) *)

End Test.


(** *** Matrix based on Q *)
Module MatrixAllQ := DecidableFieldMatrixTheory DecidableFieldElementTypeQ.
Module MatrixQ_DL := MatrixAllQ.DL.
Module MatrixQ_DP := MatrixAllQ.DP.
Module MatrixQ_DR := MatrixAllQ.DR.
Module MatrixQ_NF := MatrixAllQ.NF.
Module MatrixQ_SF := MatrixAllQ.SF.
(* Module MatrixQ_FF := MatrixAllQ.FF. *)

Section Test.
  Import MatrixQ_DL QArith.
  
  (* Compute m2l (mat1 4). *)
  (*      = [[1; 0; 0; 0]; [0; 1; 0; 0]; [0; 0; 1; 0]; [0; 0; 0; 1]]
     : list (list A) *)

End Test.


(** *** Matrix based on Qc *)
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


(** *** Matrix based on R *)
Module MatrixAllR := DecidableFieldMatrixTheory DecidableFieldElementTypeR.
Module MatrixR_DL := MatrixAllR.DL.
Module MatrixR_DP := MatrixAllR.DP.
Module MatrixR_DR := MatrixAllR.DR.
Module MatrixR_NF := MatrixAllR.NF.
Module MatrixR_SF := MatrixAllR.SF.
(* Module MatrixR_FF := MatrixAllR.FF. *)


(** *** EqDecidableFieldMatrixTheory demo *)
Module Demo_EqDecidableFieldElementType.
  Module EqMatrixAllR := EqDecidableFieldMatrixTheory BaseTypeR
                           DecidableFieldElementTypeR.
  Module MatrixR_DL := EqMatrixAllR.DL.
  Module MatrixR_DP := EqMatrixAllR.DP.
  Module MatrixR_DR := EqMatrixAllR.DR.
  Module MatrixR_NF := EqMatrixAllR.NF.
  Module MatrixR_SF := EqMatrixAllR.SF.
  Module MatrixR_FF := EqMatrixAllR.FF.

End Demo_EqDecidableFieldElementType.
       

(* ######################################################################### *)
(** * More usage demo *)

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

(** test DR *)
Module Demo_usage_DR.
  
  Import MatrixR_DR.
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

End Demo_usage_DR.

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
