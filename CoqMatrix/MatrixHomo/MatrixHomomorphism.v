(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Homomorphism theory on matrix.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export MatrixAll.
Require Export HomomorphismThy.

Require Import Lia.
Require Import List.


(** * DR and DP is homomorphism *)
Module Homo_DR_DP (E : RingElementType).

  (** Instantialize the functor to module *)
  Module Import MatrixAllInst := MatrixAll.RingMatrixTheory E.
  
  (* ====================================================== *)
  (** ** DR and DP is homomorphism with respect to madd *)

  (** Examples: prove properties of madd in DP with the help of DR *)

  Example mdp_madd_comm : forall r c,
    Commutative (@DR.madd r c) DR.meq -> Commutative (@DP.madd r c) DP.meq.
  Proof.
    intros r c H.
    apply (homo_keep_comm (fa := @DR.madd r c) (Aeq:=DR.meq)); auto.
    constructor. 
    exists dr2dp. split.
    - apply hom_madd_dr2dp.
    - split.
      + apply dr2dp_surj.
      + apply dr2dp_aeq_mor. 
  Qed.
  
  Example mdp_madd_assoc : forall r c,
    Associative (@DR.madd r c) DR.meq -> Associative (@DP.madd r c) DP.meq.
  Proof.
    intros r c H.
    apply (homo_keep_assoc (fa := @DR.madd r c) (Aeq:=DR.meq)); auto.
    constructor.
    exists dr2dp. split.
    - apply hom_madd_dr2dp.
    - split.
      + apply dr2dp_surj.
      + apply dr2dp_aeq_mor.
  Qed.

  
  (** Examples: prove properties of madd in DR with the help of DP *)
  
  Example mdr_madd_comm : forall r c,
    Commutative (@DP.madd r c) DP.meq -> Commutative (@DR.madd r c) DR.meq.
  Proof.
    intros r c H.
    apply (homo_keep_comm (fa := @DP.madd r c) (Aeq:=DP.meq)); auto.
    constructor.
    exists dp2dr. split.
    - apply hom_madd_dp2dr.
    - split.
      + apply dp2dr_surj.
      + apply dp2dr_aeq_mor.
  Qed.
  
End Homo_DR_DP.


