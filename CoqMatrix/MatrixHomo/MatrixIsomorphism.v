(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Isomorphism theory on matrix.
  author    : ZhengPu Shi
  date      : 2022.07
 *)

Require Export MatrixAll.
Require Export IsomorphismThy.

Require Import Lia.
Require Import List.


(** * DR and DP is isomorphism *)
Module Iso_DR_DP (E : RingElementType).
  
  (** Instantialize the functor to module *)
  Module Export MatrixAllInst := RingMatrixTheory E.
  
  (* ====================================================== *)
  (** ** DR and DP is isomorphism with respect to madd *)
  
  (** Examples: DR --> DP *)
  
  Example dr_dp_madd_comm : forall r c,
      Commutative (@DR.madd r c) DR.meq <-> Commutative (@DP.madd r c) DP.meq.
  Proof.
    intros r c.
    apply isomor_keep_comm.
    constructor.
    exists dr2dp. split.
    - apply hom_madd_dr2dp.
    - split. apply dr2dp_bij. apply dr2dp_aeq_mor.
      Unshelve. auto. auto.
  Qed.
  
  Example dr_dp_madd_assoc : forall r c,
      Associative (@DR.madd r c) DR.meq <-> Associative (@DP.madd r c) DP.meq.
  Proof.
    intros r c.
    apply isomor_keep_assoc.
    constructor.
    exists dr2dp. split.
    - apply hom_madd_dr2dp.
    - split. apply dr2dp_bij. apply dr2dp_aeq_mor.
      Unshelve. auto. auto.
  Qed.

  
  (** Matrix multiplication operation is closed at square matrix only. *)
  
  Example dr_dp_mmul_assoc : forall n,
      Associative (@DR.mmul n n n) DR.meq <-> Associative (@DP.mmul n n n) DP.meq.
  Proof.
  Admitted.
  
  Example dr_dp_mmul_madd_distr_left : forall n,
      DistributiveLeft (@DR.madd n n) (@DR.mmul n n n) DR.meq <->
        DistributiveLeft (@DP.madd n n) (@DP.mmul n n n) DP.meq.
  Proof.
  Admitted.
  
  (* Example dr_dp_madd_cancel_left : forall r c, *)
  (*     cancel_left (@DR.madd r c) <-> cancel_left (@DP.madd r c). *)
  (* Proof. *)
  (*   intros r c. *)
  (*   apply isomor_keep_cancel_left with (fa := @DR.madd r c). *)
  (*   exists dr2dp. split. apply hom_madd_dr2dp. apply dr2dp_bij. *)
  (* Qed. *)
  
  (* Example dr_dp_madd_cancel_right : forall r c, *)
  (*     cancel_right (@DR.madd r c) <-> cancel_right (@DP.madd r c). *)
  (* Proof. *)
  (*   intros r c. *)
  (*   apply isomor_keep_cancel_right with (fa := @DR.madd r c). *)
  (*   exists dr2dp. split. apply hom_madd_dr2dp. apply dr2dp_bij. *)
  (* Qed. *)
  
End Iso_DR_DP.


