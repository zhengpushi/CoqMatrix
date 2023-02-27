(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector theory on nat.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Import VectorAll.


(* ######################################################################### *)
(** * Export vector theory on concrete elements *)

Module VectorAllNat.
  Include BasicVectorTheory ElementTypeNat.
  Open Scope nat_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorAllNat.
  
Module VectorNat_DL.
  Include VectorAllNat.DL.
  Open Scope nat_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorNat_DL.

Module VectorNat_DP.
  Include VectorAllNat.DP.
  Open Scope nat_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorNat_DP.

Module VectorNat_DR.
  Include VectorAllNat.DR.
  Open Scope nat_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorNat_DR.

Module VectorNat_NF.
  Include VectorAllNat.NF.
  Open Scope nat_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorNat_NF.

Module VectorNat_SF.
  Include VectorAllNat.SF.
  Open Scope nat_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorNat_SF.


(* ######################################################################### *)
(** * Extended vector theory *)

(** Set a default model *)
Export VectorNat_SF.


(** General usage, no need to select low-level model *)
Section Test.
  (* Compute v2l (@l2v 3 [1;2;3]). *)
  
End Test.
