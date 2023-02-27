(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector theory on Z.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Import VectorAll.


(* ######################################################################### *)
(** * Export vector theory on concrete elements *)

Module VectorAllZ.
  Include RingVectorTheory RingElementTypeZ.
  Open Scope Z_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorAllZ.
  
Module VectorZ_DL.
  Include VectorAllZ.DL.
  Open Scope Z_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorZ_DL.

Module VectorZ_DP.
  Include VectorAllZ.DP.
  Open Scope Z_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorZ_DP.

Module VectorZ_DR.
  Include VectorAllZ.DR.
  Open Scope Z_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorZ_DR.

Module VectorZ_NF.
  Include VectorAllZ.NF.
  Open Scope Z_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorZ_NF.

Module VectorZ_SF.
  Include VectorAllZ.SF.
  Open Scope Z_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorZ_SF.


(* ######################################################################### *)
(** * Extended vector theory *)

(** Set a default model *)
Export VectorZ_SF.


(** General usage, no need to select low-level model *)
Section Test.
  (* Compute v2l (@l2v 3 [1;2;3]). *)
  
End Test.

