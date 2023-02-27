(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector theory on Qc.
  author    : ZhengPu Shi
  date      : 2021.12

  remark    :
  1. why we use Q_scope instead Qc_scope?
  (a). we can write 2, 3.5, etc. in Q_scope, but cannot in Qc_scope
  (b). Notation "1" has defined in Qc_scope, thus we cannot write
       a list of [1;2;3], which produce a type error.
       Because 2 is Q type, 1 is Qc type.
  (3). If we really need Qc, we can use function Q2Qc to do it.
 *)

Require Import VectorAll.


(* ######################################################################### *)
(** * Export vector theory on concrete elements *)

Module VectorAllQc.
  Include DecidableFieldVectorTheory DecidableFieldElementTypeQc.
  Open Scope Q_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorAllQc.
  
Module VectorQc_DL.
  Include VectorAllQc.DL.
  Open Scope Q_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorQc_DL.

Module VectorQc_DP.
  Include VectorAllQc.DP.
  Open Scope Q_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorQc_DP.

Module VectorQc_DR.
  Include VectorAllQc.DR.
  Open Scope Q_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorQc_DR.

Module VectorQc_NF.
  Include VectorAllQc.NF.
  Open Scope Q_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorQc_NF.

Module VectorQc_SF.
  Include VectorAllQc.SF.
  Open Scope Q_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorQc_SF.


(* ######################################################################### *)
(** * Extended matrix theory *)

(** Set a default model *)
Export VectorQc_SF.


(** General usage, no need to select low-level model *)
Section Test.

  Let l : list Qc := map Q2Qc [1;2;3].
  (* Compute v2l (@l2v 3 l). *)
  
End Test.
