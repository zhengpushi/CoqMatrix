(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector theory on Qc.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

Require Import VectorAll.


(* ######################################################################### *)
(** * Vector theory on Qc *)

(** ** Export vector theory on concrete elements *)

(** vector theory with all models *)
Module VectorAllQc := DecidableFieldVectorTheory DecidableFieldElementTypeQc.
Module VectorQc_DL := VectorAllQc.DL.
Module VectorQc_DP := VectorAllQc.DP.
Module VectorQc_DR := VectorAllQc.DR.
Module VectorQc_NF := VectorAllQc.NF.
Module VectorQc_SF := VectorAllQc.SF.

(** Extended vector theory *)
Module VectorQc.
  Export VectorQc_SF.

End VectorQc.


(** ** Test *)
Section Test.
  Import VectorQc.
  Open Scope Q.

  Let l : list Qc := map Q2Qc [1;2;3].
  (* Compute v2l (@l2v 3 l). *)
  
End Test.
