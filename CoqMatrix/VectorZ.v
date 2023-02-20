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
(** * Vector theory on Z *)

(** ** Export vector theory on concrete elements *)

(** vector theory with all models *)
Module VectorAllZ := RingVectorTheory RingElementTypeZ.
Module VectorZ_DL := VectorAllZ.DL.
Module VectorZ_DP := VectorAllZ.DP.
Module VectorZ_DR := VectorAllZ.DR.
Module VectorZ_NF := VectorAllZ.NF.
Module VectorZ_SF := VectorAllZ.SF.

(** Extended vector theory *)
Module VectorZ.
  Export VectorZ_SF.

End VectorZ.


(** ** Test *)
Section Test.
  Import VectorZ.
  Open Scope Z.
  (* Compute v2l (@l2v 3 [1;2;3]). *)
  
End Test.

