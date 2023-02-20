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
(** * Vector theory on nat *)

(** ** Export vector theory on concrete elements *)

(** vector theory with all models *)
Module VectorAllNat := BasicVectorTheory ElementTypeNat.
Module VectorNat_DL := VectorAllNat.DL.
Module VectorNat_DP := VectorAllNat.DP.
Module VectorNat_DR := VectorAllNat.DR.
Module VectorNat_NF := VectorAllNat.NF.
Module VectorNat_SF := VectorAllNat.SF.

(** Extended vector theory *)
Module VectorNat.
  Export VectorNat_SF.

End VectorNat.


(** ** Test *)
Section Test.
  Import VectorNat.
  (* Compute v2l (@l2v 3 [1;2;3]). *)
  
End Test.
