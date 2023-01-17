(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : block matrix
  author    : ZhengPu Shi
  date      : 2021.05
*)

From FCS Require Export Mat_def.
From FCS Require Export Mat_map.
From FCS Require Export Mat_IO.
From FCS Require Export Mat_mul.


(** ** Definition of Block Matrix *)

Section bmat_def.

  Variable A : Type.
  Variable A0 A1 : A.
  Variable fopp : A -> A.
  Variable fadd : A -> A.
  Variable r0 c0 : nat.
  
  Definition M := @mat A r0 c0.
  Definition M0 := matzero A r0 c0.
  Definition M1 := matunit A0 A1 r0.
  
  
