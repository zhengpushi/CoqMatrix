(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : test for matrix implmented with List List
  author    : ZhengPu Shi
  date      : 2021.05
*)

From FCS Require Export ListList.Matrix.


(** ** Definition of Matrix Type *)

Definition ex_dl1 := [[1;2];[3;4]].
Definition ex_dl1_len : length ex_dl1 = 2. auto. Qed.
Definition ex_dl1_wid : width ex_dl1 2. compute. auto. Qed.

Definition ex_mat1 : @mat nat 2 2 := mk_mat ex_dl1 ex_dl1_len ex_dl1_wid.
Definition ex_mat2 : mat 2 2 := mk_mat ex_dl1 ex_dl1_len ex_dl1_wid.
Definition ex_mat3 : mat 2 2 := {|
  mat_data := ex_dl1; 
  mat_height := ex_dl1_len; 
  mat_width := ex_dl1_wid
|}.

Compute mat_data ex_mat1.
Compute ex_mat1.(mat_data).


(** ** matrix with specific size *)

(** mat_1_1 *)

Compute mk_mat_1_1 3.

(** mat_1_2 *)

Compute mk_mat_1_2' nat 1 2.

(** mat_0_c *)

Compute mk_mat_0_c 3.

(** mat_1_c *)

Compute mk_mat_1_c [1;2;3] 3 eq_refl.

(** mat_1_2, mat_1_3, ... *)
  
Compute mk_mat_1_2 5 6.
  
Compute mk_mat_1_3 5 6 7.
  
Compute mk_mat_1_4 5 6 7 8.


(** mat_r_0 *)

Compute mk_mat_r_0 3.


(** mat_r_1 *)

Compute mk_mat_r_1 [1;2;3] 3 eq_refl.


(** mat_2_1, mat_3_1, ... *)

Compute mk_mat_2_1 5 6.

Compute mk_mat_3_1 5 6 7.

Compute mk_mat_4_1 5 6 7 8.

(** !Notice, this example might be error, HOW to explainate it?
  the base element could be a list, and list could be any length. *)
Compute mk_mat_4_1 [1;2] [2;3;4] [] [].


(** mat_3_3 *)

Compute mk_mat_3_3 1 2 3 4 5 6 7 8 9.

(** Get Matrix Element *)

Compute mat_nth 0 (mk_mat_3_3 1 2 3 4 5 6 7 8 9) 1 2.


(** TEST code, unfinished *)
Module test_alpha1.

  Require Import Reals.
  Open Scope R_scope.

  Require Import Arith.

  Section Complex.

    Record Complex := mkComplex {
      Re : R;
      Im : R
    }.

  End Complex.

  Section HermitonMatrix.
    Check mat.
    Variable mat_mul : forall {A r c t}, @mat A r c -> @mat A c t -> @mat A r t.
    Variable mat_H : forall {A r c}, @mat A r c -> @mat A r c.
    
    (* Hermiton Matrix is a matrix with a bit good properties *)
    Record HMat {A r c} := mkHMat {
      hmmat : @mat A r c;
      hmcond : mat_H hmmat = hmmat
    }.
    
  End HermitonMatrix.

End test_alpha1.


(** ** Matrix map to a dlist *)

Compute matmapdl Nat.succ ex_mat1.


(** ** Matrix map2 to a dlist *)

Compute matmap2dl Nat.add ex_mat1 ex_mat1.


(** ** Matrix map *)

Compute matmap Nat.succ ex_mat1.


(** ** Matrix map2 *)

Compute matmap2 Nat.add ex_mat1 ex_mat1.


(** ** zero matrix and unit matrix *)

Compute matzero 0 3 2.

Compute matunit 0 1 3.


(** ** matrix transpose *)

Compute ex_mat1.
Compute mat_trans ex_mat1.
Compute mat_trans (mk_mat_r_0 5).
Compute mat_trans (mk_mat_0_c 5).


(** ** matrix addition *)

Compute matadd Nat.add ex_mat1 ex_mat1.


(** ** matrix substraction and opposition *)

Compute matopp Nat.succ ex_mat1.
Compute matsub Nat.sub ex_mat1 ex_mat1.


(** ** matrix multiplication *)

Compute matmul 0 Nat.add Nat.mul ex_mat1 ex_mat1.


(** ** Multiplication with a constant and a matrix *)

Compute matcmul Nat.mul 3 ex_mat1.
Compute matmulc Nat.mul ex_mat1 3.
