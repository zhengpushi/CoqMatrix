(*
  purpose   : Test extracted Ocaml program of Matrix over float.
  author    : ZhengPu Shi
  date      : Nov 1, 2022

  remark    :
  1. R type in Coq ==> float type in Ocaml.
  2. Matirx operations:
     l2m: from list to a matrix
     m2l: from matrix to list.
     f2m: from function to matrix, for  input dynamically
     m2f: from matrix to function, for output dynamically
     madd
     mmul
     mget: get element
     mset: set element
  3. The test is aimed to "construct, calculate, read and write functions of matrix"
     consider the time and space cost roughly.
 *)

(** This is example from Matlab, as a contrast for correctness.
>> mat1 = [1,2,3; 4,5,6]

mat1 =

     1     2     3
     4     5     6

>> mat2 = mat1'

mat2 =

     1     4
     2     5
     3     6

>> mat3 = mat1 * mat2

mat3 =

    14    32
    32    77

>> mat4 = mat2 * mat1

mat4 =

    17    22    27
    22    29    36
    27    36    45

*)

Require Import Extraction.
Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlR.
Require Import Reals MatrixAll.
Require Import List. Import ListNotations.

(** A interface for float matrix *)
Module Type FloatMatrixSig.
  
  (** Matrix type *)
  Parameter mat : nat -> nat -> Type.
  (** Matrix addition *)
  Parameter madd : forall r c, mat r c -> mat r c -> mat r c.
  (** Matrix multiplication *)
  Parameter mmul : forall r c s, mat r c -> mat c s -> mat r s.
  (** Conversion between list and matrix *)
  Parameter l2m : forall r c, list (list R) -> mat r c.
  (* Parameter m2l : forall r c, mat r c -> (nat * nat * list (list R)). *)
  Parameter m2l : forall r c, mat r c -> list (list R).
  (** Conversion between function and matrix *)
  (* Parameter f2m : forall r c, (nat -> nat -> R) -> mat r c. *)
  (* Parameter m2f : forall r c, mat r c -> (nat * nat * (nat -> nat -> R)). *)
  (** Get / Set element *)
  (* Parameter mget : forall r c, mat r c -> nat -> nat -> R. *)
  (* Parameter mset : forall r c, mat r c -> nat -> nat -> R -> mat r c. *)

End FloatMatrixSig.


(** Many implementations *)
Module EqMatrixAllR := EqDecidableFieldMatrixTheory BaseTypeR
                         DecidableFieldElementTypeR.
Module MatrixR_DR := EqMatrixAllR.DR.
Module MatrixR_DP := EqMatrixAllR.DP.
Module MatrixR_DL := EqMatrixAllR.DL.
Module MatrixR_NF := EqMatrixAllR.NF.
Module MatrixR_SF := EqMatrixAllR.SF.
(* Module MatrixR_FF := EqMatrixAllR.FF. *)

Module DL <: FloatMatrixSig := MatrixR_DL.
Module DP <: FloatMatrixSig := MatrixR_DP.
Module DR <: FloatMatrixSig := MatrixR_DR.
Module NF <: FloatMatrixSig := MatrixR_NF.
Module SF <: FloatMatrixSig := MatrixR_SF.
(* Module FF <: FloatMatrixSig := MatrixR_FF. *)

(* Module DL <: FloatMatrixSig. *)
(*   Import MatrixR_DL. *)
(*   Locate mat. *)
(*   Check madd. *)
(*   Check mat. *)
(*   Definition mat := @mat R. *)
(*   Definition madd := @madd. *)
(*   Definition mmul := @mmul. *)
(*   Check @l2m. *)
(*   Definition l2m := @l2m. *)
(*   Definition m2l {r c} (m : mat r c) := (r, c, @m2l _ _ m). *)
(*   Definition mget := @mget. *)
(*   Definition mset := @mset. *)
(* End DL. *)

(* Module DP <: FloatMatrixSig. *)
(*   Import MatrixR_DP. *)
(*   Definition mat := @mat R. *)
(*   Definition madd := @madd. *)
(*   Definition mmul := @mmul. *)
(*   Definition l2m := @l2m. *)
(*   Definition m2l {r c} (m : mat r c) := (r, c, @m2l _ _ m). *)
(*   (* Definition mget := @mget. *) *)
(*   (* Definition mset := @mset. *) *)
(* End DP. *)

(* Module DR <: FloatMatrixSig. *)
(*   Import MatrixR_DR. *)
(*   Definition mat := @mat R. *)
(*   Definition madd := @madd. *)
(*   Definition mmul := @mmul. *)
(*   Definition l2m := @l2m. *)
(*   Definition m2l {r c} (m : mat r c) := (r, c, @m2l _ _ m). *)
(*   (* Definition mget := @mget. *) *)
(*   (* Definition mset := @mset. *) *)
(* End DR. *)

(* Module NF <: FloatMatrixSig. *)
(*   Import MatrixR_NF. *)
(*   Definition mat := @mat R. *)
(*   Definition madd := @madd. *)
(*   Definition mmul := @mmul. *)
(*   Definition l2m := @l2m. *)
(*   Definition m2l {r c} (m : mat r c) := (r, c, @m2l _ _ m). *)
(*   (* Definition mget := @mget. *) *)
(*   (* Definition mset := @mset. *) *)
(* End NF. *)

(* Module FF <: FloatMatrixSig. *)
(*   Import MatrixR_FF. *)
(*   Definition mat := @mat R. *)
(*   Definition madd := @madd. *)
(*   Definition mmul := @mmul. *)
(*   Definition l2m := @l2m. *)
(*   Definition m2l {r c} (m : mat r c) := (r, c, @m2l _ _ m). *)
(*   (* Definition mget := @mget. *) *)
(*   (* Definition mset := @mset. *) *)
(* End FF. *)

(** two float numbers are comparison decidable *)
Extract Constant total_order_T => "fun r1 r2 ->
  let c = Float.compare r1 r2 in
  if c < 0 then Some true
  else (if c = 0 then None else Some false)".

Extraction "matrix.ml" DL DP DR NF SF. (* FF. *)


