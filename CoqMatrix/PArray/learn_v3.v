(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Learn PArray
  author    : ZhengPu Shi
  date      : 2023.01

  remark    :
  1. PArray
  (1). can be extracted to array in OCaml, so the performance is well
  (2). PArray could be evaluated in Coq directly, with the built-in support.
       That is, a technology similar to function will save the get/set operation
       in Coq, and reduce the result directly.
       So, this module is work well both in Coq and OCaml.
 *)

From Coq Require Import PArray.          (* native array *)
Import PArrayNotations.
From Coq Require Import Uint63.       (* int, used in PArray *)
From Coq Require Import Extraction.


(** * Extraction to OCaml *)

Require Import MyExtrOCamlInt63.
Require Import MyExtrOCamlPArray.


(** ** Extraction to OCaml of persistent arrays. *)

(** There is a problem for type of array, so we re-define these instructions *)
(* Require Import ExtrOCamlPArray. *)

Extract Constant PArray.array "'a" => "Parray.t".
Extraction Inline PArray.array.
(* Otherwise, the name conflicts with the primitive OCaml type [array] *)

Extract Constant PArray.make => "Parray.make".
Extract Constant PArray.get => "Parray.get".
Extract Constant PArray.default => "Parray.default".
Extract Constant PArray.set => "Parray.set".
Extract Constant PArray.length => "Parray.length".
Extract Constant PArray.copy => "Parray.copy".


(** int <-> nat *)
Definition i2n : int -> nat := fun i => BinInt.Z.to_nat (Uint63.to_Z i).
Definition n2i : nat -> int := fun n : nat => Uint63.of_Z (BinInt.Z.of_nat n).

Extraction "matrix.ml" is_even. make.
Recursive Extraction is_even.
Import ZArith.


Extraction "mat.ml" is_even.

Extract Constant PrimInt63.int => "int".


(** Come from "ExtrOCamlPArray" *)

Extract Constant PArray.array "'a" => "'a array".
Extraction Inline PArray.array.
(* Otherwise, the name conflicts with the primitive OCaml type [array] *)

Extract Constant PArray.make => "Array.make".
Extract Constant PArray.get => "Array.get".
Extract Constant PArray.default => "Array.default".
Extract Constant PArray.set => "Array.set".
Extract Constant PArray.length => "Array.length".
Extract Constant PArray.copy => "Array.copy".

Extract Constant Uint63.land => "Int.logand".
Extract Constant Uint63.lsr => "Int.shift_right_logical".
Extract Constant Uint63.eqb => "Int.equal".

Extract Constant Uint63.sub => "Int.sub".
Extract Constant Uint63.lsl => "Int.shift_left".
Extract Constant Uint63.lor => "Int.logor".
(* Extract Constant Uint63.of_int => "fun i -> Int.equal i 0L". *)
(* Extract Constant Uint63.is_zero => "fun i -> Int.equal i 0L". *)
(* Extract Constant Uint63.is_even => "fun i -> is_zero (land i 1L)". *)
(* Extract Constant 1 => "fun i -> is_zero (land i 1L)". *)
(* is_even = fun i : int => is_zero (i land 1) *)

(* Extract Constant 0x1 => "1L". fun i -> Int64.equal i 0L". *)

(* Extract Constant Sint63.asr => "Uint63.a_sr". *)
(* Extract Constant Uint63.lxor => "Uint63.l_xor". *)
(* Extract Constant Uint63.add => "Uint63.add". *)
(* Extract Constant Uint63.mul => "Uint63.mul". *)
(* Extract Constant Uint63.mulc => "Uint63.mulc". *)
(* Extract Constant Uint63.div => "Uint63.div". *)
(* Extract Constant Uint63.mod => "Uint63.rem". *)
(* Extract Constant Sint63.div => "Uint63.divs". *)
(* Extract Constant Sint63.rem => "Uint63.rems". *)

Zplus. is_even.
Check 1.
Recursive Extraction Uint63.to_Z_rec.
Search 1.
Open Scope int63_scope.
Check 1.
Compute 1.
Print 1.
Locate 1.
Check 1.
Print 1.
Print to_Z_rec.
Print Uint63.is_even.
Set Printing All.
(* Check 1%int63. *)
Recursive Extraction Uint63.is_even.

Print Uint63.to_Z_rec.
Print BinInt.Z.double.
Recursive Extraction Uint63.to_Z.
Extraction "mat.ml" Uint63.eqb Uint63.to_Z.  Uint63. n2i make.



PrimInt63. make Uint63.

Variable i : Uint63.int.
Check make i.
Print PrimInt63.
Print Uint63.
Locate Uint63.
Locate PrimInt63.

(** * Matrix theory *)

Require Import ZArith Reals.


Compute i2n 2. (* = 2 : nat *)
Compute n2i 2. (* = 2%uint63 : int *)

Record vec {A:Type} (n : nat) := {
    vec_arr : array A
  }.

Definition mk_vec {A} (n : nat) (a : A) : vec n := Build_vec A n (make (n2i n) a).

Compute mk_vec 3 R0.

Extraction "mat.ml" mk_vec.

Module test_extraction.



  (* Import ZArith. *)
  (* Open Scope Z. *)
  (* Definition z_arr1 := make 10 0. *)
  (* Search array. *)
  (* Definition z_arr1_0 := z_arr1.[0]. *)
  (* Compute z_arr1_0. *)

  (* Extract Constant int => "int". *)

End test_extraction.

Import test_extraction.



(** * Evaluation in Coq *)
Module test_evaluation.

End test_evaluation.

(*
  A loop with index of int type, but int is axiomized, i.e., it have not an
  inductive structure, thus, writing fixpoint function is hard.
  (1). we can use nat, the structure is easy, but max-size-of-nat is 5000
  (2). we can use Z, it is a bit complicate, and need to solve negative.
  (3). we can use positive, but also complicate.
 *)
Module test_loop.

  (* int <-> nat *)
  Definition i2n : int -> nat := fun i => BinInt.Z.to_nat (to_Z i).
  Definition n2i : nat -> int := fun n : nat => of_Z (BinInt.Z.of_nat n).
  Compute i2n 2. (* = 2 : nat *)
  Compute n2i 2. (* = 2%uint63 : int *)

  (** loop : init + a[i] + a[i+1] + ... *)
  Fixpoint loop {A:Type} (arr : array A) (cnt : nat) (i : int) (f : A -> A -> A)
    (init : A) : A :=
    match cnt with
    | O => init
    | S cnt' => loop arr cnt' (i + 1) f (f init arr.[i])
    end.

  Definition data1 := make 50 1.
  Compute data1.
  (* = [| 
     1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
     1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
     1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
     1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
     1; 1; 1; 1; 1; 1; 1; 1; 1; 1 | 1 : nat |]
     : array nat *)

  Variable f : nat -> nat -> nat.
  Compute loop data1 10 0 f 0. (*
     = f (f (f (f (f (f (f (f (f (f 0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1
     : nat *)
  Compute loop data1 10 0 (Nat.add) 0. (*  = 10 *)
End parray_loop_with_nat.


Section matrix.

  Print array.


End matrix.
