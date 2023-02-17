(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extract this module to OCaml code
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
*)

(* Require Import Reals.
Require Import Reals.Abstract.ConstructiveReals.
Require Import Reals.Cauchy.ConstructiveCauchyReals.
Check Rabst.
Check mkCReal. *)


Require Import FieldStruct.
Require Import Sequence.
Require Import MatrixThy.
Require Import VectorThy.
Require Import Inversion.
Require Import Reals.

Require Import Extraction.

Module Import SequenceR := Sequence FieldR.FieldDefR.
Module Import MatrixR := MatrixThy FieldR.FieldDefR.
Module Import VectorR := VectorThy FieldR.FieldDefR.
Module Import InversionR := Inversion FieldR.FieldDefR.


(* some inductive datatypes *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive nat => "int" [ "0" "Int.succ" ] 
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(* constant - Real number and operations *)
Extract Constant R => float.

(* patch for coq 8.11 and newer *)
Extract Constant Rabst => "__".
Extract Constant Rrepr => "__".


Extract Constant R0 => "0.0".
Extract Constant R1 => "1.0".
Extract Constant PI => "Float.pi".
Extract Constant Rplus => "(+.)".
Extract Constant Rmult => "( *. )".
Extract Constant Rminus => "(-.)".
Extract Constant Ropp => "fun a -> (0.0 -. a)".
Extract Constant Rinv => "fun a -> (1.0 /. a)".
Extract Constant Rpower => "Float.pow".
Extract Constant sin => "Float.sin".
Extract Constant cos => "Float.cos".
Extract Constant sqrt => "Float.sqrt".
Extract Constant atan => "Float.atan".
Extract Constant acos => "Float.acos".
Extract Constant Req_EM_T => "Float.equal".


Extract Constant FieldR.FieldDefR.A => float.
Extract Constant FieldR.FieldDefR.A0 => "0.0".
Extract Constant FieldR.FieldDefR.A1 => "1.0".
Extract Constant FieldR.FieldDefR.Aadd => "(+.)".
Extract Constant FieldR.FieldDefR.Amul => "( *. )".
(* Extract Constant FieldR.FieldDefR.Asub => "(-.)". *)
Extract Constant FieldR.FieldDefR.Aopp => "fun a -> (0.0 -. a)".
Extract Constant FieldR.FieldDefR.Ainv => "fun a -> (1.0 /. a)".
(* Extract Constant FieldR.FieldDefR.Adiv => "( /. )". *)
Extract Constant FieldR.FieldDefR.Aeqb => "Float.equal".
(* Definition Aeqdec : forall x y : RingR.A, {x = y} + {x <> y}. *)


Recursive Extraction SequenceR MatrixR VectorR Inversion.

Extraction "ocaml_test/seq.ml" SequenceR.
Extraction "ocaml_test/mat.ml" MatrixR.
Extraction "ocaml_test/vec.ml" VectorR.
Extraction "ocaml_test/inv.ml" InversionR.

