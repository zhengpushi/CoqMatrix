(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extraction of [R] into Ocaml's [float]
  author    : ZhengPu Shi
  date      : Nov 3, 2022

  Reference :
  1. coq/theories/extraction/ExtrOcamlNatInt.v

*)

Require Import Extraction.
Require Import Reals.

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
(* Extract Constant pow => 
  "fun r0 n -> if n=0 then 1.0 else (r0 *. (pow r0 (n-1)))". *)
