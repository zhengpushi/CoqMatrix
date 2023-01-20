(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  author:   ZhengPu Shi
  date:     Apr 06, 2021
  
  purpose:
  1. learn Reals and Floats library
  2. how to connect them?
  3. how to extract code?
  
  conclusion:
  1. "float", 
    write in Coq is easy;
    eval in Coq is easy;
    proof is hard;
    extraction is easy.
  2. "R", 
    write in Coq is easy;
    eval in Coq is hard;
    proof is easy;
    extraction is hard.
  3. theare are no connection between these two library. 
*)

(** * 1. learn Reals and Floats libray *)

(** R type **)
Require Import Reals.

Open Scope R.

(* Support for direct writing float style after Coq 8.13 *)
Check 3.25.

(* arithmetic operations for abstract values is easy *)
Example r_ex1 : forall r1 r2, r1 + r2 = r2 + r1.
Proof.
  auto. Search (_ + _ = _ + _). apply Rplus_comm.
  Qed.

(* arithmetic operations for special values is hard *)
Definition r_1 := 0.1.
Definition r_2 := 0.2.
Definition r_3 := 0.3.
Example r_1_add_r_2 : r_1 + r_2 = r_3.
Proof.
  unfold r_1, r_2, r_3.
  Locate "+".
  Print Rplus.
  Search Rplus.
  Abort.

Require Import Rdefinitions.
Print Rplus.
Print Rplus_def.


(** Float **)
Require Import Floats.

(* Require Import FloatClass.
Require Import PrimFloat.
Require Import SpecFloat.
Require Import FloatOps.
Require Import FloatAxioms.
Require Import FloatLemmas. *)

Open Scope float.

(* Float type is based on Binary64 *)
Check 3.25.
Check 0.12.

(* special value is easy *)
Compute (0.25 + 1.25).
Compute (0.25 + 1.25 =? 1.5).
Compute (0.25 * 0.25).

(* import data structures *)

Print float_class.
(* Variant float_class : Set :=
    PNormal : float_class     positive number
  | NNormal : float_class     negative number
  | PSubn : float_class       ?
  | NSubn : float_class       ?
  | PZero : float_class       +0
  | NZero : float_class       -0
  | PInf : float_class        +inf
  | NInf : float_class        -inf
  | NaN : float_class         not a number 
  *)

Print float_comparison.
(* Variant
float_comparison : Set :=
    FEq : float_comparison        float equal
  | FLt : float_comparison        float less than
  | FGt : float_comparison        float great than
  | FNotComparable : float_comparison     float can not compare.
  *)

Print float.      (* primitive type for Binary64 floating-point numbers. *)
Check 0.25.
Check 0x1p-2.
Check 32.625.
Definition f_0_25 := 0.25.
Compute f_0_25.
Compute - f_0_25.
Compute (f_0_25 =? f_0_25).
Locate "=?".
Print eqb.
Print Coq.Floats.PrimFloat.eqb.

Print add.
Search add.
Check Int63.int.
Require Import Numbers.Cyclic.Int63.Int63.
Compute (of_int63 32%int63).


(* SpecFloat *)
(* IEEE754.Binary module of the Flocq library
http://flocq.gforge.inria.fr/
 *)

Print spec_float.
(* Variant spec_float :=
  | S754_zero (s : bool)
  | S754_infinity (s : bool)
  | S754_nan
  | S754_finite (s : bool) (m : positive) (e : Z).
   *)

Require Import Floats.

(* convert a float to fractional part in [0.5, 1.) and integer part.  *)
Compute frshiftexp 0.5.
Compute frshiftexp 0.25.
Compute frshiftexp 1.25.

Compute next_up 1.25.
Compute next_down 1.25.
Check 1.2499999999999998.

Compute infinity.
Compute neg_infinity.
Compute nan.
Compute of_int63 1.
Compute opp (div (of_int63 1) (of_int63 0)).
Compute div (of_int63 0) (of_int63 0).
Check nan.


Compute is_nan nan.
Compute nan =? nan.
Compute get_sign 0.25.


Compute emin.
Compute fexp 1 2 3.

Compute Zdigits2 64.

Compute canonical_mantissa 1 1 1 1.

Compute SFopp (S754_zero true).

Check SFeqb.
Compute SFmax_float 0 100.


Compute Prim2SF 1.25.
Compute Prim2SF (1/0).
Compute Prim2SF (0/0).

Compute SF2Prim (S754_zero true).


Print SF64add.

Print SFeqb.
Print SFcompare.
Check add_spec.
Check compare_spec.

Variable f1 f2 : float.
(* arithmetic operation for abstract numbers is hard *) 
Example f_eq: f1 + f2 = f2 + f1.
  Locate "+".
  Print add.
  Abort.

Example f_eq: Prim2SF (f1 + f2) = Prim2SF (f2 + f1).
  Print add.
  rewrite add_spec.
  Abort.


(*** 2. how to connect them? ***)


(***  3. how to extract code? ***)
Require Import Extraction.

Example ex_f1 : float := 0.2.
Example ex_f2 : float := 0.1 + 0.2.
Example ex_r1 : R := 0.2.
Example ex_r2 : R := 0.1 + 0.2.

Recursive Extraction ex_f1 ex_f2.
Recursive Extraction ex_r2 ex_r2.


