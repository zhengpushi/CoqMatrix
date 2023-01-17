(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : test for Matrix
  author    : ZhengPu Shi
  date      : 2021.12
*)

From FCS Require Import DepPair.Matrix.


(** ** Definitions of matrix module, it is implemented as a Vector 2 *)

Example mat_ex1 : mat 2 3 := [[1;2;3];[4;5;6]].
Example mat_ex2 : mat 2 3 := [[7;8;9];[10;11;12]].
Example mat_ex3 : mat 3 2 := [[1;2];[3;4];[5;6]].


(** ** Construct a matrix with a function *)

Compute mmake 3 2 (fun r c => (S r, S c)).


(** ** Get (ir,rc) element of a matrix *)
 
Compute mnth 99 mat_ex1 0 0.
Compute mnth 99 mat_ex1 0 5.


(** ** Construct a matrix with same element *)

Compute mrepeat 3 2 9.


(** ** Zero matrix *)

Compute @mat0 nat 0 3 2.


(** ** Mapping  matrix to matrix *)

Compute mmap S mat_ex1.


(** ** Mapping two matrices to another matrix *)

Compute mmap2 Nat.add mat_ex1 mat_ex2.


(** ** Construct a matrix with a vector and a a matrix *)

Example vec_ex1 : vec 3 := [1;2;3].
Example vec_ex2 : vec 3 := [4;5;6].
Compute mconsr vec_ex1 mat_ex1.
Compute mconsc vec_ex1 mat_ex3.


(** ** Get head row, tail rows, head column and tail columns of a matrix *)

Compute mhdr mat_ex1.
Compute mtlr mat_ex1.
Compute mhdc mat_ex1.
Compute mtlc mat_ex1.


(** ** Unit matrix *)

Compute mat1 0 1 3.
Compute mat1' 0 1 3.

(** ** Get row of a matrix as a vector *)

Compute mrow 99 0 mat_ex1.
Compute mrow 99 1 mat_ex1.


(** ** Get column of a matrix as a vector *)

Compute mcol 99 0 mat_ex1.
Compute mcol 99 5 mat_ex1.


(** Convert from a vector to a row matrix or column matrix, and convert the 
 matrix back to a vector *)

Compute v2rm vec_ex1.
Compute rm2v (v2rm (vec_ex1)).
Compute v2cm vec_ex1.
Compute cm2v (v2cm (vec_ex1)).


(** ** Append two matrix with same column number or row number *)

Compute mappr mat_ex1 mat_ex2.
Compute mappc mat_ex1 mat_ex2.


(** ** Split a matrix to two parts by row or column *)

Compute (msplitr 1 2 0 mat_ex3).
Compute (msplitr 1 2 0 mat_ex3) : mat 1 2 * mat 2 2.
Compute msplitr' 1 2 0 mat_ex3.

Example msplitr'_ex1 : msplitr' 1 2 0 mat_ex3 = msplitr 1 2 0 mat_ex3.
compute. f_equal. Check (minus_plus 1 2). Abort.

Fail Compute msplitc 2 3 99 [[1;2;3;4;5];[6;7;8;9;10]].
Compute @msplitc nat 2 2 3 99 [[1;2;3;4;5];[6;7;8;9;10]].
Compute msplitc 2 3 99 ([[1;2;3;4;5];[6;7;8;9;10]] : mat 2 5).


(** matrix addition. m1(r,c) + m2(r,c) = m(r,c) *)

Compute madd Nat.add mat_ex1 mat_ex2.


(** matrix substraction. m1(r,c) - m2(r,c) = m(r,c) *)

Compute msub Nat.sub mat_ex1 mat_ex2.


(* constant multiplied to a matrix *)

Compute mcmul Nat.mul 3 mat_ex1.
Compute mmulc Nat.mul mat_ex1 3.


(* Transpose a matrix *)

Compute mtrans mat_ex1.


(** Inner product a vector and a matrix. v(c) *' m(r,c) = v(r) *)

Compute vdotm 0 Nat.add Nat.mul vec_ex1 mat_ex1.


(** Inner product two matrix. m(r1,c) *' (m(r2,c) = m(r1,r2) *)

Compute mdot 0 Nat.add Nat.mul mat_ex1 mat_ex2.
Compute mdot 0 Nat.add Nat.mul mat_ex2 mat_ex1.

Module mdot_test.
  Notation mdot := (mdot 0 Nat.add Nat.mul).
  
  (* (2,3) * (2,2) *)
  Definition matA : mat 3 2 := [[1;2];[3;4];[5;6]].
  Definition matB : mat 2 2 := [[7;8];[9;10]].
  Definition matC : mat 4 2 := [[11;12];[13;14];[15;16];[17;18]].
  
  Definition matAT := mtrans matA.
  Definition matBT := mtrans matB.
  Definition matAB := mdot matA matB.
  Definition matBA := mdot matB matA.
  Definition mat_AB_C := mdot (mdot matA matB) matC.
  Definition mat_A_CBT := mdot matA (mdot matC (mtrans matB)).
  
  (* prop1: mtrans (mdot A B) = mdot B A *)
  Compute matAB.
  Compute matBA.
  Compute mtrans matAB.
  
  (* prop2: mdot (mdot A B) C = mdot A (mdot C (mtrans B)) *)
  Compute mat_AB_C.
  Compute mat_A_CBT.

End mdot_test.


(** matrix multiplication. m1(r,c) * m2(c,t) = m(r,t) *)

Compute mmul 0 Nat.add Nat.mul mat_ex1 mat_ex3. (*
  [[1;2;3];[4;5;6]] * [[1;2];[3;4];[5;6]] = [[22;28];[49;64]]
  (1;2;3)_(1;3;5) = 1 + 6 + 15 = 22
  (1;2;3)_(2;4;6) = 2 + 8 + 18 = 28
  (4;5;6)_(1;3;5) = 4 + 15 + 30 = 49
  (4;5;6)_(2;4;6) = 8 + 20 + 36 = 64 *) 


(** ** Row-vector multiply a matrix, or matrix multiply column-vector. 
  1. v(r) converted to mv(1,r)
  2. v(r) * m(r,c) = mv(1,r) * m(r,c) = m'(1,c) *)

Compute vmulm 0 Nat.add Nat.mul vec_ex1 mat_ex3.
Compute mmulv 0 Nat.add Nat.mul mat_ex1 vec_ex1.


(** Matrix to list list *)


Compute m2l ([[1;2];[3;4];[5;6]] : mat 3 2).
Definition dl : list (list nat) := 
  cons (cons 1 (cons 2 nil))
       (cons (cons 3 (cons 4 nil))
             (cons (cons 5 (cons 6 nil))
                   nil
             )
       ).
Compute l2m 0 dl 3 2.
