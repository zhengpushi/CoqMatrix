(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Test for matrix implemented with Dependent List
  author    : ZhengPu Shi
  date      : 2021.12
*)

From FCS Require Import DepList.Matrix.
Import VectorNotations.


(** Fin *)
Check F1 : fin 10.
Check F1 : fin 2.     (* F1 has type: fin (S ?n) *)
Check FS F1 : fin 3.
Check FS F1 : fin 2.

(** vec *)
Example vec_ex0 : @vec nat 0 := vnil.
Example vec_ex1 : vec 3 := [1;2;3].
Example vec_ex2 : vec 3 := [4;5;6].

(** vconst *)
Compute vconst 1 5.

(** fin_gen *)
Compute fin_gen 0 0.
Compute fin_gen 3 0.
Compute fin_gen 3 1.
Compute fin_gen 3 2.
Compute fin_gen 3 3.

(** mat *)
Example mat_ex1 : mat 2 3 := [[1;2;3];[4;5;6]].
Example mat_ex2 : mat 2 3 := [[7;8;9];[10;11;12]].
Example mat_ex3 : mat 3 2 := [[1;2];[3;4];[5;6]].

(** transpoes *)
Compute mtrans mat_ex1.

(** Comparison of vfoldl, vfoldr, vfoldlrev *)
Module Cmp_diff_method_of_vfold.

  Example v := [1;2;3;4].
  
  Compute vfoldl Nat.add 0 v.
  Print fold_left.
  (* Fold from first element, execute f in every recursion step *)
  (* vfoldl add 0 [1;2;3;4]
    = vfoldl add (add 0 1) [2;3;4] => vfoldl add 1 [2;3;4]
    = vfoldl add (add 1 2) [3;4] => vfoldl add 3 [3;4]
    = vfoldl add (add 3 3) [4] => vfoldl add 6 [4]
    = vfoldl add (add 6 4) [] = vfoldl add 10 []
    = 10
  *)
  
  Compute vfoldr Nat.add v 0.
  Print fold_right.
  (* Fold from last element, push operand to stack, then execute f when popping *)
  (* vfoldr add [1;2;3;4] 0
    = add 1 (vfoldr add [2;3;4] 0)
    = add 1 (add 2 (vfoldr add [3;4] 0))
    = add 1 (add 2 (add 3 (vfoldr add [4] 0)))
    = add 1 (add 2 (add 3 (add 4 (vfoldr add [] 0))))
    = add 1 (add 2 (add 3 (add 4 0)))
    = add 1 (add 2 (add 3 4))
    = add 1 (add 2 7)
    = add 1 9
    = 10
  *)
  
  Compute vfoldlrev Nat.add 0 v.
  Print vfoldlrev.
  (* Fold from first element, push operand to stack, then execute f when popping *)
  (* vfoldlrev add 0 [1;2;3;4].
    = add (vfoldlrev 0 [2;3;4]) 1
    = add (add (vfoldlrev 0 [3;4]) 2) 1
    = add (add (add (vfoldlrev 0 [4]) 3) 2) 1
    = add (add (add (add (vfoldlrev 0 []) 4) 3) 2) 1
    = add (add (add (add 0 4) 3) 2) 1
    = add (add (add 4 3) 2) 1
    = add (add 7 2) 1
    = add 9 1
    = 10
  *)

End Cmp_diff_method_of_vfold.


(** ** sum of vector *)
Compute sum 0 Nat.add [1;2;3].
Compute sum (vconst 0 3) (fun v1 v2 => vadd Nat.add v1 v2)
  [[1;2;3];[4;5;6]]. 
Compute sum 0 Nat.add (sum (vconst 0 3) (fun v1 v2 => vadd Nat.add v1 v2)
  [[1;2;3];[4;5;6]]).


(** ** sum of matrix *)
Compute sumsum 0 Nat.add [[1;2;3];[4;5;6]].


(** vnth, vdot, vmake *)

Example ex_vec1 : vec 1 := [1].
(* Example ex_vec1' : vec 1 := [R0]. *)

Example ex_vec3 : vec 3 := [1;2;3].
Print ex_vec3.

Fail Compute vnth vnil F1.
Compute vnth ex_vec3 (F1).

Example ex_vec3' : vec 3 := Eval compute in vopp Nat.succ ex_vec3.
Print ex_vec3'.

Example ex_vec3'' : vec 3 := Eval compute in vadd Nat.add ex_vec3 ex_vec3'.
Print ex_vec3''.

Compute vdot 0 Nat.add Nat.mul ex_vec3 ex_vec3.

Definition vmake_fun1 n : fin n -> nat := fun (fn : fin n) => n.
Compute (@vmake_fun1 3 F1).
Compute (@vmake_fun1 3 (FS F1)).
Compute vmake (@vmake_fun1 3).


(** ** matrix multiplication *)
Example ex_mat22 : mat 2 2 := [[1;2];[3;4]].
Example ex_mat22' : mat 2 2 := [[true;false];[false;true]].
Example ex_mat33 : mat 3 3 := [[1;2;3];[4;5;6];[7;8;9]].
Example ex_mat33' := mtrans ex_mat33. Print ex_mat33'.
Example ex_mat33'' := Eval compute in (mtrans ex_mat33). Print ex_mat33''.
  
Compute mrowi ex_mat22 (FS F1).
Compute mnth ex_mat22 F1 (FS F1).


(** vector to list *)
Check ([1;2;3] : vec 3).
Compute v2l ([1;2;3] : vec 3).
Compute l2v 0 (List.cons 1 (List.cons 2 List.nil)) 2.

(** Matrix to list list *)
Compute m2l ([[1;2];[3;4];[5;6]] : mat 3 2).

(** list to matrix *)
Require Import List.
Import ListNotations.
Definition dl : list (list nat) := [[1;2];[3;4];[5;6]]%list.
Compute l2m 0 dl 3 2.


(** OCaml code extraction *)
Recursive Extraction ex_mat22 mtrans mmul.
Extraction "test.ml" ex_mat22 mtrans mmul.


(* =============================================================== *)
(** matrix multiplication (from CoLoR) *)
Import MatMultCoLoR.

(* these functions looks weill *)
Recursive Extraction fin vmake.
Recursive Extraction mat_build. 

(* there are magic code, but still could be used *)
Recursive Extraction mmul.
Recursive Extraction mat_mult.

Extract Inductive list => "list" [ "[]" "(::)" ].
(* Extract Inductive nat => int [ "0" "succ" ] 
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))". *)

Open Scope vector_scope.
Example v2 : vec 2 := [1;2].
Example f1 : fin 1 := F1.
Example f2_1 : fin 2 := F1.
Example f2_2 : fin 2 := FS F1.
Example f3 : fin 3 := FS F1.
Fail Example f2_3 : fin 2 := FS (FS F1).
Compute vnth v2 f2_1.
Fail Compute vnth v2 f3.

Extraction "mat1.ml" mat_build_spec mat_build mat_mult
  ex_vec1 ex_vec3 ex_mat22 ex_mat33 
  of_list to_list
  v2 f1 f2_1 f2_2 f3.

Recursive Extraction   Vector.t Fin.t of_list to_list vnth vadd v2.
Extraction "mat2.ml" Vector.t Fin.t of_list to_list vnth vadd v2.
