(*
  purpose   : Example usage for CoqMatrix library
  author    : ZhengPu Shi
  date      : Feb 28, 2023

  remark    :
  1. library name is coq-matrix, and current version is 1.0.3
  2. logical name is CoqMatrix

 *)

(** Installation CoqMatrix library from OPAM
    $ repo add coq-released https://coq.inria.fr/opam/released
    $ install coq-matrix
*)


(* =========================================================================== *)
(** * Basic usage for matrix *)

(* You should import the matrix library on different element types, such as Nat/Z/Q/Qc/R. *)
From CoqMatrix Require Import MatrixNat.
(* Now, all the types, functions, lemmas, notations are available *)

(* Or, import the vector library on different element types *)
From CoqMatrix Require Import VectorZ.

(* Or, use matrix library on your favorite model *)
From CoqMatrix Require Import MatrixQ.
Import MatrixQ_DL. (* DL/DP/DR/NF/FF/SF *)
(* Now, the matrix model is switched to DepList (DL) *)


(* =========================================================================== *)
(** * Example usage for matrix *)

Reset Initial.

(* import matrix library on Q (rational number) *)
From CoqMatrix Require Import MatrixQ.

(* matrix type *)
Check mat. (* : nat -> nat -> Type *)

(* construct a matrix with a list *)
Example m1 : mat 2 3 := l2m [[1;2;3];[4;5;6]].

(* construct a matrix with a function *)
Example m3 : mat 2 3 :=
  mk_mat
    (fun i j =>
       match i, j with
       | 0%nat, 0%nat => 1
       | 1%nat, 2%nat => 2
       | _, _ => 0
       end).

(** show content *)
Compute (m2l m3). (* = [[1; 0; 0]; [0; 0; 2]] *)



(* construct a matrix with every elements *)
Example m2 : mat 2 2 := mk_mat_2_2 1 2 3 4.

(** transpose a matrix *)
Compute m2l (m2\T).           (* = [[1; 3]; [2; 4]] *)

(** matrix addition *)
Compute m2l (m2 + m2).        (* = [[2; 4]; [6; 8]] *)

(** matrix scalar multiplication *)
Compute m2l (3 c* m2).        (* = [[3; 6]; [9; 12]] *)

(** matrix multiplication *)
Compute m2l (m2 * m2).        (* = [[7; 10]; [15; 22]] *)

(** identity matrix *)
Compute m2l (mat1 3).         (* = [[1; 0; 0]; [0; 1; 0]; [0; 0; 1]] *)


(* =========================================================================== *)
(** * We can develop extra matrix theories on concrete element types *)

(* Go back to the initial state *)
Reset Initial.

(* import matrix library on R *)
From CoqMatrix Require Import MatrixR.

(** Determinate on square matrix of dimension 3×3 *)
Example m1 := mat1 3.
Compute det3 m1.

(* Prove that the determinate of it is 1 *)
Goal det3 m1 = 1.
Proof.
  compute. ring.
Qed.

(** trace *)
Compute trace m1.



(* =========================================================================== *)
(** * Vector theories are also available *)

(* Go back to the initial state *)
Reset Initial.

(* import vector library on Q *)
From CoqMatrix Require Import VectorQ.

(** vector type, it is matrix type actually *)
Check vec.
Print vec.

(** create vector from list *)
Example v1 : vec 3 := l2v [1;2;3].

(** vector arithmetic operations *)
Compute v2l (v1 + v1). (* addition *)
Compute v2l (v1 - v1). (* subtraction *)
Compute v2l (2 c* v1).  (* left scalar multiplication *)
Compute v2l (v1 *c 2).  (* right scalar multiplication *)
Compute vdot v1 v1. (* dot product *)

(** mapping a vector with an unary function *)
Example v2 := vmap v1 (fun a => 2 * (a + 3))%A.
Goal v2 == l2v [8; 10; 12].
Proof.
  lma.
Qed.

(** mapping two vectors with a binary function *)
Example v3 := vmap2 v1 v1 (fun a b => 2 * a - b)%A.
Goal v3 == v1.
Proof.
  lma.
Qed.


(* =========================================================================== *)
(** * We can develop extra vector theories on concrete element types *)

(* Go back to the initial state *)
Reset Initial.

(* import vector library on R *)
From CoqMatrix Require Import VectorR.

(* show this module *)
Print VectorR.

Example v1 : vec 3 := l2v [1;2;3].

(* ****************************************************** *)
(** ** Vector theory on vectors of any dimension *)

(** cross product *)
Compute m2l (vcross3 v1 v1).

(** length (magnitude) of a vector *)
Check vlen v1.

(** normalize a vector to unit vector *)
Check vnormalize v1. (* ToDo: maybe the definition need to modify. *)

(** Predicate: two vectors are parallel *)
Check vparallel v1 v1.

(** Some useful properties about {vcmul,vnonzero,vparallel} *)
(*
Parameter vcmul_vnonzero_neq0_imply_neq0 :
  forall (n : nat) (v : vec n) (k : A),
  vnonzero v -> ~ k c* v == vec0 -> k <> A0.

Parameter vec_eq_vcmul_imply_coef_neq0 :
  forall (n : nat) (v1 v2 : vec n) (k : A),
  vnonzero v1 -> vnonzero v2 -> v1 == k c* v2 -> k <> A0.

Parameter vcmul_nonzero_eq_zero_imply_k0 :
  forall (n : nat) (v : vec n) (k : A),
  vnonzero v -> k c* v == vec0 -> k = 0.

Parameter vcmul_vnonzero_eq_iff_unique_k :
  forall (n : nat) (v : vec n) (k1 k2 : A),
  vnonzero v -> k1 c* v == k2 c* v -> k1 = k2.

Parameter vcmul_vnonzero_eq_self_imply_k1 :
  forall (n : nat) (v : vec n) (k : A), vnonzero v -> k c* v == v -> k = 1.

Parameter vparallel_vnonezero_imply_unique_k :
  forall (n : nat) (v1 v2 : vec n),
  vnonzero v1 ->
  vnonzero v2 -> vparallel v1 v2 -> exists ! k : A, v1 == k c* v2.

Parameter vparallel_iff1 :
  forall (n : nat) (v1 v2 : vec n),
  vnonzero v1 -> vparallel v1 v2 <-> (exists ! k : A, v2 == k c* v1).
*)


(* ****************************************************** *)
(** ** Vector theory on vectors of dimension 3 (we call it vector3) *)

(** dot product on vector3 *)
Compute vdot3 v1 v1.

(** angle between two vector3 *)
Check vangle3 v1 v1.
(* Compute vangle3 v1 v1. (* long expression *) *)


(* =========================================================================== *)
(** * Advanced topic: matrix on function *)

Reset Initial.

From CoqMatrix Require Import MatrixAll.

(** function from A to B *)
Module Fun_Nat_Nat := ElementTypeFun ElementTypeNat ElementTypeNat.
Module Import MatrixFun_Nat_Nat := BasicMatrixTheory Fun_Nat_Nat.
Import DR. (* import a model *)

(* now, A is a sig type, and exactly, it is a function with a proposition.
   This extra porposition is designed to assure that the given function f is 
   proper to Aeq. That is: forall x y : A.I, I.Aeq x y -> O.Aeq (f x) (f y) *)
Compute A.

(* try to construct a single function *)
Example f00 : A.
refine (exist _ S _). cbv. intros. auto. Defined.

(* construct our matrix *)
Example m11 : mat 1 1 := l2m [[f00]].
Example m12 : mat 1 2 := l2m [[f00;f00]].
Compute m2l (m12\T).

