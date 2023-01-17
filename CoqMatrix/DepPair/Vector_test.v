(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : test for Vector
  author    : ZhengPu Shi
  date      : 2021.01
*)

From FCS Require Import DepPair.Vector.


(** ** Definition of vector *)

Example vec_ex0 : @vec nat 0 := tt.
Example vec_ex1 : vec 3 := [1;2;3].
Example vec_ex2 : vec 3 := [4;5;6].


(** ** Construct a vector with same element *)

Compute vrepeat 5 3.


(** ** vec0, its elements is 0 *)

Compute vec0 0 3.


(** ** Get head element *)

Compute vhd 0 vec_ex1.


(** ** Get tail vector *)

Compute vtl vec_ex1.
Compute vtl (vtl vec_ex1).


(** ** Get last element *)

Compute vlast vec_ex1.


(** Construct a vector with a function *)

Compute vmake_old 5 (fun i : nat => i).
Compute vmake 5 (fun i => 3).
Compute vmake 5 (fun i : nat => i).


(** ** Append two vectors *)

Compute vapp vec_ex1 vec_ex2.


(** Get n-th element of a vector *)

Compute vnth 99 2 vec_ex1.
Compute vnth 99 5 vec_ex1.


(** ** Get top k element of a vector *)

Compute vfirstn 99 5 vec_ex1.


(** Get remain (n-k) elements of a vector *)

Compute vskipn 1 vec_ex1.


(** ** Maping a vector to another *)

Compute vmap (S) vec_ex1.


(** Mapping two vectors to another vector *)

Compute vmap2 Nat.add vec_ex1 vec_ex2.


(** ** Vector addition *)

Compute vadd Nat.add vec_ex1 vec_ex1.


(** ** Vector substraction *)

Compute vopp Nat.succ vec_ex1.
Compute vsub Nat.sub vec_ex1 vec_ex1.


(** ** Vector constant multiplication *)

Compute vcmul Nat.mul 3 vec_ex1.
Compute vmulc Nat.mul vec_ex1 3.


(** ** Fold a vector to an element *)

Compute vfoldl Nat.add 0 vec_ex1.
Compute vfoldr Nat.add 0 vec_ex1.


(** ** Dot product of two vectors *)

Compute vdot 0 Nat.add Nat.mul vec_ex1 vec_ex1.


(** ** Concatenation a nested vector to a plain vector *)

Compute vvflat ([[1;2];[3;4];[5;6]] : @vec (vec 2) 3).
