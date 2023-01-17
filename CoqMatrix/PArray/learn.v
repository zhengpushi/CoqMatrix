(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Learn PArray
  author    : ZhengPu Shi
  date      : 2023.01
 *)

(*
  remark    :
  1. A loop need to trace the index of int type, but int is axiomized, 
     havn't a inductive structure, hard to write fixpoint function.
     (1). we can use nat, the structure is easy, but max-size-of-nat is 5000
     (2). we can use Z, it is a bit complicate, and need to solve negative.
     (3). we can use positive, but also complicate.
 *)

Require Import Coq.Numbers.Cyclic.Int63.Uint63. (* native int *)
Require Import PArray.          (* native array *)

Module parray_loop_with_nat.

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
  Compute loop data1 10 0 (Nat.add) 0. (*  = 10 
                                           : nat *)
End parray_loop_with_nat.
