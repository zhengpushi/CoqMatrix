(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : vector implemented with PArray model
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :

 *)

Require Export TupleExt ListExt Hierarchy Sequence.
Require Export PArray.
Import PArrayNotations.
Require Export RExt RealFunction.
Require Import Extraction.
Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOCamlInt63.
Require Import MyExtrOCamlPArray.
Require Import MyExtrOCamlR.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv Ale Alt Altb Aleb a2r.
Generalizable Variable B Badd Bzero.

(** Control the scope *)
Open Scope R_scope.
Open Scope nat_scope.
Open Scope A_scope.
Open Scope vec_scope.

(* ======================================================================= *)
(** ** Definition of vector type [vec] *)

(* nat to int *)
Definition nat2int (i : nat) : PrimInt63.int := Uint63.of_Z (Z.of_nat i).
Coercion nat2int : nat >-> PrimInt63.int.

(* n-vector based on PArray *)
Inductive vec {A : Type} (n : nat) := Vec (a : array A).

(* vector to array *)
Definition v2a {A n} (v : @vec A n) : array A := let '(Vec _ a) := v in a.

(* make a vector *)
Definition vmake {A} (n : nat) (a : A) : @vec A n := Vec _ (make n a).

(* get element *)
Definition vget {A n} (v : @vec A n) (i : nat) : A := (v2a v).[i].

(* set element *)
Definition vset {A n} (v : @vec A n) (i : nat) (a : A) : @vec A n :=
  Vec _ ((v2a v).[i <- a]).


(* function to vector *)
(* 注：该函数缺乏原生支持，需要递归来实现 *)
Definition f2v {A} n (f : nat -> A) : @vec A n :=
  let a0 : array A := make n (f 0) in
  let wt (a : array A) (ix : nat * A) := let (i,x) := ix in set a i x in
  let a1 : array A := seqfoldl (fun i => (i, f i)) n a0 wt in
  Vec _ a1.

(* Compute f2v 100 (fun i => i). *)
(* Time Compute f2v 1000 (fun i => i). (* 2.2s, too slow *) *)

(** 检查PArray对证明的支持 *)
Section proof_test.
  Variable A : Type.
  Variable a b c : A.

  (* 一个给定维度的具体向量，可通过计算直接得证 *)
  (* [a;a] = ([a,a] <- 0,b <- 0,a) *)
  Goal (vmake 2 a) = vset (vset (vmake 2 a) 0 b) 0 a.
  Proof. cbv. auto. Qed.
  
  (* 越界时仍然可以获得“安全的值”，不会引发“异常” *)
  Compute vget (vmake 2 a) 5.

  (* 但“默认值”的设计，也许会是安全隐患。因为下面的命题可以得证 *)
  Goal vset (vmake 2 a) 5 b = vmake 2 a.
  Proof. cbv. auto. Qed.
  (* 上述命题，语义上讲，左侧含有越界操作，应当触发异常，不应该简单的等同于右侧 *)

  (* 任意维度时，就不能通过计算来证明了，需要使用性质来验证 *)
  Goal forall n i, i < n -> vmake n a = vset (vmake n a) i a.
  Proof.
    intros. unfold vset, vmake, v2a.
    f_equal.
    apply array_ext; simpl; auto.
    - rewrite length_set. auto.
    - intros. rewrite get_make.
      destruct (Uint63.eq_dec i i0).
      + subst. rewrite get_set_same; auto.
      + rewrite get_set_other; auto. rewrite get_make. auto.
    - rewrite default_set. auto.
  Qed.
End proof_test.

(* ======================================================================= *)
(** ** Get element of a vector *)

Notation "a .1" := ((v2a a).[0]) : vec_scope.
Notation "a .2" := ((v2a a).[1]) : vec_scope.
Notation "a .3" := ((v2a a).[2]) : vec_scope.
Notation "a .4" := ((v2a a).[3]) : vec_scope.
Notation "a .x" := ((v2a a).[0]) : vec_scope.
Notation "a .y" := ((v2a a).[1]) : vec_scope.
Notation "a .z" := ((v2a a).[2]) : vec_scope.


(* 遗憾的是，抽取OCaml时有一些问题，比如 Uint63, PArray 的OCaml支持是缺失的 *)
Recursive Extraction vmake vget vset.
Extraction "PVector_byPArray.ml" vmake vget vset.

