(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : vector implemented with abstract array model
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
  1. Motivation:
     We want to get a verifiable and relative high performance representation of 
     vector and matrix in Coq, also including extracted code in OCaml.
     There are several ways:
     
     (1) DepPair, DepList, DepRecOfList
         特点：结构化的数据组织
         优点：
            * 可以在Coq中求值；
            * DepRecOfList抽取到的OCaml代码没有冗余，因对应到了list类型
         缺点：
            * 结构化的方式在处理转置，高斯消元，行列式等需要平等对待行列指标时很低效
            * DepPair, DepList抽取到的OCaml代码有冗余参数
     (2) NatFun, FinFun，FinFunByMC(表示MATHCOMP库中的实现)
         特点：函数式的数据组织
         优点：
            * NatFun和FinFun可以在Coq中求值。
            * 函数的编写和证明都简单很多，使得可以容易的验证复杂算法。
            * FinFun的类型安全性更高，但抽取出的OCaml去掉了依赖类型信息，也降低了安全性。
            * FinFunByMC已实现的理论最多，但需要较高的门槛。
         缺点：
            * 函数式方式在抽取出的OCaml实现在数据访问时效率较低
            * FinFunByMC无法在Coq中求值
     (3) axiomaized bassed on Array
         特点：
            * 公理化实现
            * 越界时无法完成证明，另外也会在OCaml中抛出异常。
         优点：
            * 提取出的OCaml代码直接对应array结构，运行效率高
            * 由于是抽象表示，利用模式匹配也可获得较高的证明自动化程度
         缺点：
            * 无法在Coq中求值
     (4) PArray
         特点：
            * 原生数组的直接支持
            * 提供“默认值”的支持，因此越界时不会引发异常
         优点：
            * 可在Coq中求值，而且效率高
            * 提取出的OCaml代码直接对应array结构，运行效率高
         缺点：
            * PArray没有长度概念，需要额外扩展
            * Uint63.int类型理论不熟悉，常需要与nat类型转换。
            * PArray应该是有4096的限制，我记得大概是这个数值
            * PArray没有将函数转化为数组的原生支持

  2. Several forms of a "vector"
     
     arr -- vec
     | \  / |
     |  \/  |
     |  /\  |
     | /  \ |
     F --- list

     arr : Array.array in OCaml
     vec : vector has given length, made be list
     F : natural-number-indexing-Function
     list : a list of data
     
     These forms have conversion functions between each other, such as:
     a2v <-> v2a,
     v2l <-> l2v,
     l2f <-> f2l,
     f2a <-> a2f, 
     ...
 *)


Require Export TupleExt ListExt Hierarchy Sequence.
Require Export RExt RealFunction.
Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt MyExtrOCamlR.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv Ale Alt Altb Aleb a2r.
Generalizable Variable B Badd Bzero.

(** Control the scope *)
Open Scope R_scope.
Open Scope nat_scope.
Open Scope A_scope.
Open Scope vec_scope.

(** Preserved notations *)
Reserved Infix "==" (at level 70).
Reserved Notation "v .[ i ]"
  (at level 2, left associativity, format "v .[ i ]").
Reserved Notation "v .[ i <- a ]"
  (at level 2, left associativity, format "v .[ i <- a ]").
Reserved Notation "M .[ i , j <- a ]"
  (at level 2, left associativity, format "M .[ i , j <- a ]").


(** * Interface of vector model *)
Module Type VectorModel.
  
  (** ** Basic operations *)

  (* vector type *)
  Parameter vec : forall {A : Type} (n : nat), Type.
  (* equality of two vectors *)
  Parameter veq : forall {A n} (v1 v2 : @vec A n), Prop.
  (* v.[i] *)
  Parameter vget : forall {A n} (v : @vec A n) (i : nat), A.
  (* v.[i<-a] *)
  Parameter vset : forall {A n} (v : @vec A n) (i : nat) (a : A), @vec A n.
  (* [a,a,...] *)
  Parameter vconst : forall {A} n (a : A), @vec A n.
  (* [f 0, f 1, ... ] *)
  Parameter f2v : forall {A} (n : nat) (f : nat -> A), @vec A n.
  
  (** ** controlling extraction *)
  Extract Constant vec "'a" => "'a array".
  Extract Constant vget => "fun _ v -> Array.get v".
  Extract Constant vset => "Array.set".
  Extract Constant vconst => "Array.make".
  Extract Constant f2v => "Array.init".
  (* Recursive Extraction vget vset vconst f2v. *)
  (* Extraction "PVector.ml" vget vset vconst f2v. *)

  (** ** notations for operations *)
  Infix "==" := veq : vec_scope.
  Notation "v .[ i ]" := (vget v i) : vec_scope.
  Notation "v .[ i <- a ]" := (vset v i a) : vec_scope.

  (** ** Specifications of the basic operations *)

  (* Two vector are equal if all corresponding elements are equal *)
  Axiom veq_if : forall {A n} (v1 v2 : @vec A n),
      (forall i, i < n -> v1.[i] = v2.[i]) -> v1 == v2.
  (* Two vector are equal imply all corresponding elements are equal *)
  Axiom veq_imply : forall {A n} (v1 v2 : @vec A n),
      v1 == v2 -> (forall i, i < n -> v1.[i] = v2.[i]).
  
  (* Get element after a update operation with same index return the new value *)
  Axiom vset_eq : forall {A n} (v : @vec A n) (i : nat) (a : A),
      i < n -> (v.[i<-a]).[i] = a.
  (* Get element after a update operation with different index return the old value *)
  Axiom vset_neq : forall {A n} (v : @vec A n) (i j : nat) (a : A),
      i < n -> j < n -> i <> j -> (v.[i<-a]).[j] = v.[j].
  (* Update element with its own value won't change the vector *)
  Axiom vset_same : forall {A n} (v : @vec A n) (i : nat) (a : A),
      i < n -> v.[i<-v.[i]] == v.
  (* Update element twice at same position will only keep last operation *)
  Axiom vset_shadow : forall {A n} (v : @vec A n) (i : nat) (a b : A),
      i < n -> v.[i<-a].[i<-b] == v.[i<-b].
  (* Update element twice at different position can exchange the operation *)
  Axiom vset_permute : forall {A n} (v : @vec A n) (i j : nat) (a b : A),
      i < n -> j < n -> i <> j -> v.[i<-a].[j<-b] == v.[j<-b].[i<-a].

  (* Get element from a constant vector return default value *)
  Axiom vget_vconst : forall {A n} (a : A) (i : nat),
      i < n -> (@vconst _ n a).[i] = a.
  (* Update element of a constant vector with its default value won't change it *)
  Axiom vset_vconst_same : forall {A n} (a : A) (i : nat),
      i < n -> (@vconst _ n a).[i<-a] == (@vconst _ n a).
  
  (* Get element from of a function-generated vector yields its corresponding value *)
  Axiom vget_f2v : forall {A n f} i, i < n -> (@f2v A n f).[i] = f i.
  (* Generate-vector-from-function is injective *)
  Axiom f2v_inj : forall {A} (n : nat) (f g : nat -> A),
      f2v n f == f2v n g -> (forall i, i < n -> f i = g i).
  
End VectorModel.



(* Try to rewrite *)
(* Ltac try_rw := *)
(*   match goal with *)
(*   | [H : ?a = ?b |- ?f ?a _ _ = ?f ?b _ _]     => rewrite H *)
(*   | [H : ?a = ?b |- ?f ?a _ = ?f ?b _]     => rewrite H *)
(*   | [H : ?a = ?b |- ?f ?a = ?f ?b ]     => rewrite H *)
(*   end. *)

(* Do logic works *)
Ltac logic :=
  repeat
    (match goal with
     | [|- _ -> _]              => intros
     | [H : _ /\ _ |- _]         => destruct H
     | [ |- _ /\ _ ]             => split
     | [H : _ |- _ <-> _ ]       => split; intros
     | [H : ?a = ?b |- _ ]      => try progress (rewrite H)
     | [H : ?a <> ?b |- False]       => destruct H
     end;
     auto).


(* Eliminitate nat comparison *)
Ltac nat_cmp :=
  repeat (
      intros;
      let E := fresh "E" in
      try match goal with
        | [ H : context [?i ??= ?j] |- _]  => destruct (i ??= j) as [E|E]
        | [ |- context [?i ??= ?j]]        => destruct (i ??= j) as [E|E]
        | [ H : context [?i ??< ?j] |- _]  => destruct (i ??< j) as [E|E]
        | [ |- context [?i ??< ?j]]        => destruct (i ??< j) as [E|E]
        | [ H : context [?i ??<= ?j] |- _] => destruct (i ??<= j) as [E|E]
        | [ |- context [?i ??<= ?j]]       => destruct (i ??<= j) as [E|E]
        (* `i = j |- _`, use it to rewrite *)
        | [H : ?i = ?j |- _] => match type of i with | nat => try rewrite H in * end
        end;
      auto; try reflexivity; try easy; try lia; try ring).


(** * Vector model by SafeNatFun *)
Module SafeNatFunVectorModel : VectorModel.

  (** ** Basic operations *)
  (* vector type. Note, we cannot simply use `Inductive vec` due to module restriction *)
  Inductive t (A : Type) (n : nat) : Type := mk_vec (f : nat -> A).
  Definition vec (A : Type) (n : nat) : Type := t A n.
  
  (* Automatically convert vector to function *)
  Definition _v2f {A n} (v : @vec A n) : nat -> A := let '(mk_vec _ _ f) := v in f.
  Coercion _v2f : vec >-> Funclass.

  (* equality of two vectors *)
  Definition veq {A n} (v1 v2 : @vec A n) : Prop := forall i, i < n -> v1 i = v2 i.
  
  (* [f 0, f 1, ... ] *)
  Definition f2v {A n} (f : nat -> A) : @vec A n := mk_vec _ _ f.
  
  (* v.[i] *)
  Definition vget {A n} (v : @vec A n) (i : nat) : A := v i.

  (* v.[i<-a] *)
  Definition vset {A n} (v : @vec A n) (i : nat) (a : A) : @vec A n :=
    f2v (fun i0 => if i0 ??= i then a else v i0).
  
  (* [a,a,...] *)
  Definition vconst {A} n (a : A) : @vec A n := f2v (fun _ => a).
  

  (** ** notations for operations *)
  Infix "==" := veq : vec_scope.
  Notation "v .[ i ]" := (vget v i) : vec_scope.
  Notation "v .[ i <- a ]" := (vset v i a) : vec_scope.

  
  (** ** Specifications of the basic operations *)


  (* Two vector are equal if all corresponding elements are equal *)
  Lemma veq_if : forall {A n} (v1 v2 : @vec A n),
      (forall i, i < n -> v1.[i] = v2.[i]) -> v1 == v2.
  Proof. logic. Qed.
  
  (* Two vector are equal imply all corresponding elements are equal *)
  Lemma veq_imply : forall {A n} (v1 v2 : @vec A n),
      v1 == v2 -> (forall i, i < n -> v1.[i] = v2.[i]).
  Proof. logic. Qed.

  (* Get element after a update operation with same index return the new value *)
  Lemma vset_eq : forall {A n} (v : @vec A n) (i : nat) (a : A),
      i < n -> (v.[i<-a]).[i] = a.
  Proof. intros. simpl. nat_cmp. Qed.
  
  (* Get element after a update operation with different index return the old value *)
  Lemma vset_neq : forall {A n} (v : @vec A n) (i j : nat) (a : A),
      i < n -> j < n -> i <> j -> (v.[i<-a]).[j] = v.[j].
  Proof. intros. simpl. nat_cmp. Qed.
  
  (* Update element with its own value won't change the vector *)
  Lemma vset_same : forall {A n} (v : @vec A n) (i : nat) (a : A),
      i < n -> v.[i<-v.[i]] == v.
  Proof. intros. hnf; intros; simpl. nat_cmp. Qed.
  
  (* Update element twice at same position will only keep last operation *)
  Lemma vset_shadow : forall {A n} (v : @vec A n) (i : nat) (a b : A),
      i < n -> v.[i<-a].[i<-b] == v.[i<-b].
  Proof. intros. hnf; intros; simpl. nat_cmp. Qed.
  
  (* Update element twice at different position can exchange the operation *)
  Lemma vset_permute : forall {A n} (v : @vec A n) (i j : nat) (a b : A),
      i < n -> j < n -> i <> j -> v.[i<-a].[j<-b] == v.[j<-b].[i<-a].
  Proof. intros. hnf; intros; simpl. nat_cmp. Qed.

  (* Get element from a constant vector return default value *)
  Lemma vget_vconst : forall {A n} (a : A) (i : nat),
      i < n -> (@vconst _ n a).[i] = a.
  Proof. intros. simpl. nat_cmp. Qed.
  
  (* Update element of a constant vector with its default value won't change it *)
  Lemma vset_vconst_same : forall {A n} (a : A) (i : nat),
      i < n -> (@vconst _ n a).[i<-a] == (@vconst _ n a).
  Proof. intros. hnf; intros; simpl. nat_cmp. Qed.
  
  (* Get element from of a function-generated vector yields its corresponding value *)
  Lemma vget_f2v : forall {A n f} i, i < n -> (@f2v A n f).[i] = f i.
  Proof. intros. simpl. nat_cmp. Qed.
  
  (* Generate-vector-from-function is injective *)
  Lemma f2v_inj : forall {A} (n : nat) (f g : nat -> A),
      @f2v _ n f == f2v g -> (forall i, i < n -> f i = g i).
  Proof. intros. unfold f2v in H. specialize (H i H0). inv H. auto. Qed.
  
End SafeNatFunVectorModel.


(** * Vector theory  *)
Module VectorTheory (E : VectorModel).
  Import E.

  (* ======================================================================= *)
  (** ** demo code for matrix *)

  Definition mat {A} r c := @vec (@vec A c) r.

  (* Note, the set operation efficiency maybe is a bit low, since one row operation *)
  Definition mset {A r c} (M : @mat A r c) (i j : nat) (a : A) : @mat A r c :=
    M.[i<-M.[i].[j<-a]].

  Notation "M .[ i , j <- a ]" := (mset M i j a) : mat_scope.

  (* ======================================================================= *)

  (** ** Cast between two [vec] type with actual equal range *)

  (** Cast from [vec n] type to [vec m] type if [n = m] *)
  Definition cast_vec {A n m} (v : @vec A n) (H: n = m) : @vec A m :=
    @eq_rect_r nat m (fun n0 : nat => vec n0 -> vec m) (fun v0 : vec m => v0) n H v.


  (* ======================================================================= *)
  (** ** Get element of a vector *)

  Notation "a .1" := (a.[0]) : vec_scope.
  Notation "a .2" := (a.[1]) : vec_scope.
  Notation "a .3" := (a.[2]) : vec_scope.
  Notation "a .4" := (a.[3]) : vec_scope.
  Notation "a .x" := (a.[0]) : vec_scope.
  Notation "a .y" := (a.[1]) : vec_scope.
  Notation "a .z" := (a.[2]) : vec_scope.


  (* ======================================================================= *)
  (** ** Equality of vector *)

  (** v1 == v2 <-> forall i, v1.[i] = v2.[i] *)
  Lemma veq_iff : forall {A n} (v1 v2 : @vec A n),
      v1 == v2 <-> (forall i, i < n -> v1.[i] = v2.[i]).
  Proof. intros. split; intros. apply veq_imply; auto. apply veq_if; auto. Qed.
  
  (* Proof equality of two vectors *)
  Ltac veq :=
    repeat
      (logic;
       try
         match goal with
         | [|- ?v1 == ?v2] => apply veq_if; intros
         | [H : ?i < ?n |- ?a.[?i] = ?b.[?i]] => repeat (destruct i; auto; try lia)
         | [H : ?v1 == ?v2 |- ?v1.[?i] = ?v2.[?i]] => apply veq_imply
         end;
       auto; try lia).

  (** The equality of 0-D vector *)
  Lemma v0eq : forall {A} (v1 v2 : @vec A 0), v1 == v2.
  Proof. veq. Qed.

  (** The equality of 1-D vector *)
  Lemma v1eq_iff : forall {A} (v1 v2 : @vec A 1), v1 == v2 <-> v1.1 = v2.1.
  Proof. veq. Qed.

  Lemma v1neq_iff : forall {A} (v1 v2 : @vec A 1), ~(v1 == v2) <-> v1.1 <> v2.1.
  Proof. intros. rewrite v1eq_iff; tauto. Qed.
  
  (** The equality of 2-D vector *)
  Lemma v2eq_iff : forall {A} (v1 v2 : @vec A 2), v1 == v2 <-> v1.1 = v2.1 /\ v1.2 = v2.2.
  Proof. veq. Qed.

  Lemma v2neq_iff : forall {A} (v1 v2 : @vec A 2), ~(v1 == v2) <-> (v1.1 <> v2.1 \/ v1.2 <> v2.2).
  Proof. intros. rewrite v2eq_iff; tauto. Qed.

  (** The equality of 3-D vector *)
  Lemma v3eq_iff : forall {A} (v1 v2 : @vec A 3),
      v1 == v2 <-> v1.1 = v2.1 /\ v1.2 = v2.2 /\ v1.3 = v2.3.
  Proof. veq. Qed.

  Lemma v3neq_iff : forall {A} (v1 v2 : @vec A 3),
      ~(v1 == v2) <-> (v1.1 <> v2.1 \/ v1.2 <> v2.2 \/ v1.3 <> v2.3).
  Proof. intros. rewrite v3eq_iff; tauto. Qed.

  (** The equality of 4-D vector *)
  Lemma v4eq_iff : forall {A} (v1 v2 : @vec A 4),
      v1 == v2 <-> v1.1 = v2.1 /\ v1.2 = v2.2 /\ v1.3 = v2.3 /\ v1.4 = v2.4.
  Proof. veq. Qed.

  Lemma v4neq_iff : forall {A} (v1 v2 : @vec A 4),
      ~(v1 == v2) <-> (v1.1 <> v2.1 \/ v1.2 <> v2.2 \/ v1.3 <> v2.3 \/ v1.4 <> v2.4).
  Proof. intros. rewrite v4eq_iff; tauto. Qed.

  (** ~(v1 == v2) <-> ∃ i, u $ i <> v $ i *)
  Lemma vneq_iff_exist_nth_neq : forall {A n} (v1 v2 : @vec A n),
      ~(v1 == v2) <-> exists i, i < n /\ v1.[i] <> v2.[i].
  Proof.
    intros. logic.
    - rewrite veq_iff in H.
      apply not_all_ex_not in H. destruct H as [n0 H]. exists n0. tauto.
    - rewrite veq_iff. destruct H as [i H].
      intro. specialize (H0 i). tauto.
  Qed.


  (* ======================================================================= *)
  (** ** Vector with same elements *)
  Section vrepeat.
    Context {A} {Azero : A} {n : nat}.

    Definition vrepeat (a : A) : @vec A n := vconst n a.

    (** (repeat a).i = a *)
    Lemma nth_vrepeat : forall a i, i < n -> (vrepeat a).[i] = a.
    Proof. intros. unfold vrepeat. rewrite vget_vconst; auto. Qed.
  End vrepeat.
End VectorTheory.

Module V := (VectorTheory VectorModel).
Extraction "VectoryTheory.ml" VectorTheory.
Recursive Extraction VectorTheory.

(* ======================================================================= *)
(** ** Zero vector *)
Section vzero.
  Context {A} (Azero : A) {n : nat}.
  
  Definition vzero : @vec A n := vrepeat Azero.

  (** vzero.i = 0 *)
  Lemma nth_vzero : forall i, i < n -> vzero.[i] = Azero.
  Proof. intros. apply nth_vrepeat; auto. Qed.
  
End vzero.

