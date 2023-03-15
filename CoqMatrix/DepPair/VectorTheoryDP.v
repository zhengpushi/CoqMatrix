(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector Theory implemented with DepPair
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
*)

Require Export VectorTheory.
Require Import DepPair.MatrixTheoryDP.


(* ######################################################################### *)
(** * Basic vector theory implemented with DepList *)

Module BasicVectorTheoryDP (E : ElementType).

  (* ==================================== *)
  (** ** Also contain matrix theory *)
  Module Export BasicMatrixTheoryDP := BasicMatrixTheoryDP E.

  (* ==================================== *)
  (** ** Vector element type *)
  Export E.

  Infix "==" := (eqlistA Aeq) : list_scope.

  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope vec_scope.
  
  (* ==================================== *)
  (** ** Vector type *)
  
  Definition vec n := mat n 1.

  (** matrix equality *)
  Definition veq {n} (v1 v2 : vec n) := meq v1 v2.
  Infix "==" := veq : vec_scope.

  (** meq is equivalence relation *)
  Lemma veq_equiv : forall n, Equivalence (veq (n:=n)).
  Proof.
    intros. apply meq_equiv.
  Qed.
  

  (** Get element of vector *)
  Definition vnth {n} (v : vec n) i : A := @mnth n 1 v i 0.
  
(*   Notation "v .[ i ]" := (vnth v i) (at level 30) : vec_scope. *)
  (* Notation "v . [ i ]" := (vnth i v) (at level 30). *)

  (** veq and mnth should satisfy this constraint *)
  Lemma veq_iff_vnth : forall {n : nat} (v1 v2 : vec n),
      (v1 == v2) <-> (forall i, i < n -> (vnth v1 i == vnth v2 i)%A).
  Proof.
    intros.
  Admitted.
  

  (* ==================================== *)
  (** ** Convert between list and vector *)
  Definition v2l {n} (v : vec n) : list A := hdc A0 (m2l v).
  (* Definition v2l' {n} (v : vec n) : list A := to_list (mcoli v F1). *)
  
  Definition l2v {n} (l : list A) : vec n := l2m (row2col l).
  
  Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
  Admitted.
  
  Lemma v2l_l2v_id : forall {n} (l : list A),
    length l = n -> (@v2l n (@l2v n l) == l)%list.
  Admitted.

  Lemma l2v_v2l_id : forall {n} (v : vec n), l2v (v2l v) == v.
  Admitted.
  
  (* ==================================== *)
  (** ** Convert between tuples and vector *)
  Definition t2v_2 (t : @T2 A) : vec 2 := let '(a,b) := t in l2v [a;b].
  Definition t2v_3 (t : @T3 A) : vec 3 := let '(a,b,c) := t in l2v [a;b;c].
  Definition t2v_4 (t : @T4 A) : vec 4 := let '(a,b,c,d) := t in l2v [a;b;c;d].

  Definition v2t_2 (v : vec 2) : @T2 A.
    destruct v as (a1, (a2, _)).
    destruct a1 as (a11,_), a2 as (a21,_).
    apply (a11,a21).
  Defined.

  Definition v2t_3 (v : vec 3) : @T3 A.
    destruct v as (a1, (a2, (a3, _))).
    destruct a1 as (a11,_), a2 as (a21,_), a3 as (a31,_).
    apply (a11,a21,a31).
  Defined.
    
  Definition v2t_4 (v : vec 4) : @T4 A.
    destruct v as (a1, (a2, (a3, (a4, _)))).
    destruct a1 as (a11,_), a2 as (a21,_), a3 as (a31,_), a4 as (a41,_).
    apply (a11,a21,a31,a41).
  Defined.
  
  Lemma v2t_t2v_id_2 : forall (t : A * A), v2t_2 (t2v_2 t) = t.
  Proof.
    intros. destruct t. simpl. unfold v2t_2. f_equal.
  Qed.
  
  Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v.
  Proof.
    intros.
    repeat match goal with
    | v : vec _ |- _ => destruct v
    | v : Vector.vec _ |- _ => destruct v
    end.
    easy.
  Qed.
  
  (** mapping of a vector *)
  Definition vmap {n} (v : vec n) f : vec n := mmap f v.
  
  (** folding of a vector *)
(*   Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)
  
  (** mapping of two matrices *)
  Definition vmap2 {n} (v1 v2 : vec n) f : vec n := mmap2 f v1 v2.
  
End BasicVectorTheoryDP.


(* ######################################################################### *)
(** * Ring vector theory implemented with DepList  *)

(** zero vector, vector addition, opposition, substraction, scalar multiplication,
    dot product *)
Module RingVectorTheoryDP (E : RingElementType) <: RingVectorTheory E.

  (* ==================================== *)
  (** ** Also contain matrix theory *)
  Module Export RingMatrixTheoryDP := RingMatrixTheoryDP E.

  Export E.
  Include (BasicVectorTheoryDP E).

  (** ** Zero vector *)
  Definition vec0 {n} : vec n := mat0 n 1.

  (* (** Assert that a vector is an zero vector. *) *)
  (* Definition vzero {n} (v : vec n) : Prop := v = vec0. *)

  (* (** Assert that a vector is an non-zero vector. *) *)
  (* Definition vnonzero {n} (v : vec n) : Prop := ~(vzero v). *)
  
  (* (** vec0 is equal to mat0 with column 1 *) *)
  (* Lemma vec0_eq_mat0 : forall n, vec0 = mat0 n 1. *)
  (* Proof. *)
  (*   intros. easy. *)
  (* Qed. *)

  (* (** It is decidable that if a vector is zero vector. *) *)
  (* Lemma vzero_dec : forall {n} (v : vec n), {vzero v} + {vnonzero v}. *)
  (* Proof. *)
  (*   intros. apply meq_dec. *)
  (* Qed. *)
  
  
  (** *** Vector addition *)

  Definition vadd {n} (v1 v2 : vec n) : vec n := madd v1 v2.
  Infix "+" := vadd.

  (** v1 + v2 = v2 + v1 *)
  Lemma vadd_comm : forall {n} (v1 v2 : vec n), (v1 + v2) == (v2 + v1).
  Proof.
    intros. apply madd_comm.
  Qed.

  (** (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma vadd_assoc : forall {n} (v1 v2 v3 : vec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof.
    intros. apply madd_assoc.
  Qed.

  (** vec0 + v = v *)
  Lemma vadd_0_l : forall {n} (v : vec n), vec0 + v == v.
  Proof.
    intros. apply madd_0_l.
  Qed.

  (** v + vec0 = v *)
  Lemma vadd_0_r : forall {n} (v : vec n), v + vec0 == v.
  Proof.
    intros. apply madd_0_r.
  Qed.

  
  (** *** Vector opposite *)
  
  Definition vopp {n} (v : vec n) : vec n := mopp v.
  Notation "- v" := (vopp v).

  (** v + (- v) = vec0 *)
  Lemma vadd_opp_r : forall {n} (v : vec n), v + (- v) == vec0.
  Proof.
    intros. apply madd_opp.
  Qed.

  (** (- v) + v = vec0 *)
  Lemma vadd_opp_l : forall {n} (v : vec n), (- v) + v == vec0.
  Proof.
    intros. rewrite vadd_comm. apply madd_opp.
  Qed.
  

  (** *** Vector subtraction *)

  Definition vsub {n} (v1 v2 : vec n) : vec n := v1 + (- v2).
  Infix "-" := vsub.


  (** *** Vector scalar multiplication *)

  Definition vcmul {n} a (v : vec n) : vec n := a c* v.
  Definition vmulc {n} (v : vec n) a : vec n := v *c a.

  (** v *c a = a c* v *)
  Lemma vmulc_eq_vcmul : forall {n} a (v : vec n), v *c a == a c* v.
  Proof.
    intros. apply mmulc_eq_mcmul.
  Qed.

  (** a c* (b c* v) = (a * b) c* v *)
  Lemma vcmul_assoc : forall {n} a b (v : vec n), a c* (b c* v) == (a * b) c* v.
  Proof.
    intros. apply mcmul_assoc.
  Qed.

  (** a c* (b c* v) = b c* (a c* v) *)
  Lemma vcmul_perm : forall {n} a b (v : vec n), a c* (b c* v) == b c* (a c* v).
  Proof.
    intros. apply mcmul_perm.
  Qed.

  (** (a + b) c* v = (a c* v) + (b c* v) *)
  Lemma vcmul_add_distr_l : forall {n} a b (v : vec n), 
    (a + b)%A c* v == (a c* v) + (b c* v).
  Proof.
    intros. apply mcmul_add_distr_r.
  Qed.

  (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
  Lemma vcmul_add_distr_r : forall {n} a (v1 v2 : vec n), 
    a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof.
    intros. unfold vadd. apply mcmul_add_distr_l.
  Qed.

  (** 1 c* v = v *)
  Lemma vcmul_1_l : forall {n} (v : vec n), A1 c* v == v.
  Proof.
    intros. apply mcmul_1_l.
  Qed.

  (** 0 c* v = vec0 *)
  Lemma vcmul_0_l : forall {n} (v : vec n), A0 c* v == vec0.
  Proof.
    intros. apply mcmul_0_l.
  Qed.
  
  
  (** *** Vector dot product *)
  
  (** dot production of two vectors.
      Here, we use matrix multiplication to do it, and it is a different way to 
      general situation. *)
  Definition vdot {n : nat} (v1 v2 : vec n) :=
    scalar_of_mat (v1\T * v2)%mat.
  
End RingVectorTheoryDP.


(* ######################################################################### *)
(** * Decidable-field vector theory implemented with DepPair  *)

Module DecidableFieldVectorTheoryDP (E : DecidableFieldElementType)
<: DecidableFieldVectorTheory E.

  (* ==================================== *)
  (** ** Also contain matrix theory *)
  Module Export DecidableFieldMatrixTheoryDP := DecidableFieldMatrixTheoryDP E.

  Export E.
  Include (RingVectorTheoryDP E).

  (** veq is decidable *)
  Lemma veq_dec : forall (n : nat), Decidable (veq (n:=n)).
  Proof. intros. apply meq_dec. Qed.

End DecidableFieldVectorTheoryDP.


(* ######################################################################### *)
(** * Test  *)
Module Test.

  Module Import VectorR := RingVectorTheoryDP RingElementTypeR.
  Import Reals.
  Open Scope R.
  
  Definition v1 := @l2v 3 [1;2;3].
  Definition v2 := @l2v 3 [4;5;6].
  Example vdot_ex1 : vdot v1 v2 = (4+10+18)%R.
  Proof.
    compute. ring.
  Qed.
  
End Test.


(** ** Others, later ... *)

(*
  (* ==================================== *)
  (** ** Vector equility *)
  Lemma veq_dec : forall {n} (v1 v2 : V n), {v1 = v2} + {v1 <> v2}.
  Proof.
    intros. apply meq_dec.
  Qed.

  
  (* ==================================== *)
  (** ** 2-dim vector operations *)

  Definition vlen2 (v : V 2) : X :=
    let '(x,y) := v2t_2 v in
      (x * x + y * y)%X.
  
  (* ==================================== *)
  (** ** 3-dim vector operations *)

  Definition vlen3 (v : V 3) : X :=
    let '(x,y,z) := v2t_3 v in
      (x * x + y * y + z * z)%X.
      
  Definition vdot3 (v0 v1 : V 3) : X :=
    let '(a0,b0,c0) := v2t_3 v0 in
    let '(a1,b1,c1) := v2t_3 v1 in
      (a0 * a1 + b0 * b1 + c0 * c1)%X.
 *)
 
