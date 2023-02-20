(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector Theory implemented with SafeNatFun
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. This is safe version of NatFun, which corrected the shape problem
*)


Require Export VectorTheory.
Require Import SafeNatFun.MatrixTheorySF.


(* ######################################################################### *)
(** * Basic vector theory implemented with SafeNatFun *)

Module BasicVectorTheorySF (E : ElementType).

  (* ==================================== *)
  (** ** Also contain matrix theory *)
  Module Export BasicMatrixTheorySF := BasicMatrixTheorySF E.

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
  Definition veq {n} (v1 v2 : vec n) := @meq n 1 v1 v2.
  Infix "==" := veq : vec_scope.

  (** meq is equivalence relation *)
  Lemma veq_equiv : forall n, Equivalence (veq (n:=n)).
  Proof.
    intros. unfold veq. unfold meq.
    (* apply meq_equiv. *)
    (* Qed. *)
    (* Tips: a bit different to other models. *)
  Admitted.

  (** Get element of vector *)
  Definition vnth {n} (v : vec n) i : A := @mnth n 1 v i 0.

  Global Notation "v @ i " := (vnth v i) : vec_scope.

  (** veq and mnth should satisfy this constraint *)
  Lemma veq_iff_vnth : forall {n : nat} (v1 v2 : vec n),
      (v1 == v2) <-> (forall i, i < n -> (vnth v1 i == vnth v2 i)%A).
  Proof.
    intros.
  Admitted.
  

  (* ==================================== *)
  (** ** Convert between list and vector *)
  Definition v2l {n} (v : vec n) : list A := @Matrix.mcol _ n 1 0 v.
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
  Definition t2v_2 (t : @T2 A) : vec 2 :=
    let '(a,b) := t in l2m [[a];[b]].
  Definition t2v_3 (t : @T3 A) : vec 3 :=
    let '(a,b,c) := t in l2m [[a];[b];[c]].
  Definition t2v_4 (t : @T4 A) : vec 4 :=
    let '(a,b,c,d) := t in l2m [[a];[b];[c];[d]].

  Definition v2t_2 (v : vec 2) : @T2 A := (v@0, v@1).
  Definition v2t_3 (v : vec 3) : @T3 A := (v@0, v@1, v@2).
  Definition v2t_4 (v : vec 4) : @T4 A := (v@0, v@1, v@2, v@3).
  
  Lemma v2t_t2v_id_2 : forall (t : A * A), v2t_2 (t2v_2 t) = t.
  Proof.
    intros. destruct t. simpl. unfold v2t_2. f_equal.
  Qed.
  
  Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v.
  Proof.
    intros. apply veq_iff_vnth. intros i Hi. simpl.
    repeat (try destruct i; auto; try lia); easy.
  Qed.
  
  (** mapping of a vector *)
  Definition vmap {n} (v : vec n) f : vec n := mmap f v.
  
  (** folding of a vector *)
(*   Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)
  
  (** mapping of two matrices *)
  Definition vmap2 {n} (v1 v2 : vec n) f : vec n := mmap2 f v1 v2.
  
End BasicVectorTheorySF.

(* Module Test_vnth_notation. *)
(* Module Import M := BasicVectorTheorySF ElementTypeNat. *)
(* Variable r c n : nat. *)
(* Definition v : vec 4 := l2v [1;2;3;4]. *)
  (* Compute v@(v@0). *)
(* End Test_vnth_notation. *)

  
(* ######################################################################### *)
(** * Ring vector theory implemented with SafeNatFun *)

(** zero vector, vector addition, opposition, substraction, scalar multiplication,
    dot product *)
Module RingVectorTheorySF (E : RingElementType) <: RingVectorTheory E.

  (* ==================================== *)
  (** ** Also contain matrix theory *)
  Module Export RingMatrixTheorySF := RingMatrixTheorySF E.

  Export E.
  Include (BasicVectorTheorySF E).

  (** ** Zero vector *)
  Definition vec0 {n} : vec n := mat0 n 1.

  (** Assert that a vector is an zero vector. *)
  Definition vzero {n} (v : vec n) : Prop := v == vec0.

  (** Assert that a vector is an non-zero vector. *)
  Definition vnonzero {n} (v : vec n) : Prop := ~(vzero v).
  
  (** vec0 is equal to mat0 with column 1 *)
  Lemma vec0_eq_mat0 : forall n, vec0 = mat0 n 1.
  Proof.
    intros. easy.
  Qed.
  
  
  (** *** Vector addition *)

  Definition vadd {n} (v1 v2 : vec n) : vec n := @madd n 1 v1 v2.
  Infix "+" := vadd.

  (** v1 + v2 = v2 + v1 *)
  Lemma vadd_comm : forall {n} (v1 v2 : vec n), (v1 + v2) == (v2 + v1).
  Proof.
    intros. apply (@madd_comm n 1).
  Qed.

  (** (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma vadd_assoc : forall {n} (v1 v2 v3 : vec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof.
    intros. apply (@madd_assoc n 1).
  Qed.

  (** vec0 + v = v *)
  Lemma vadd_0_l : forall {n} (v : vec n), vec0 + v == v.
  Proof.
    intros. apply (@madd_0_l n 1).
  Qed.

  (** v + vec0 = v *)
  Lemma vadd_0_r : forall {n} (v : vec n), v + vec0 == v.
  Proof.
    intros. apply (@madd_0_r n 1).
  Qed.

  
  (** *** Vector opposite *)
  
  Definition vopp {n} (v : vec n) : vec n := @mopp n 1 v.
  Notation "- v" := (vopp v).

  (** v + (- v) = vec0 *)
  Lemma vadd_opp : forall {n} (v : vec n), v + (- v) == vec0.
  Proof.
    intros. apply (@madd_opp n 1).
  Qed.
  

  (** *** Vector subtraction *)

  Definition vsub {n} (v1 v2 : vec n) : vec n := v1 + (- v2).
  Infix "-" := vsub.


  (** *** Vector scalar multiplication *)

  Definition vcmul {n} a (v : vec n) : vec n := @mcmul n 1 a v.
  Definition vmulc {n} (v : vec n) a : vec n := @mmulc n 1 v a.
  Infix "c*" := vcmul.
  Infix "*c" := vmulc.

  (** v *c a = a c* v *)
  Lemma vmulc_eq_vcmul : forall {n} a (v : vec n), (v *c a) == (a c* v).
  Proof.
    intros. apply (@mmulc_eq_mcmul n 1).
  Qed.

  (** a c* (b c* v) = (a * b) c* v *)
  Lemma vcmul_assoc : forall {n} a b (v : vec n), a c* (b c* v) == (a * b) c* v.
  Proof.
    intros. apply (@mcmul_assoc n 1).
  Qed.

  (** a c* (b c* v) = b c* (a c* v) *)
  Lemma vcmul_perm : forall {n} a b (v : vec n), a c* (b c* v) == b c* (a c* v).
  Proof.
    intros. apply (@mcmul_perm n 1).
  Qed.

  (** (a + b) c* v = (a c* v) + (b c* v) *)
  Lemma vcmul_add_distr_l : forall {n} a b (v : vec n), 
    (a + b)%A c* v == (a c* v) + (b c* v).
  Proof.
    intros. apply (@mcmul_add_distr_r n 1).
  Qed.

  (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
  Lemma vcmul_add_distr_r : forall {n} a (v1 v2 : vec n), 
    a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof.
    intros. unfold vadd. apply (@mcmul_add_distr_l n 1).
  Qed.

  (** 1 c* v = v *)
  Lemma vcmul_1_l : forall {n} (v : vec n), A1 c* v == v.
  Proof.
    intros. apply (@mcmul_1_l n 1).
  Qed.

  (** 0 c* v = vec0 *)
  Lemma vcmul_0_l : forall {n} (v : vec n), A0 c* v == vec0.
  Proof.
    intros. apply (@mcmul_0_l n 1).
  Qed.
  
  
  (** *** Vector dot product *)
  
  (** dot production of two vectors.
      Here, we use matrix multiplication to do it, and it is a different way to 
      general situation. *)
  Definition vdot {n : nat} (v1 v2 : vec n) :=
    scalar_of_mat (@mmul 1 n 1 (v1\T) v2)%mat.
  
End RingVectorTheorySF.



(* ######################################################################### *)
(** * Decidable-field vector theory implemented with SafeNatFun  *)

Module DecidableFieldVectorTheorySF (E : DecidableFieldElementType)
<: DecidableFieldVectorTheory E.

  (* ==================================== *)
  (** ** Also contain matrix theory *)
  Module Export DecidableFieldMatrixTheorySF := DecidableFieldMatrixTheorySF E.

  Export E.
  Include (RingVectorTheorySF E).

  (** veq is decidable *)
  Lemma veq_dec : forall (n : nat), Decidable (veq (n:=n)).
  Proof. intros. apply meq_dec. Qed.

  Global Existing Instance veq_dec.

  (** It is decidable that if a vector is zero vector. *)
  Lemma vzero_dec : forall {n} (v : vec n), {vzero v} + {vnonzero v}.
  Proof.
    intros. apply veq_dec.
  Qed.
  
End DecidableFieldVectorTheorySF.


(* ######################################################################### *)
(** * Test  *)
Module Test.

  Module Import VectorR := RingVectorTheorySF RingElementTypeR.
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

  Lemma vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : V n) k,
    vnonzero v1 -> vnonzero v2 -> v1 = k c* v2 -> k <> X0.
  Proof.
    intros. intro. subst. rewrite vcmul_0_l in H. destruct H. easy.
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
p
 *)
