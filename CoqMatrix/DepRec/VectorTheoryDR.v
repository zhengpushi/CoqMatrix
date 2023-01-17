(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector Theory implemented with DepRec
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
*)

Require Export VectorTheory.
Require Import DepRec.MatrixTheoryDR.

(* ######################################################################### *)
(** * Basic vector theory implemented with DepRec *)

Module BasicVectorTheoryDR (E : ElementType).

  (* ==================================== *)
  (** ** Matrix theory *)
  Module Import BasicMatrixTheoryDR := BasicMatrixTheoryDR E.

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

  (** veq and mnth should satisfy this constraint *)
  Lemma veq_iff_vnth : forall {n : nat} (v1 v2 : vec n),
      (v1 == v2) <-> (forall i, i < n -> (vnth v1 i == vnth v2 i)%A).
  Proof.
    intros. split; intros; try apply meq_iff_mnth; auto.
  Admitted.
  
  (* ==================================== *)
  (** ** Convert between list and vector *)

  Definition v2l {n} (v : vec n) : list A := hdc A0 (m2l v).

  Definition l2v {n} (l : list A) : vec n := l2m (row2col l).
  
  Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
  Proof.
    intros. unfold v2l.
    rewrite hdc_length. destruct v. simpl. auto.
  Qed.
  
  Lemma v2l_l2v_id : forall {n} (l : list A),
    length l = n -> (@v2l n (@l2v n l) == l)%list.
  Proof.
    intros. unfold v2l,l2v. simpl.
    (* rewrite m2l_l2m_id.  unfold v2l,l2v. simpl. *)
  Admitted.
  
  Lemma l2v_v2l_id : forall {n} (v : vec n), 
    l2v (v2l v) == v.
  Proof.
    intros. unfold v2l,l2v. simpl.
  Admitted.
  
  (* ==================================== *)
  (** ** Convert between tuples and vector *)
  Definition t2v_2 t := let '(a,b) := t in @l2m 2 1 [[a];[b]].
  Definition t2v_3 t := let '(a,b,c) := t in @l2m 3 1 [[a];[b];[c]].
  Definition t2v_4 t := let '(a,b,c,d) := t in @l2m 4 1 [[a];[b];[c];[d]].
  
  Definition v2t_2 v := let d := @m2l 2 1 v in (
    hd A0 (hd [] d), 
    hd A0 (hd [] (tl d))
    ).
    
  Definition v2t_3 v := let d := @m2l 3 1 v in (
    hd A0 (hd [] d), 
    hd A0 (hd [] (tl d)), 
    hd A0 (hd [] (tl (tl d)))
    ).
    
  Definition v2t_4 v := let d := @m2l 4 1 v in (
    hd A0 (hd [] d), 
    hd A0 (hd [] (tl d)), 
    hd A0 (hd [] (tl (tl d))), 
    hd A0 (hd [] (tl (tl (tl d))))
    ).
  
  Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v.
  Proof.
    intros. unfold t2v_2,v2t_2.
  (*   rewrite <- l2m_m2l_id. apply meq_iff. simpl. *)
  (*   repeat (try f_equal; auto). *)
    (* Qed. *)
  Admitted.
  
  Lemma v2t_t2v_id_2 : forall (t : A * A), v2t_2 (t2v_2 t) = t.
  Proof.
    intros. destruct t. simpl. unfold v2t_2. f_equal.
  Qed.
  
  (** Mapping of a vector *)
  Definition vmap {n} (v : vec n) f : vec n := mmap f v.
  
  (** Folding of a vector *)
(*   Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)
  
  (** Mapping of two vectors *)
  Definition vmap2 {n} (v1 v2 : vec n) f : vec n := mmap2 f v1 v2.

End BasicVectorTheoryDR.


(* ######################################################################### *)
(** * Ring vector theory implemented with DepRec  *)

(** zero vector, vector addition, opposition, substraction, scalar multiplication,
    dot product *)
Module RingVectorTheoryDR (E : RingElementType) <: BasicVectorTheory E.

  (* ==================================== *)
  (** ** Matrix theory *)
  
  Module Import RingMatrixTheoryDR := RingMatrixTheoryDR E.

  Export E.
  Include (BasicVectorTheoryDR E).

  (** ** Zero vector *)
  Definition vec0 {n} : vec n := mat0 n 1.

  (* (** Assert that a vector is an zero vector. *) *)
  (* Definition vzero {n} (v : vec n) : Prop := v = vec0. *)

  (* (** Assert that a vector is an non-zero vector. *) *)
  (* Definition vnonzero {n} (v : vec n) : Prop := ~(vzero v). *)
  
  (* (** vec0 is equal to mat0 with column 1 *) *)
  (* Lemma vec0_eq_mat0 : forall n, vec0 = mat0 n 1. *)
  (* Proof. *)
  (*   intros. apply meq_iff. auto. *)
  (* Qed. *)

  (* (** It is decidable that if a vector is zero vector. *) *)
  (* Lemma vzero_dec : forall {n} (v : vec n), {vzero v} + {vnonzero v}. *)
  (* Proof. *)
  (*   intros. apply meq_dec. *)
  (* Qed. *)
  
  (** *** Vector addition *)

  Definition vadd {n} (v1 v2 : vec n) : vec n := (v1 + v2)%mat.
  Infix "+" := vadd : vec_scope.

  Lemma vadd_comm : forall {n} (v1 v2 : vec n), v1 + v2 == v2 + v1.
  Proof.
    intros. apply madd_comm.
  Qed.

  Lemma vadd_assoc : forall {n} (v1 v2 v3 : vec n), 
    (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof.
    intros. apply madd_assoc.
  Qed.

  Lemma vadd_0_l : forall {n} (v : vec n), vec0 + v ==  v.
  Proof.
    intros. apply madd_0_l.
  Qed.

  Lemma vadd_0_r : forall {n} (v : vec n), v + vec0 == v.
  Proof.
    intros. apply madd_0_r.
  Qed.

  
  (** *** Vector opposite *)
  
  Definition vopp {n} (v : vec n) : vec n := (-v)%mat.
  Notation "- v" := (vopp v) : vec_scope.

  Lemma vadd_opp : forall {n} (v : vec n), v + (- v) == vec0.
  Proof.
    intros. apply madd_opp.
  Qed.
  

  (** *** Vector subtraction *)

  Definition vsub {n} (v1 v2 : vec n) : vec n := (v1 - v2)%mat.
  Infix "-" := vsub : vec_scope.

  
  (** *** Vector scalar multiplication *)

  Definition vcmul {n} a (v : vec n) : vec n := a c* v.
  Definition vmulc {n} (v : vec n) a : vec n := v *c a.

  Lemma vmulc_eq_vcmul : forall {n} a (v : vec n), v *c a == a c* v.
  Proof.
    intros. apply mmulc_eq_mcmul.
  Qed.

  Lemma vcmul_assoc : forall {n} a b (v : vec n), a c* (b c* v) == (a * b) c* v.
  Proof.
    intros. apply mcmul_assoc.
  Qed.

  Lemma vcmul_perm : forall {n} a b (v : vec n), a c* (b c* v) == b c* (a c* v).
  Proof.
    intros. apply mcmul_perm.
  Qed.

  Lemma vcmul_add_distr_l : forall {n} a b (v : vec n), 
    (a + b)%A c* v == (a c* v) + (b c* v).
  Proof.
    intros. apply mcmul_add_distr_r.
  Qed.

  Lemma vcmul_add_distr_r : forall {n} a (v1 v2 : vec n), 
    a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof.
    intros. apply mcmul_add_distr_l.
  Qed.

  Lemma vcmul_1_l : forall {n} (v : vec n), A1 c* v == v.
  Proof.
    intros. apply mcmul_1_l.
  Qed.

  Lemma vcmul_0_l : forall {n} (v : vec n), A0 c* v == vec0.
  Proof.
    intros. apply mcmul_0_l.
  Qed.

  
  (** *** Vector dot product *)
  
  Definition vdot {n : nat} (v1 v2 : vec n) := scalar_of_mat (v1\T * v2)%mat.
  
End RingVectorTheoryDR.


(* ######################################################################### *)
(** * Test  *)
Module Test.

  Module Import VectorR := RingVectorTheoryDR RingElementTypeR.
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
(** ** 2-dim vector operations *)

(** Square of length of a 2D-vector *)
Definition vlen2 (v : vec 2) : A :=
  let '(x,y) := v2t_2 v in
  (x * x + y * y)%X.

(* ==================================== *)
(** ** 3-dim vector operations *)

(** Square of length of a 3D-vector *)
Definition vlen3 (v : vec 3) : A :=
  let '(x,y,z) := v2t_3 v in
  (x * x + y * y + z * z)%X.

(** Dot product of a 3D-vector *)
Definition vdot3 (v0 v1 : vec 3) : A :=
  let '(a0,b0,c0) := v2t_3 v0 in
  let '(a1,b1,c1) := v2t_3 v1 in
  (a0 * a1 + b0 * b1 + c0 * c1)%X.


(** v1 <> 0 -> v2 <> 0 -> v1 = c c* v2 -> k <> 0 *)
Lemma vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : vec n) k,
    vnonzero v1 -> vnonzero v2 -> v1 = k c* v2 -> k <> A0.
Proof.
  intros. intro. subst. rewrite vcmul_0_l in H. destruct H. easy.
Qed.


(* ==================================== *)
(** ** Vector equility *)
Lemma veq_dec : forall {n} (v1 v2 : vec n), {v1 = v2} + {not (v1 = v2)}.
Proof.
  intros. apply meq_dec.
Qed.

 *)
