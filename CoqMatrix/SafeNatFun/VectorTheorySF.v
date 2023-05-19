(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector Theory implemented with SafeNatFun (with Module)
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. This is safe version of NatFun, which corrected the shape problem
*)


Require Export VectorTheory.
Require Export SafeNatFun.Vector.


(* ######################################################################### *)
(** * Basic vector theory implemented with SafeNatFun *)

Module BasicVectorTheorySF (E : ElementType).

  (* ==================================== *)
  (** ** Also contain matrix theory *)
  (* Module Export BasicMatrixTheorySF := BasicMatrixTheorySF E. *)

  (* ==================================== *)
  (** ** Vector element type *)
  Export E.

  Infix "==" := (eqlistA Aeq) : list_scope.

  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
  
  (* ==================================== *)
  (** ** Vector type *)

  Definition vec n := @vec A n.

  (** matrix equality *)
  Definition veq {n} (v1 v2 : vec n) : Prop := @veq _ Aeq n v1 v2.
  Global Infix "==" := veq : vec_scope.

  (** meq is equivalence relation *)
  Lemma veq_equiv : forall n, Equivalence (veq (n:=n)).
  Proof. apply veq_equiv. Qed.

  (** Get element of vector *)
  Definition vnth {n} (v : vec n) i : A := vnth (Azero:=Azero) v i.
  Global Notation "v ! i " := (vnth v i) : vec_scope.

  (** veq and mnth should satisfy this constraint *)
  Lemma veq_iff_vnth : forall {n : nat} (v1 v2 : vec n),
      (v1 == v2) <-> (forall i, i < n -> (v1!i == v2!i)%A).
  Proof. intros. apply veq_iff_vnth. Qed.
  

  (* ==================================== *)
  (** ** Convert between list and vector *)
  Definition v2l {n} (v : vec n) : list A := v2l v.
  Definition l2v {n} (l : list A) : vec n := l2v Azero n l.
  
  Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
  Proof. intros. apply v2l_length. Qed.
  
  Lemma v2l_l2v_id : forall {n} (l : list A),
    length l = n -> (@v2l n (@l2v n l) == l)%list.
  Proof. intros. apply v2l_l2v_id; auto. Qed.

  Lemma l2v_v2l_id : forall {n} (v : vec n), l2v (v2l v) == v.
  Proof. intros. apply l2v_v2l_id; auto. Qed.
  
  (* ==================================== *)
  (** ** Make concrete vector *)
  Definition mk_vec2 (a0 a1 : A) : vec 2 := mk_vec2 (Azero:=Azero) a0 a1.
  Definition mk_vec3 (a0 a1 a2 : A) : vec 3 := mk_vec3 (Azero:=Azero) a0 a1 a2.
  Definition mk_vec4 (a0 a1 a2 a3 : A) : vec 4 := mk_vec4 (Azero:=Azero) a0 a1 a2 a3.

  (* ==================================== *)
  (** ** Convert between tuples and vector *)
  Definition t2v_2 (t : @T2 A) : vec 2 := t2v_2 (Azero:=Azero) t.
  Definition t2v_3 (t : @T3 A) : vec 3 := t2v_3 (Azero:=Azero) t.
  Definition t2v_4 (t : @T4 A) : vec 4 := t2v_4 (Azero:=Azero) t.

  Definition v2t_2 (v : vec 2) : @T2 A := v2t_2 v.
  Definition v2t_3 (v : vec 3) : @T3 A := v2t_3 v.
  Definition v2t_4 (v : vec 4) : @T4 A := v2t_4 v.
  
  Lemma v2t_t2v_id_2 : forall (t : A * A), v2t_2 (t2v_2 t) = t.
  Proof. apply v2t_t2v_id_2. Qed.
  
  Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v.
  Proof. apply t2v_v2t_id_2. Qed.
  
  (** mapping of a vector *)
  Definition vmap {n} (v : vec n) f : vec n := vmap v f.
  
  (** folding of a vector *)
  (* Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)
  
  (** mapping of two matrices *)
  Definition vmap2 {n} (v1 v2 : vec n) f : vec n := vmap2 v1 v2 f.

  (* ======================================================================= *)
  (** ** Advanced matrix construction by mixing vectors and matrices *)
  Section AdvancedConstrtuct.

    (** Construct a matrix with a vector and a matrix by row *)
    Definition mconsr {r c} (v : vec c) (m : mat r c) : mat (S r) c :=
      mconsr v m.

    (** Construct a matrix with a vector and a matrix by column *)
    Definition mconsc {r c} (v : vec r) (m : mat r c) : mat r (S c) :=
      mconsc v m.

  End AdvancedConstrtuct.
  
End BasicVectorTheorySF.

  
(* ######################################################################### *)
(** * Ring vector theory implemented with SafeNatFun *)

(** zero vector, vector addition, opposition, substraction, scalar multiplication,
    dot product *)
Module RingVectorTheorySF (E : RingElementType) <: RingVectorTheory E.

  Export E.
  Include (BasicVectorTheorySF E).

  (** Import ring matrix theory *)
  (* Module Export RingMatrixTheorySF := RingMatrixTheorySF E. *)

  Open Scope mat_scope.
  Open Scope vec_scope.

  (** ** Zero vector *)
  Definition vec0 {n} : vec n := vec0 (Azero:=Azero).

  (** Assert that a vector is an zero vector. *)
  Definition vzero {n} (v : vec n) : Prop := vzero (Azero:=Azero) (Aeq:=Aeq) v.

  (** Assert that a vector is an non-zero vector. *)
  Definition vnonzero {n} (v : vec n) : Prop := vnonzero (Azero:=Azero) (Aeq:=Aeq) v.
  
  (** vec0 is equal to mat0 with column 1 *)
  Lemma vec0_eq_mat0 : forall n, vec0 == mat0 Azero n 1.
  Proof. apply vec0_eq_mat0. Qed.
  
  
  (** *** Vector addition *)

  Definition vadd {n} (v1 v2 : vec n) : vec n := vadd (Aadd:=Aadd) v1 v2.
  Global Infix "+" := vadd : vec_scope.

  (** v1 + v2 = v2 + v1 *)
  Lemma vadd_comm : forall {n} (v1 v2 : vec n), (v1 + v2) == (v2 + v1).
  Proof. intros. apply vadd_comm. Qed.

  (** (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma vadd_assoc : forall {n} (v1 v2 v3 : vec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof. intros. apply vadd_assoc. Qed.

  (** vec0 + v = v *)
  Lemma vadd_0_l : forall {n} (v : vec n), vec0 + v == v.
  Proof. intros. apply vadd_0_l. Qed.

  (** v + vec0 = v *)
  Lemma vadd_0_r : forall {n} (v : vec n), v + vec0 == v.
  Proof. intros. apply vadd_0_r. Qed.

  
  (** *** Vector opposite *)
  
  Definition vopp {n} (v : vec n) : vec n := vopp (Aopp:=Aopp) v.
  Global Notation "- v" := (vopp v) : vec_scope.

  (** v + (- v) = vec0 *)
  Lemma vadd_opp_r : forall {n} (v : vec n), v + (- v) == vec0.
  Proof. intros. apply vadd_opp. Qed.

  (** (- v) + v = vec0 *)
  Lemma vadd_opp_l : forall {n} (v : vec n), (- v) + v == vec0.
  Proof. intros. rewrite vadd_comm. apply vadd_opp. Qed.


  (** *** Vector subtraction *)

  Definition vsub {n} (v1 v2 : vec n) : vec n := vsub (Aadd:=Aadd) (Aopp:=Aopp) v1 v2.
  Global Infix "-" := vsub : vec_scope.


  (** *** Vector scalar multiplication *)

  Definition vcmul {n} a (v : vec n) : vec n := vcmul (Amul:=Amul) a v.
  Definition vmulc {n} (v : vec n) a : vec n := vmulc (Amul:=Amul) v a.
  Global Infix "c*" := vcmul : vec_scope.
  Global Infix "*c" := vmulc : vec_scope.

  (** v *c a = a c* v *)
  Lemma vmulc_eq_vcmul : forall {n} a (v : vec n), (v *c a) == (a c* v).
  Proof. intros. apply vmulc_eq_vcmul. Qed.

  (** a c* (b c* v) = (a * b) c* v *)
  Lemma vcmul_assoc : forall {n} a b (v : vec n), a c* (b c* v) == (a * b)%A c* v.
  Proof. intros. apply vcmul_assoc. Qed.

  (** a c* (b c* v) = b c* (a c* v) *)
  Lemma vcmul_perm : forall {n} a b (v : vec n), a c* (b c* v) == b c* (a c* v).
  Proof. intros. apply vcmul_perm. Qed.

  (** (a + b) c* v = (a c* v) + (b c* v) *)
  Lemma vcmul_add_distr_l : forall {n} a b (v : vec n), 
    (a + b)%A c* v == (a c* v) + (b c* v).
  Proof. intros. apply vcmul_add_distr_l. Qed.

  (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
  Lemma vcmul_add_distr_r : forall {n} a (v1 v2 : vec n), 
    a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply vcmul_add_distr_r. Qed.

  (** 1 c* v = v *)
  Lemma vcmul_1_l : forall {n} (v : vec n), Aone c* v == v.
  Proof. intros. apply vcmul_1_l. Qed.

  (** 0 c* v = vec0 *)
  Lemma vcmul_0_l : forall {n} (v : vec n), Azero c* v == vec0.
  Proof. intros. apply vcmul_0_l. Qed.
  
  
  (** *** Vector dot product *)
  
  (** dot production of two vectors. *)
  Definition vdot {n : nat} (v1 v2 : vec n) :=
    vdot (Azero:=Azero) (Aadd:=Aadd) (Amul:=Amul) v1 v2.
  Infix "⋅" := vdot : vec_scope.

  (** dot production is commutative *)
  Lemma vdot_comm : forall {n} (v1 v2 : vec n), (v1 ⋅ v2 == v2 ⋅ v1)%A.
  Proof. intros. apply vdot_comm. Qed.

  (** 0 * v = 0 *)
  Lemma vdot_0_l : forall {n} (v : vec n), (vec0 ⋅ v == Azero)%A.
  Proof. intros. apply vdot_0_l. Qed.

  (** v * 0 = 0 *)
  Lemma vdot_0_r : forall {n} (v : vec n), (v ⋅ vec0 == Azero)%A.
  Proof. intros. apply vdot_0_r. Qed.
  
End RingVectorTheorySF.



(* ######################################################################### *)
(** * Decidable-field vector theory implemented with SafeNatFun  *)

Module DecidableFieldVectorTheorySF (E : DecidableFieldElementType)
<: DecidableFieldVectorTheory E.

  (* ==================================== *)
  (** ** Also contain matrix theory *)
  (* Module Export DecidableFieldMatrixTheorySF := DecidableFieldMatrixTheorySF E. *)

  Export E.
  Include (RingVectorTheorySF E).

  Open Scope mat_scope.
  Open Scope vec_scope.

  (** veq is decidable *)
  Lemma veq_dec : forall (n : nat), Decidable (veq (n:=n)).
  Proof. intros. apply veq_dec. Qed.

  Global Existing Instance veq_dec.

  (** It is decidable that if a vector is zero vector. *)
  Lemma vzero_dec : forall {n} (v : vec n), {vzero v} + {vnonzero v}.
  Proof. intros. apply veq_dec. Qed.
  
End DecidableFieldVectorTheorySF.

  
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
 *)
