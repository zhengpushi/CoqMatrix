(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector theory on R.
  author    : ZhengPu Shi
  date      : 2021.12

  reference resources:
  1. 《高等数学学习手册》徐小湛，p173
  2. Vector Calculus - Michael Corral
  3. https://github.com/coq/coq/blob/master/test-suite/success/Nsatz.v
     Note that, there are concepts related to geometry including 
          point, parallel, colinear.
 *)

Require Import VectorAll.
Require MatrixR.
Export HierarchySetoid.
Export ListNotations.
Export TupleExt.



(* ######################################################################### *)
(** * Export vector theory on concrete elements *)

Module VectorAllR.
  Include DecidableFieldVectorTheory DecidableFieldElementTypeR.
  Open Scope R_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorAllR.
  
Module VectorR_DL.
  Include VectorAllR.DL.
  Open Scope R_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorR_DL.

Module VectorR_DP.
  Include VectorAllR.DP.
  Open Scope R_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorR_DP.

Module VectorR_DR.
  Include VectorAllR.DR.
  Open Scope R_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorR_DR.

Module VectorR_NF.
  Include VectorAllR.NF.
  Open Scope R_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorR_NF.

Module VectorR_SF.
  Include VectorAllR.SF.
  Open Scope R_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
End VectorR_SF.


(* ######################################################################### *)
(** * Extended matrix theory *)

(* Export MatrixR.MatrixR. *)

(** Export matrix theory on R type *)
Export MatrixR.
(* Check det3. *) (* we can use det3 now *)

(** Set a default model *)
Export VectorR_SF.

(* ======================================================================= *)
(** ** Vector with any dimension *)
Section DimAny.

  (** Length (magnitude) of a vector *)
  Definition vlen {n} (v : vec n) : R := sqrt (vdot v v).

  (** Length of a vector u is one, iff the dot product of u and u is one *)
  Lemma vlen_eq1_iff_vdot_eq1 : forall n (u : vec n), (vlen u == A1 <-> vdot u u == A1)%A.
  Proof.
    intros. unfold vlen. remember (vdot u u) as r.
    split; intros; hnf in *.
    ra. rewrite H. ra.
  Qed.

  (** A unit vector u is a vector whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable.
   *)
  Definition vunit {n} (u : vec n) : Prop := (vdot u u == A1)%A.

  (** Verify the definition is reasonable *)
  Lemma vunit_ok : forall {n} (u : vec n), vunit u <-> (vlen u == A1)%A.
  Proof.
    intros. split; intros; apply vlen_eq1_iff_vdot_eq1; auto.
  Qed.

  (** Normalization of a non-zero vector v.
      That is, get a unit vector in the same directin as v. *)
  Definition vnormalize {n} (v : vec n) : vec n :=
    let k := 1 / (vlen v) in
    vcmul k v.
  
  (** Every vector of length zero all are zero-vector *)
  Lemma vec_len0_is_vec0 : forall v : vec 0, v == vec0.
  Proof. lma. Qed.
  
  (** If k times a non-zero vector equal to zero vector, then k must be not zero *)
  Lemma vcmul_vnonzero_neq0_imply_neq0 : forall {n} (v : vec n) k,
      vnonzero v -> ~(k c* v == vec0) -> k <> A0.
  Proof.
    intros. intro. subst.
    rewrite vcmul_0_l in H0. destruct H0. easy.
  Qed.

  (** Two non-zero vectors has k-times relation, then k is not zero *)
  Lemma vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : vec n) k,
      vnonzero v1 -> vnonzero v2 -> v1 == k c* v2 -> k <> A0.
  Proof.
    intros. intro. subst. rewrite vcmul_0_l in H1. destruct H. easy.
  Qed.
  
  (** If k times a non-zero vector equal to zero, then k must be zero *)
  (*
    v <> 0 ==> ~(∀ i, v[i] = 0)
    k*v = 0 ==> ∀ i, k*v[i] = 0
    {k=0}+{k<>0} ==> k<>0  (if k=0, then qed)
    ---------------------------
    ∃ i, v[i] <> 0, then, k*v[i] <> 0, thus, contradict.
   *)
  Lemma vcmul_nonzero_eq_zero_imply_k0 : forall {n} (v : vec n) k,
      vnonzero v -> k c* v == vec0 -> k = 0.
  Proof.
    intros. destruct v as [v]. cbv in *.
    destruct (decidable k 0); auto.
    (* idea: from "~(∀ij(v i j = 0)" to "∃ij(v i j≠0)" *)
    (* Tips, a good practice of logic proposition *)
    assert (exists (ij:nat*nat), let (i,j) := ij in (i<n)%nat /\ (j<1)%nat /\ ~(v i j == A0)%A).
    { clear k H0 n0.
      apply not_all_not_ex. intro.
      destruct H. intros. specialize (H0 (i,0)%nat). simpl in H0.
      apply not_and_or in H0. destruct H0; try easy.
      apply not_and_or in H0. destruct H0; try easy; try lia.
      apply NNPP in H0.
      assert (j = 0%nat) by lia. subst. auto. }
    destruct H1. destruct x as (i,j). destruct H1. destruct H2.
    specialize (H0 i j H1 H2).
    apply Rmult_integral in H0. destruct H0; easy.
  Qed.

  (** If use k1 and k2 to left multiplicate a non-zero vector get same result, 
        then k1 and k2 must be equal. *)
  Lemma vcmul_vnonzero_eq_iff_unique_k : forall {n} (v : vec n) k1 k2, 
      vnonzero v -> k1 c* v == k2 c* v -> k1 = k2.
  Proof.
    intros. destruct v as [v]. cbv in H,H0.
    (* ∀i(f(i)=0 /\ k1*f(i) = k2*f(i)) -> k1 = k2 *)
    destruct (decidable k1 k2); auto.
    destruct H. intros. (* eliminated the universal quantifiers *)
    specialize (H0 i j H H1).
    (* k1 * x = k2 * x  /\  k1 <> k2  -> x = 0 *)
    ra.
  Qed.

  (** If k times a non-zero vector equal to itself, then k is equal to 1 *)
  Lemma vcmul_vnonzero_eq_self_imply_k1 : forall {n} (v : vec n) k,
      vnonzero v -> k c* v == v -> k = 1.
  Proof.
    intros. destruct v as [g].
    cbv in H,H0.
    (* To prove k = 1， first get a conclusion of k <> 1, then eliminate the 
         universal quantifiers *)
    destruct (decidable k 1); auto.
    destruct H. intros. specialize (H0 i j H H1).
    (* k * x = x /\  k <> 1 /\ x <> 0 -> x = 0 *)
    apply Rmult_eq_self_imply_0_or_k1 in H0. destruct H0; try easy.
  Qed.

  
  (** Two vectors are parallel (or said colinear) *)
  (* Note:
       1. definition: zero-vector is parallel to any vector, or two non-zero
          vectors have k times relation
       2. There are two choices to handling zero-vector
          (1). The mainstream approach is that the zero vector is parallel and
               perpendicular to any vector.
          (2). Only consider the non-zero vector, one reason of it is that the 
               transitivity is broken after including zero-vector.
       3. About parallel:
          https://www.zhihu.com/question/489006373
          a. “平行”或“不平行”是对两个可以被识别的方向的比较，对于零向量，“方向”是不可
             识别的，或说，是不确定的。从这个角度讲，“平行”这个概念不该被用到评价两个
             零向量的关系上的。
          b. 不过，两个零向量是“相等”的，对于向量而言，“相等”这件事包含了大小和方向
             的相等，这么说来，说两个零向量“方向”相等，也就是“平行”或也是说得通的。
   *)

  (* Definition 1: v1 is k times to v2，or v2 is k times to v1 *)
  Definition vparallel_ver1 {n} (v1 v2 : vec n) : Prop :=
    exists k, (v1 == k c* v2 \/ v2 == k c* v1).

  (* Definition 2: v1 is zero-vector, or v2 is zero-vector, or v1 is k times to v2 *)
  Definition vparallel_ver2 {n} (v1 v2 : vec n) : Prop :=
    (vzero v1) \/ (vzero v2) \/ (exists k, v1 == k c* v2).

  (* These two definitions are same *)
  Lemma vparallel_ver1_eq_ver2 : forall {n} (v1 v2 : vec n),
      vparallel_ver1 v1 v2 <-> vparallel_ver2 v1 v2.
  Proof.
    intros. unfold vparallel_ver1, vparallel_ver2.
    unfold vzero, vnonzero, Vector.vzero. split; intros.
    - destruct H. destruct H.
      + right. right. exists x. auto.
      + destruct (decidable v1 vec0); auto.
        destruct (decidable v2 (vec0)); auto.
        right. right. exists (A1/x)%A. rewrite H.
        lma. apply vec_eq_vcmul_imply_coef_neq0 in H; auto.
    - destruct H as [H1 | [H2 | H3]].
      + exists A0. left. rewrite H1. rewrite vcmul_0_l. easy.
      + exists A0. right. rewrite H2. rewrite vcmul_0_l. easy.
      + destruct H3. exists x. left; auto.
  Qed.

  (** Vector parallel relation. Here, we use definition 2 *)
  Definition vparallel {n} (v0 v1 : vec n) : Prop :=
    vparallel_ver2 v0 v1.

  Notation "v0 // v1" := (vparallel (v0) (v1)) (at level 70) : vec_scope.


  (** * Properties of vector parallel *)

  (** This is an equivalence relation *)

  Lemma vparallel_refl : forall {n} (v : vec n), v // v.
  Proof.
    intros. unfold vparallel,vparallel_ver2. right. right. exists 1.
    rewrite vcmul_1_l. easy.
  Qed.

  Lemma vparallel_sym : forall {n} (v0 v1 : vec n), v0 // v1 -> v1 // v0.
  Proof.
    intros. unfold vparallel,vparallel_ver2 in *.
    assert ({vzero v0} + {vnonzero v0}). apply meq_dec.
    assert ({vzero v1} + {vnonzero v1}). apply meq_dec.
    destruct H0.
    - right; left; auto.
    - destruct H1.
      + left; auto.
      + destruct H; auto. destruct H; auto. destruct H.
        right; right. exists (A1/x)%A. rewrite H.
        lma. apply vec_eq_vcmul_imply_coef_neq0 in H; auto.
  Qed.

  (* Additionally, v1 need to be a non-zero vector.
       Because if v1 is zero vector, then v0//v1, v1//v2, but v0 and v2 needn't
       to be parallel. *)
  Lemma vparallel_trans : forall {n} (v0 v1 v2 : vec n), 
      vnonzero v1 -> v0 // v1 -> v1 // v2 -> v0 // v2.
  Proof.
    intros. unfold vparallel, vparallel_ver2 in *.
    assert ({vzero v0} + {vnonzero v0}). apply meq_dec.
    assert ({vzero v1} + {vnonzero v1}). apply meq_dec.
    assert ({vzero v2} + {vnonzero v2}). apply meq_dec.
    destruct H2.
    - left; auto.
    - destruct H4.
      + right; left; auto.
      + right; right.
        destruct H3.
        * destruct H0; try contradiction.
        * destruct H0,H1; try contradiction.
          destruct H0,H1; try contradiction.
          destruct H0,H1. unfold vcmul. 
          exists (x*x0)%A. rewrite H0,H1. apply mcmul_assoc.
  Qed.

  (** If two non-zero vectors are parallel, then there is a unique k such that
        they are k times relation *)
  Lemma vparallel_vnonezero_imply_unique_k : forall {n} (v1 v2 : vec n),
      vnonzero v1 -> vnonzero v2 -> v1 // v2 -> (exists ! k, v1 == k c* v2).
  Proof.
    intros.
    destruct H1; try contradiction.
    destruct H1; try contradiction.
    destruct H1. exists x. unfold unique. split; auto.
    intros. apply vcmul_vnonzero_eq_iff_unique_k with (v:=v2); auto.
    rewrite <- H1,H2. easy.
  Qed.

  (** Given a non-zero vector v1 and another vector v2,
        v1 is parallel to v2, iff, there is a unique k such that v2 is k times v1.
        The left-to-right direction is a corollary of last lemma *)
  Lemma vparallel_iff1 : forall {n} (v1 v2 : vec n) (H : vnonzero v1),
      (v1 // v2) <-> (exists ! k, v2 == k c* v1).
  Proof.
    intros. split; intros.
    - destruct (decidable v2 vec0).
      + destruct H0; try easy. clear H0.
        exists 0. split.
        * rewrite vcmul_0_l. auto.
        * intros.
          rewrite v in H0.
          apply symmetry in H0. apply symmetry.
          apply vcmul_nonzero_eq_zero_imply_k0 in H0; auto.
      + apply vparallel_sym in H0.
        apply vparallel_vnonezero_imply_unique_k in H0; auto.
    - destruct H0. destruct H0. apply vparallel_sym.
      right. right. exists x. auto.
  Qed.
  
End DimAny.


(* ======================================================================= *)
(** ** Vector of 3-dim *)
Section Dim3.

  (** skew symmetry matrix *)
  Definition skew_sym_mat_of_v3 (v : vec 3) : smat 3 :=
    let '(x,y,z) := v2t_3 v in 
    (mk_mat_3_3
      A0    (-z)  y
      z     A0    (-x)
      (-y)  x     A0)%A.

  (** dot product of two 3-dim vectors *)
  Definition vdot3 (a b : vec 3) : A :=
    let '(a1,a2,a3) := v2t_3 a in 
    let '(b1,b2,b3) := v2t_3 b in
    (a1*b1 + a2*b2 + a3*b3)%A.

  (** cross product (vector product) of two 3-dim vectors *)
  Definition vcross3 (v1 v2 : vec 3) : vec 3 := ((skew_sym_mat_of_v3 v1) * v2)%mat.

  (** If a matrix is SO3? *)
  (* SO(n): special orthogonal group *)
  Definition so3 (m : smat 3) : Prop := 
    let so3_mul_unit : Prop := ((m \T) * m == mat1 3)%mat in
    let so3_det : Prop := (det3 m) = A1 in
    so3_mul_unit /\ so3_det.
  
  (** Angle between two vectors *)
  Definition vangle3 (v0 v1 : vec 3) : R := 
    acos (scalar_of_mat (v0\T * v1)%mat).

  (** The angle between (1,0,0) and (1,1,0) is 45 degree, i.e., π/4 *)
  Example vangle3_ex1 : vangle3 (l2v [1;0;0]) (l2v [1;1;0]) = PI/4.
  Proof.
    compute.
    (*     Search acos. *)
  Abort. (* 暂不知哪里错了，要去查叉乘的意义 *)
  
  (** 根据两个向量来计算旋转轴 *)
  Definition rot_axis_by_twovec (v0 v1 : vec 3) : vec 3 :=
    let s : R := (vlen v0 * vlen v1)%R in
    (s c* (vcross3 v0 v1))%mat.

  (* 谓词：两向量不共线（不平行的） *)
(* Definition v3_non_colinear (v0 v1 : V3) : Prop :=
    v0 <> v1 /\ v0 <> (-v1)%M.
 *)
  
End Dim3.


(** ** Test *)
Section Test.
  Open Scope R.

  (* Compute v2l (@l2v 3 [1;2;3]). *)

  Notation "0" := R0.
  Notation "1" := R1.
  
  Let v1 := @l2v 5 (map nat2R (seq 0 5)).
  (* Compute v2l v1. *)
  (* Compute vdot v1 v1. *)

End Test.
