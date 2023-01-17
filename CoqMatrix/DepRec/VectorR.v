(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector theory of real numbers based on ListList
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. Use real numbers to represent components.
  2. it is based on VectorThySig
*)

Require Export DepRec.VectorThy.
Require Export FieldStruct.
Require Export ListListExt RExt.

Export FieldR.
Module Export VectorThyR := VectorThy FieldR.FieldDefR.

Open Scope R.
Open Scope mat_scope.
Open Scope vec_scope.

(* ######################################################################### *)
(** * Vector theory on Real numbers *)

(* ==================================== *)
(** ** Vector operations on any dimensions *)
Section DimAny.

  (** Length of a vector, also known as magnitude, and norm (Euclidean norm). *)
  
  (** Vector length squared. Note: it is suitable for compute *)
  Definition vlen_sqr {n} (v : V n) : R := vdot v v.

  (** Vector length. Note: it is a existential construct, suitable for proofs. *)
  Definition vlen {n} (v : V n) : R := sqrt (vlen_sqr v).

  (** Normalization of non-zero vector *)
  Definition vnormalize {n} (v : V n) (H : vnonzero v) : V n :=
    let k := 1 / (vlen v) in
      vcmul k v.

  (** The k times of a non-zero vector v is equal to 0, then k must be 0 *)
  Lemma vcmul_nonzero_eq_zero_imply_k0 : forall {n} (v : V n) k,
    vnonzero v -> k c* v = vec0 -> k = 0.
  Proof.
    intros. destruct v. unfold vnonzero in *. unfold vec0 in *.
    unfold mcmul in *.
    apply meq_iff in H0. apply meq_iff_not in H. simpl in *.
    unfold dmap in *.
    destruct (Xeqdec k 0); auto.
    rename mat_data into dl.
    generalize dependent n.
    generalize dependent dl. induction dl; intros.
    - simpl in *; subst; simpl in *. easy.
    - simpl in *. destruct n; simpl in *. easy.
      destruct mat_width. inversion mat_height.
      unfold dlzero in H. simpl in H.
      rewrite cons_neq_iff in H; try apply list_eq_dec.
      + destruct H.
        * (* a != [0] *)
          destruct a; try easy.
          assert (x <> 0 /\ a = []).
          { apply list_length1_neq. split; auto. }
          destruct H3.
          rewrite H5 in H0. simpl in H0. inversion H0.
  (*         assert ({k = 0} + {k != 0}). apply Aeqdec. *)
          destruct (Xeqdec k 0); auto.
          assert (k * x <> 0)%X; try easy.
          apply Rmult_integral_contrapositive_currified; auto.
        * (* dl != repeat [A0] n *)
          apply IHdl with (n:=n); auto.
          inversion H0. rewrite H6. rewrite H5. auto.
      + apply Xeqdec.
  Qed.

  (** Vector parallel (collinear): zero vector is parallel to any vector, 
      or two non-zero vectors has k times relation.
      
      Discussion:
      The mainstream approach is that, the zero vector is parallel and perpendicular 
      to any vector. If we could discuss parallel only for non-zero vector?
      A explicit reason is that, transitivity of parallel relation is not preserved 
      if contain zero vector.

      Ref: https://www.zhihu.com/question/489006373
      
      关于零向量的平行？ 两个方面:
      a. “平行”或“不平行”是对两个可以被识别的方向的比较，对于零向量，“方向”是不可
         识别的，或说，是不确定的。从这个角度讲，“平行”这个概念不该被用到评价两个
         零向量的关系上的。
      b. 不过，两个零向量是“相等”的，对于向量而言，“相等”这件事包含了大小和方向
         的相等，这么说来，说两个零向量“方向”相等，也就是“平行”或也是说得通的。
  *)

  (* 定义1：v0是v1的k倍，或者 v1是v0的k倍。*)
  Definition vparallel_ver1 {n} (v0 v1 : V n) : Prop :=
    exists k, (v0 = k c* v1 \/ v1 = k c* v0).

  (* 定义2：v0 是 0，或者 v1 是 0，或者 v0 是 v1 的 k 倍 *)
  Definition vparallel_ver2 {n} (v0 v1 : V n) : Prop :=
    (vzero v0) \/ (vzero v1) \/ (exists k, v0 = k c* v1).

  (* 证明这两个定义等价 *)
  Lemma vparallel_ver1_eq_ver2 : forall {n} (v0 v1 : V n),
    vparallel_ver1 v0 v1 <-> vparallel_ver2 v0 v1.
  Proof.
    intros. unfold vparallel_ver1, vparallel_ver2.
    unfold vzero, vnonzero. split; intros.
    - assert ({v0 = vec0} + {v0 <> vec0}). apply meq_dec.
      assert ({v1 = vec0} + {v1 <> vec0}). apply meq_dec.
      destruct H0.
      + left. auto.
      + destruct H1.
        * right. left. auto.
        * right. right. destruct H. destruct H.
          { exists x. auto. }
          { exists (1/x). rewrite H.
            rewrite mcmul_assoc.
            replace ((1/x)%R * x)%X with 1.
            rewrite mcmul_1_l. easy.
            compute. field.
            apply (vec_eq_vcmul_imply_coef_neq0 v1 v0); auto. }
    - destruct H.
      + exists 0. left. rewrite mcmul_0_l. rewrite H. rewrite vec0_eq_mat0.
        easy.
      + destruct H.
        * exists 0. right. rewrite mcmul_0_l,H,vec0_eq_mat0. easy.
        * destruct H. exists x. left. auto.
  Qed.

  (** 向量平行谓词的定义 *)
  Definition vparallel {n} (v0 v1 : V n) : Prop :=
    vparallel_ver2 v0 v1.

  Notation "v0 // v1" := (vparallel (v0) (v1)) (at level 70) : vec_scope.


  (** * 向量平行的性质 *)

  (** 向量平行是等价关系 *)

  (** 自反性 *)
  Lemma vparallel_refl : forall {n} (v : V n), v // v.
  Proof.
    intros. unfold vparallel,vparallel_ver2. right. right. exists 1.
    rewrite mcmul_1_l. easy.
  Qed.

  (** 对称性 *)
  Lemma vparallel_sym : forall {n} (v0 v1 : V n), v0 // v1 -> v1 // v0.
  Proof.
    intros. unfold vparallel,vparallel_ver2 in *.
    assert ({vzero v0} + {vnonzero v0}). apply meq_dec.
    assert ({vzero v1} + {vnonzero v1}). apply meq_dec.
    destruct H0.
    - right; left; auto.
    - destruct H1.
      + left; auto.
      + destruct H; auto. destruct H; auto. destruct H.
        right; right. rewrite H.
        exists (1/x). rewrite mcmul_assoc.
        replace ((1/x)%R * x)%X with 1. rewrite mcmul_1_l; easy.
        compute. field. apply (vec_eq_vcmul_imply_coef_neq0 v0 v1); auto.
  Qed.

  (** 传递性 *)
  (* 要求v1是非零向量。因为若v1为0，v0//v1, v1//v2, 但 v0,v2 不平行 *)
  Lemma vparallel_trans : forall {n} (v0 v1 v2 : V n), 
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
          destruct H0,H1. rewrite H0,H1.
          exists (x*x0)%X. apply mcmul_assoc.
  Qed.

  (** 非零向量k倍相等，k唯一 *)
  Lemma vcmul_vnonzero_eq_iff_unique_k : forall {n} (v : V n) (H : vnonzero v), 
    forall k1 k2, k1 c* v = k2 c* v -> k1 = k2.
  Proof.
    intros. destruct v. apply meq_iff in H0. simpl in *.
    rename mat_data into dl. unfold vnonzero in H. apply meq_iff_not in H.
    simpl in *.
    unfold dmap in *.
    (* hard part *)
    generalize dependent n. 
    generalize dependent dl.
    induction dl; intros.
    - simpl in *; subst; simpl in *. easy.
    - simpl in *. inversion H0. clear H0. destruct mat_width.
      destruct n. easy. simpl in *.
      apply cons_neq_iff in H. destruct H.
      + (* a != [0] *)
        destruct a. easy.
        assert (a = []).
        { simpl in *. inversion H0. rewrite length_zero_iff_nil in H5; auto. }
        assert (x <> 0).
        { rewrite H4 in *. apply cons_neq_iff in H. destruct H; auto.
          apply Xeqdec. }
        subst. simpl in H2. inversion H2.
        apply Rmult_eq_reg_r with (r:=x); auto.
      + (* dl != ListAux.cvt_row2col (repeat 0 n) *)
        apply IHdl with (n:=n); auto.
      + apply list_eq_dec. apply Xeqdec.
  Qed.

  (** 非零向量平行，则存在唯一比例系数k *)
  Lemma vparallel_vnonezero_imply_unique_k : forall {n} (v0 v1 : V n) 
    (H1 : vnonzero v0) (H2 : vnonzero v1),
    v0 // v1 -> (exists ! k, v0 = k c* v1).
  Proof.
    intros.
    destruct H; try contradiction.
    destruct H; try contradiction.
    destruct H. exists x. unfold unique. split; auto.
    intros. apply vcmul_vnonzero_eq_iff_unique_k with (v:=v1); auto.
    rewrite <- H,H0. easy.
  Qed.

  (** 非零向量v0，v1 与 v0 平行，iff，存在唯一实数 a 使得 v1 = a * v0 *)
  Lemma vparallel_iff1 : forall {n} (v0 v1 : V n) (H : vnonzero v0),
    (v1 // v0) <-> (exists ! a, v1 = a c* v0).
  Proof.
    intros. split; intros.
    - unfold vparallel, vparallel_ver2, vnonzero in *.
      assert ({vzero v0} + {vnonzero v0}). apply meq_dec.
      assert ({vzero v1} + {vnonzero v1}). apply meq_dec.
      destruct H1; try contradiction.
      destruct H2.
      + (* {vzero v1} *) 
        exists 0. unfold unique. split.
        * rewrite v2. rewrite mcmul_0_l. apply vec0_eq_mat0.
        * rewrite v2. intros.
          symmetry. symmetry in H1.
          apply vcmul_nonzero_eq_zero_imply_k0 with (v:=v0); auto.
      + (* {vnonzero v1} *)
        destruct H0; try easy.
        destruct H0; try easy.
        destruct H0.
        (* vnonzero v0 -> vnonzero v1 -> v1 = x * v0 -> exists ! x *)
        exists x. unfold unique. split; auto.
        intros. rewrite H0 in H1.
        apply vcmul_vnonzero_eq_iff_unique_k in H1; auto.
    - destruct H0. destruct H0.
      unfold vparallel. unfold vparallel_ver2.
      right. right. exists x. auto.
  Qed.

End DimAny.



(* ==================================== *)
(** ** 3-dim vector operations *)
Section Dim3.
   
  (** 3阶方阵的行列式 *)
  Definition det3 (m : M 3 3) : X :=
    let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) :=
      m2t_3x3 m in
    let b1 := (a11 * a22 * a33)%X in
    let b2 := (a12 * a23 * a31)%X in
    let b3 := (a13 * a21 * a32)%X in
    let c1 := (a11 * a23 * a32)%X in
    let c2 := (a12 * a21 * a33)%X in
    let c3 := (a13 * a22 * a31)%X in
    let b := (b1 + b2 + b3)%X in
    let c := (c1 + c2 + c3)%X in
      (b - c)%X.

  (** V3斜对称矩阵 *)
  Definition skew_sym_mat_of_v3 (v : V 3) : M 3 3 :=
    let '(x,y,z) := v2t_3 v in 
      (mk_mat_3_3
        X0    (-z)  y
        z     X0    (-x)
        (-y)  x     X0)%X.

  (** V3叉乘，向量积 *)
  Definition vcross3 (v1 v2 : V 3) : V 3 := (skew_sym_mat_of_v3 v1) * v2.

  (** 矩阵是否为SO3（李群，旋转群） *)
  Definition so3 (m : M 3 3) : Prop := 
    let so3_mul_unit : Prop := (m ᵀ) * m = mat1 3 in
    let so3_det : Prop := (det3 m) = X1 in
      so3_mul_unit /\ so3_det.
  
   (** 计算两个向量的夹角 *)
  Definition vangle3 (v0 v1 : V 3) : R := 
    acos (scalar_of_mat (v0 ᵀ * v1)).
  
  (** (1,0,0) 和 (1,1,0) 的夹角是 45度，即 π/4 *)
  Example vangle3_ex1 : vangle3 (l2v [1;0;0]) (l2v [1;1;0]) = PI/4.
  Proof.
    compute.
(*     Search acos. *)
    Abort. (* 暂不知哪里错了，要去查叉乘的意义 *)
    
  (** 根据两个向量来计算旋转轴 *)
  Definition rot_axis_by_twovec (v0 v1 : V 3) : V 3 :=
    let s : R := (vlen v0 * vlen v1)%R in
      (s c* (vcross3 v0 v1))%M.

  (* 谓词：两向量不共线（不平行的） *)
  (* Definition v3_non_colinear (v0 v1 : V3) : Prop :=
    v0 <> v1 /\ v0 <> (-v1)%M.
   *)
  
End Dim3.
