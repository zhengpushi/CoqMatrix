(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector theory of real numbers based on Function
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. Use real numbers to represent components.
  2. it is based on VectorThySig
  
  ref:
  1. 《高等数学学习手册》徐小湛，p173
  2. Vector Calculus - Michael Corral
  3. https://github.com/coq/coq/blob/master/test-suite/success/Nsatz.v
     注意，这里有Coq库中定义的几何学形式化内容，包括点，平行，共线等。
*)

Require Export NatFun.VectorThy.
Require Export FieldStruct.
Require Export ListListExt RExt.

Module VectorThyR := VectorThy FieldR.FieldDefR.
Export VectorThyR.

Open Scope R.


(* ######################################################################### *)
(** * 向量理论在实数域上的扩充 *)

(* ======================================================================= *)
(** ** 任意维度上的通用向量操作 *)
Section DimAny.

  (** 向量的长度，模，范数（欧几里得范数）的平方。方便计算。*)
  Definition vlen_sqr {n} (v : V n) : R := vdot v v.

  (** 向量的长度，模，范数（欧几里得范数）。存在性的构造，适合证明 *)
  Definition vlen {n} (v : V n) : R := sqrt (vlen_sqr v).

  (** 非零向量的单位化 *)
  Definition vnormalize {n} (v : V n) (H : vnonzero v) : V n :=
    let k := 1 / (vlen v) in
      vcmul k v.
  
  (** 长度为0的向量，也都是零向量 *)
  Lemma vec_len0_is_vec0 : forall v : V 0, v = vec0.
  Proof.
    intros. apply meq_iff. intro. intros. easy.
  Qed.

  (** 非零向量v的k倍等于0，则k必为0 *)
  Lemma vcmul_nonzero_eq_zero_imply_k0 : forall {n} (v : V n) k,
    vnonzero v -> k c* v = vec0 -> k = 0.
  Proof.
    intros. destruct v as [g].
    unfold vnonzero,vzero,vec0,mat0 in *.
    apply meq_iff in H0. apply neq_imply_mneq in H.
    unfold mcmul,vzero,vec0,mat0,meq in H,H0. simpl in *.
    Admitted.
(*     !! Something wrong.
    assert (~(forall i j, (i < n)%nat -> (j < 1)%nat -> g i j = A0)).
    { intro. destruct H. f_equal.
      apply functional_extensionality. intros.
      apply functional_extensionality. intros. auto. }
    (*  ∀ij(k * g i j = 0)  ~∀ij(g i j = 0)   -> k = 0
      思路：由 ∀ij(k * g i j = 0) 得 k = 0 \/ ∀ij(g i j = 0) *)
    destruct (Aeqdec k 0); auto.
    assert (forall i j, (i < n)%nat -> (j < 1)%nat -> g i j = A0).
    { intros. assert ((k * g i j)%A = A0).
      { apply H0; auto. }
      (* k<>0 /\ k * (g i j) = 0 -> g i j = 0 *)
      apply Rmult_integral in H4. destruct H4; try easy. }
    { 
  Qed. *)

  (** 向量平行（共线）：零向量与任何向量平行，或者非零向量是k倍的关系
    定义：u和v中，一个是另一个的数乘。 
    平行：parallel
    共线：colinear
    
    遗留问题：主流做法是零向量与任何向量都平行、都垂直。
    是否可以：仅考虑非零向量的平行，零向量不考虑。
    一个原因是：考虑零向量后，平行传递性不完美了。
    *)

  (* 关于零向量的平行？ 
    1. https://www.zhihu.com/question/489006373
    两个方面:
    a. “平行”或“不平行”是对两个可以被识别的方向的比较，对于零向量，“方向”是不可
      识别的，或说，是不确定的。从这个角度讲，“平行”这个概念不该被用到评价两个
      零向量的关系上的。
    b. 不过，两个零向量是“相等”的，对于向量而言，“相等”这件事包含了大小和方向
      的相等，这么说来，说两个零向量“方向”相等，也就是“平行”或也是说得通的。
  *)

  (* 定义1：v1是v2的k倍，或者 v2是v1的k倍。*)
  Definition vparallel_ver1 {n} (v1 v2 : V n) : Prop :=
    exists k, (v1 = k c* v2 \/ v2 = k c* v1).

  (* 定义2：v1 是 0，或者 v2 是 0，或者 v1 是 v2 的 k 倍 *)
  Definition vparallel_ver2 {n} (v1 v2 : V n) : Prop :=
    (vzero v1) \/ (vzero v2) \/ (exists k, v1 = k c* v2).

  (* 证明这两个定义等价 *)
  Lemma vparallel_ver1_eq_ver2 : forall {n} (v1 v2 : V n),
    vparallel_ver1 v1 v2 <-> vparallel_ver2 v1 v2.
  Proof.
    intros. unfold vparallel_ver1, vparallel_ver2.
    unfold vzero, vnonzero. split; intros.
    - destruct H. destruct H.
      + right. right. exists x. auto.
      + destruct (veq_dec v1 (vec0)); auto.
        destruct (veq_dec v2 (vec0)); auto.
        right. right. exists (X1/x)%X. rewrite H.
        apply meq_iff.
        intros i j Hi Hj. destruct v1 as [g1], v2 as [g2]. simpl in *.
        field.
        apply vec_eq_vcmul_imply_coef_neq0 in H; auto.
    - destruct H as [H1 | [H2 | H3]].
      + exists X0. left. rewrite H1. compute. f_equal.
        apply functional_extensionality. intros.
        apply functional_extensionality. intros. ring.
      + exists X0. right. rewrite H2. compute. f_equal.
        apply functional_extensionality. intros.
        apply functional_extensionality. intros. ring.
      + destruct H3. exists x. left; auto.
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
        right; right. exists (X1/x)%X. rewrite H.
        compute. intros.
        remember v1. destruct v3. f_equal.
(*         apply meq_iff. intros i j Hi Hj. simpl. *)
        apply functional_extensionality. intros.
        apply functional_extensionality. intros.
        unfold X in *. field.
        rewrite Heqv3 in *.
        apply (vec_eq_vcmul_imply_coef_neq0 v0 v1); auto.
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
          destruct H0,H1. 
          exists (x*x0). rewrite H0,H1. apply mcmul_assoc.
  Qed.
  
  (** 数乘非零向量得到零向量，则该系数必为 0 *)
  Lemma vcmul_vnonzero_eq0_imply_k_eq0 : 
    forall {n} (v : V n) (H : vnonzero v) k, k c* v = vec0 -> k = X0.
  Proof.
    intros. destruct v as [g].
    unfold vnonzero,vzero,vec0,mat0,meq in *; simpl in *.
    (* ∀i(f i <> 0 /\ k * f i = 0 -> k = 0 *)
    (* 方法：先由 k = 0 的结论反推出 k <> 0 的前提；然后构造某个全称量词中的
      否定命题。 *)
    destruct (Xeqdec k 0); auto. (* 得到了 k <> 0 的前提 *)
    destruct H. (* 转而证明 f i = 0 *)
    f_equal. apply functional_extensionality.
    intros i. apply functional_extensionality.
(* (*     intros j. remember (H0 i j). H H1) as E.  (* 以上两步，消去了全称量词 *) *)
(*     clear HeqE. *)
    apply Rmult_integral in E. destruct E; auto. easy.
  Qed. *)
  Admitted.
  
  (** 数乘非零向量得到非零向量，则该系数必不为 0 *)
  Lemma vcmul_vnonzero_neq0_imply_k_neq0 : 
    forall {n} (v : V n) (H : vnonzero v) k, ~(k c* v = vec0) -> k <> X0.
  Proof.
    intros. intro. subst. rewrite vcmul_0_l in H0. destruct H0. easy.
  Qed.

  (** 两个非零向量k倍相等，k唯一 *)
  Lemma vcmul_vnonzero_eq_iff_unique_k : 
    forall {n} (v : V n) (H : vnonzero v) k1 k2, 
      k1 c* v = k2 c* v -> k1 = k2.
  Proof.
    intros. destruct v as [g]. unfold vnonzero,vzero,vec0,mat0,meq in *.
    simpl in *.
    (* ∀i(f(i)=0 /\ k1*f(i) = k2*f(i)) -> k1 = k2 *)
    destruct (Xeqdec k1 k2); auto.
    destruct H. intros. (* 消去了全称量词 *)
(*     remember (H0 i j H H1) as E. clear HeqE.
    (* k1 * x = k2 * x  /\  k1 <> k2  -> x = 0 *)
    apply Rmult_eq_imply_eq0_r in E; auto.
  Qed. *)
  Admitted.

  (** 非零向量k倍相等于自己，则k为1 *)
  Lemma vcmul_vnonzero_eq_self_iff_k1 : 
    forall {n} (v : V n) (H : vnonzero v) k, 
      k c* v = v -> k = 1.
  Proof.
    intros. destruct v as [g].
    unfold vnonzero,vzero,vec0,mat0,meq in *; simpl in *.
    (* 证明 k = 1，老的方法，先得到 k <> 1 的前提，然后消去全称量词 *)
    destruct (Xeqdec k 1); auto.
    destruct H. intros. (* 消去了全称量词 *)
(*     remember (H0 i j H H1) as E. clear HeqE.
    destruct (Aeqdec (g i j) A0); auto.
    (* k * x = x /\  k <> 1 /\ x <> 0 -> x = 0 *)
    (* 需要一条性质：
      forall k, (forall x, k * x = x -> x = 0 \/ (x <> 0 /\ k = 1)). *)
    apply Rmult_eq_self_imply_0_or_k1 in E. destruct E; try easy.
  Qed.
 *)
 Admitted.
 
  (** 非零向量平行，则存在唯一比例系数k *)
  Lemma vparallel_vnonezero_imply_unique_k : forall {n} (v1 v2 : V n) 
    (H1 : vnonzero v1) (H2 : vnonzero v2),
    v1 // v2 -> (exists ! k, v1 = k c* v2).
  Proof.
    intros.
    destruct H; try contradiction.
    destruct H; try contradiction.
    destruct H. exists x. unfold unique. split; auto.
    intros. apply vcmul_vnonzero_eq_iff_unique_k with (v:=v2); auto.
    rewrite <- H,H0. easy.
  Qed.

  (** 给定 向量v1，v2，
    v1<>0 /\ v1//v2 <=> 存在唯一实数 a 使得 v2 = a * v1 *)
  Lemma vparallel_iff1 : forall {n} (v1 v2 : V n) (H : vnonzero v1),
    (v1 // v2) <-> (exists ! a, v2 = a c* v1).
  Proof.
    intros.
(*     unfold vparallel, vparallel_ver2, vnonzero in *. *)
    split; intros.
    - destruct (veq_dec v2 (vec0)).
      + exists 0. split.
(*         * rewrite v. compute. intros. ring.
        * intros. rewrite v in H1. apply veq_sym in H1.
          apply eq_sym. apply vcmul_vnonzero_eq0_imply_k_eq0 in H1; auto.
      + unfold vparallel,vparallel_ver2 in *.
        destruct H0; try easy. destruct H0; try easy.
        destruct H0. exists (A1/x)%A. split.
        * rewrite H0. intros i j Hi Hj. simpl. field.
          apply vcmul_vnonzero_neq0_imply_k_neq0 with (v2); auto.
          rewrite <- H0. auto.
        * intros. rewrite H0 in H1.
          rewrite vcmul_assoc1 in H1.
          apply veq_sym in H1.
          apply vcmul_vnonzero_eq_self_iff_k1 in H1; auto.
          rewrite <- H1. field.
          apply vcmul_vnonzero_neq0_imply_k_neq0 with (v2); auto.
          rewrite <- H0. auto.
    - destruct H0. destruct H0. apply vparallel_sym.
      unfold vparallel, vparallel_ver2.
      right. right. exists x. auto.
  Qed. *)
  Admitted.

End DimAny.



(* ======================================================================= *)
(** ** 3-dim vector operations *)
Section Dim3.
   
  (** 3阶方阵的行列式 *)
  Definition det3 (m : M 3 3) : X :=
    let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) :=
      m2t_3x3 m in
    let b1 := (a11 * a22 * a33) in
    let b2 := (a12 * a23 * a31) in
    let b3 := (a13 * a21 * a32) in
    let c1 := (a11 * a23 * a32) in
    let c2 := (a12 * a21 * a33) in
    let c3 := (a13 * a22 * a31) in
    let b := (b1 + b2 + b3) in
    let c := (c1 + c2 + c3) in
      (b - c).

  (** V3斜对称矩阵 *)
  Definition skew_sym_mat_of_v3 (v : V 3) : M 3 3 :=
    let '(x,y,z) := v2t_3 v in 
      mk_mat_3_3
        X0    (-z)  y
        z     X0    (-x)
        (-y)  x     X0.

  (** V3叉乘，向量积 *)
  Definition vcross3 (v1 v2 : V 3) : V 3 := ((skew_sym_mat_of_v3 v1) * v2)%M.

  (** 矩阵是否为SO3（李群，旋转群） *)
  Definition so3 (m : M 3 3) : Prop := 
    let so3_mul_unit : Prop := ((m ᵀ) * m)%M = mat1 3 in
    let so3_det : Prop := (det3 m) = X1 in
      so3_mul_unit /\ so3_det.
  
   (** 计算两个向量的夹角 *)
  Definition vangle3 (v0 v1 : V 3) : R := 
    acos (scalar_of_mat (v0 ᵀ * v1)%M).
  
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
