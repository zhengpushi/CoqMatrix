(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector theory on real numbers
  author    : ZhengPu Shi
  date      : 2021.12
  
  ref:
  1. 《高等数学学习手册》徐小湛，p173
  2. Vector Calculus - Michael Corral
  3. https://github.com/coq/coq/blob/master/test-suite/success/Nsatz.v
     注意，这里有Coq库中定义的几何学形式化内容，包括点，平行，共线等。
*)

Require Export Vector.
Require Export RMatrix.

Open Scope R.
Open Scope mat_scope.

(* ======================================================================= *)
(** ** 从向量理论 导出的 实数域向量理论 *)

Definition vec := vec (A:=R).

Definition v2f {n} (v : vec n) := v2f v.

Definition f2v {n} f : vec n := f2v n f.

Definition vnth {n} (v : vec n) i := vnth v i.

Definition veq {n} (v1 v2 : vec n) := veq v1 v2.
Global Infix "==" := veq : vec_scope.

Lemma veq_refl : forall {n} (v : vec n), v == v.
Proof. intros. apply veq_refl. Qed.

Lemma veq_sym : forall {n} (v1 v2 : vec n), v1 == v2 -> v2 == v1.
Proof. intros. apply veq_sym; auto. Qed.

Lemma veq_trans : forall {n} (v1 v2 v3 : vec n),
    v1 == v2 -> v2 == v3 -> v1 == v3.
Proof. intros. apply veq_trans with v2; auto. Qed.

Hint Resolve veq_refl : vec.
Hint Resolve veq_sym : vec.
Hint Resolve veq_trans : vec.

Lemma veq_dec : forall {n} (v1 v2 : vec n), {v1 == v2} + {~(v1 == v2)}.
Proof. intros. apply veq_dec. Qed.

Definition t2v_2 (t : T2) : vec 2 := t2v_2 (A0:=0) t.

Definition v2t_2 (v : vec 2) : T2 := v2t_2 v.

Definition t2v_3 (t : T3) : vec 3 := t2v_3 (A0:=0) t.

Definition v2t_3 (v : vec 3) : T3 := v2t_3 v.

Definition t2v_4 (t : T4) : vec 4 := t2v_4 (A0:=0) t.

Definition v2t_4 (v : vec 4) : T4 := v2t_4 v.

Lemma v2t_t2v_id_2 : forall (t : T2), v2t_2 (t2v_2 t) = t.
Proof. intros. apply v2t_t2v_id_2. Qed.

Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v.
Proof. intros. apply t2v_v2t_id_2. Qed.

Definition v2l {n} (v : vec n) := v2l v.

Definition l2v n l : vec n := l2v (A0:=0) l.

Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
Proof. intros. apply v2l_length. Qed.

Lemma v2l_l2v_id : forall {n} l, length l = n -> v2l (l2v n l) = l.
Proof. intros. apply v2l_l2v_id; auto. Qed.

Lemma l2v_v2l_id : forall {n} (v : vec n), l2v _ (v2l v) == v.
Proof. intros. apply l2v_v2l_id. Qed.

Definition vec0 n : vec n := vec0 (A0:=0).

Definition vzero {n} (v : vec n) := vzero (A0:=0) v.

Definition vnonzero {n} (v : vec n) := vnonzero (A0:=0) v.

Lemma vec0_eq_mat0 : forall {n}, vec0 n == mat0 n 1.
Proof. apply vec0_eq_mat0. Qed.

Lemma vzero_dec : forall {n} (v : vec n), {vzero v} + {vnonzero v}.
Proof. intros. apply vzero_dec. Qed.

Definition vmap {n} (v : vec n) f : vec n := vmap v f.

Definition vmap2 {n} (v1 v2 : vec n) f : vec n := vmap2 v1 v2 f.

Definition vdot {n} (v1 v2 : vec n) :=
  vdot v1 v2 (add0:=Rplus) (zero0:=0) (mul0:=Rmult).

Definition vlen_sqr {n} (v : vec n) : R := vdot (n:=n) v v.

Definition vadd {n} (v1 v2 : vec n) : vec n := vadd v1 v2 (add0:=Rplus).
Global Infix "+" := vadd : vec_scope.

Lemma vadd_comm : forall {n} (v1 v2 : vec n), v1 + v2 == v2 + v1.
Proof. intros. apply vadd_comm. Qed.

Lemma vadd_assoc : forall {n} (v1 v2 v3 : vec n),
    (v1 + v2) + v3 == v1 + (v2 + v3).
Proof. intros. apply vadd_assoc. Qed.

Lemma vadd_0_l : forall {n} (v : vec n), (vec0 n) + v == v.
Proof. intros. apply vadd_0_l. Qed.

Lemma vadd_0_r : forall {n} (v : vec n), v + (vec0 n) == v.
Proof. intros. apply vadd_0_r. Qed.

Definition vopp {n} (v : vec n) : vec n := vopp v (opp:=Ropp).
Global Notation "- v" := (vopp v) : vec_scope.

Lemma vadd_vopp : forall {n} (v : vec n), v + (-v) == (vec0 n).
Proof. intros. apply vadd_opp. Qed.

Definition vsub {n} (v1 v2 : vec n) := vsub v1 v2 (add0:=Rplus) (opp:=Ropp).
Global Infix "-" := vsub : vec_scope.

Definition vcmul {n} a (v : vec n) := vcmul a v (mul0:=Rmult).
Global Infix "c*" := vcmul : vec_scope.

Definition vmulc {n} (v : vec n) a := vmulc v a (mul0:=Rmult).
Global Infix "*c" := vmulc : vec_scope.

Lemma vmulc_eq_vcmul : forall {n} a (v : vec n), v *c a == a c* v.
Proof. intros. apply vmulc_eq_vcmul. Qed.

Lemma vcmul_assoc : forall {n} a b (v : vec n), (a * b)%R c* v == a c* (b c* v).
Proof. intros. apply vcmul_assoc. Qed.

Lemma vcmul_perm : forall {n} a b (v : vec n), a c* (b c* v) == b c* (a c* v).
Proof. intros. apply vcmul_perm. Qed.

Lemma vcmul_add_distr_l : forall {n} a (v1 v2 : vec n),
    a c* (v1 + v2) == a c* v1 + a c* v2.
Proof. intros. apply vcmul_add_distr_l. Qed.

Lemma vcmul_add_distr_r : forall {n} a b (v : vec n),
    (a + b) c* v == a c* v + b c* v.
Proof. intros. apply vcmul_add_distr_r. Qed.

Lemma vcmul_1_l : forall {n} (v : vec n), 1 c* v == v.
Proof. intros. apply vcmul_1_l. Qed.

Lemma vcmul_0_l : forall {n} (v : vec n), 0 c* v == vec0 n.
Proof. intros. apply vcmul_0_l. Qed.

Lemma vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : vec n) k,
    vnonzero v1 -> vnonzero v2 -> v1 == k c* v2 -> k <> 0.
Proof. intros. apply vec_eq_vcmul_imply_coef_neq0 with v1 v2; auto. Qed.


(* ======================================================================= *)
(** ** 新增的 实数域向量理论 *)

(** 向量的长度，模，范数（欧几里得范数）。存在性的构造，适合证明 *)
Definition vlen {n} (v : vec n) : R := sqrt (vlen_sqr v).

(** 非零向量的单位化 *)

(* 旧的定义，提供 v 非零的证明。修改原因：在定义中没必要提及性质 *)
Definition vnormalize' {n} (v : vec n) (H : vnonzero (n:=n) v) : vec n :=
  let k := 1 / (vlen v) in
  vcmul k v.
Definition vnormalize {n} (v : vec n) : vec n :=
  let k := 1 / (vlen v) in
  vcmul k v.

(** 长度为0的向量具有唯一性 *)
(* Lemma vec_len0_is_vec0 : forall v : vec 0, v == vec0 0. *)
Lemma vec_len0_uniq : forall v : vec 0, v == vec0 0.
Proof.
  intros. apply meq_iff. intro. intros. easy.
Qed.

(** 非零向量v的k倍等于0，则k必为0 *)
Lemma vcmul_nonzero_eq0_imply_k0 : forall {n} (v : vec n) k,
    vnonzero v -> k c* v == vec0 n -> k = 0.
Proof.
  intros. destruct v as [g].
  unfold vnonzero,vzero,vec0,mat0 in *.
  unfold veq in *. meq_simp.
  (* 思路：特例化 H0，导出矛盾 *)
  (* 判断 k 是否为0 *)
  destruct (Req_EM_T k 0); auto.
  (* 先看n是否为零，分两种情况 *)
  destruct n.
  - cbv in H.
    exfalso. apply H. intros. lia.
  - exfalso. cbv in H. cbv in H0.
    apply H. intros. apply (H0 i j H1) in H2.
    (* k<>0 /\ k * (g i j) = 0 -> g i j = 0 *)
    apply Rmult_integral in H2. destruct H2; try easy.
Qed.

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
Definition vparallel_ver1 {n} (v1 v2 : vec n) : Prop :=
  exists k, (v1 == k c* v2 \/ v2 == k c* v1).

(* 定义2：v1 是 0，或者 v2 是 0，或者 v1 是 v2 的 k 倍 *)
Definition vparallel_ver2 {n} (v1 v2 : vec n) : Prop :=
  (vzero v1) \/ (vzero v2) \/ (exists k, v1 == k c* v2).

(* 证明这两个定义等价 *)
Lemma vparallel_ver1_eq_ver2 : forall {n} (v1 v2 : vec n),
    vparallel_ver1 v1 v2 <-> vparallel_ver2 v1 v2.
Proof.
  intros. unfold vparallel_ver1, vparallel_ver2.
  unfold vzero, vnonzero. split; intros.
  - destruct H. destruct H.
    + right. right. exists x. auto.
    + destruct (veq_dec v1 (vec0 n)); auto.
      destruct (veq_dec v2 (vec0 n)); auto.
      right. right. exists (R1/x). rewrite H.
      apply meq_iff.
      intros i j Hi Hj. destruct v1 as [g1], v2 as [g2]. simpl in *.
      field.
      apply vec_eq_vcmul_imply_coef_neq0 in H; auto.
  - destruct H as [H1 | [H2 | H3]].
    + exists R0. left. cbv in *. intros. rewrite H1; auto. ring.
    + exists R0. right. cbv in *. intros. rewrite H2;auto. ring.
    + destruct H3. exists x. left; auto.
Qed.

(** 向量平行谓词的定义 *)
Definition vparallel {n} (v0 v1 : vec n) : Prop :=
  vparallel_ver2 v0 v1.

Notation "v0 // v1" := (vparallel (v0) (v1)) (at level 70) : vec_scope.


(** * 向量平行的性质 *)

(** 向量平行是等价关系 *)

(** 自反性 *)
Lemma vparallel_refl : forall {n} (v : vec n), v // v.
Proof.
  intros. unfold vparallel,vparallel_ver2. right. right. exists 1.
  rewrite mcmul_1_l. easy.
Qed.

(** 对称性 *)
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
      right; right. exists (1/x). rewrite H.
      rewrite <- vcmul_assoc.
      replace (1/x * x)%R with 1.
      rewrite vcmul_1_l; auto with vec.
      field.
      apply (vec_eq_vcmul_imply_coef_neq0 v0 v1); auto.
Qed.

(** 传递性 *)
(* 要求v1是非零向量。因为若v1为0，v0//v1, v1//v2, 但 v0,v2 不平行 *)
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
        destruct H0,H1. 
        exists (x*x0)%R. rewrite H0,H1. apply mcmul_assoc.
Qed.

(** 数乘非零向量得到非零向量，则该系数必不为 0 *)
Lemma vcmul_vnonzero_neq0_imply_k_neq0 : 
  forall {n} (v : vec n) (H : vnonzero v) k, ~(k c* v == vec0 n) -> k <> 0.
Proof.
  intros. intro. subst. rewrite vcmul_0_l in H0. destruct H0. easy.
Qed.

(** 两个非零向量k倍相等，k唯一 *)
Lemma vcmul_vnonzero_eq_iff_unique_k : 
  forall {n} (v : vec n) (H : vnonzero v) k1 k2, 
    k1 c* v == k2 c* v -> k1 = k2.
Proof.
  intros. destruct v as [g].
  cbv in H. cbv in H0.
  (* ∀i(f(i)=0 /\ k1*f(i) = k2*f(i)) -> k1 = k2 *)
  destruct (Req_EM_T k1 k2); auto.
  destruct H. intros. (* 消去了全称量词 *)
  specialize (H0 i j H H1).
  ra.
Qed.

(** 非零向量k倍相等于自己，则k为1 *)
Lemma vcmul_vnonzero_eq_self_iff_k1 : 
  forall {n} (v : vec n) (H : vnonzero v) k, 
    k c* v == v -> k = 1.
Proof.
  intros. destruct v as [g]. cbv in H,H0.
  (* 证明 k = 1，老的方法，先得到 k <> 1 的前提，然后消去全称量词 *)
  destruct (Req_EM_T k 1); auto.
  destruct H. intros. (* 消去了全称量词 *)
  specialize (H0 i j H H1).
  (* forall k, (forall x, k * x = x -> x = 0 \/ (x <> 0 /\ k = 1)). *)
  ra.
Qed.

(** 非零向量平行，则存在唯一比例系数k *)
Lemma vparallel_vnonezero_imply_unique_k :
  forall {n} (v1 v2 : vec n) (H1 : vnonzero v1) (H2 : vnonzero v2),
    v1 // v2 -> (exists ! k, v1 == k c* v2).
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
Lemma vparallel_iff1 : forall {n} (v1 v2 : vec n) (H : vnonzero v1),
    (v1 // v2) <-> (exists ! a, v2 == a c* v1).
Proof.
  intros.
  split; intros.
  - destruct (veq_dec v2 (vec0 n)).
    + exists 0. split.
      * rewrite m. rewrite vcmul_0_l. auto with vec.
      * intros. rewrite m in H1.
        apply eq_sym. apply veq_sym in H1.
        apply vcmul_nonzero_eq0_imply_k0 in H1; auto.
    + unfold vparallel,vparallel_ver2 in *.
      destruct H0; try easy. destruct H0; try easy.
      destruct H0. exists (1/x). split.
      * rewrite H0. intros i j Hi Hj. simpl. field.
        apply vcmul_vnonzero_neq0_imply_k_neq0 with (v2); auto.
        rewrite <- H0. auto.
      * intros. rewrite H0 in H1.
        rewrite <- vcmul_assoc in H1.
        apply veq_sym in H1.
        apply vcmul_vnonzero_eq_self_iff_k1 in H1; auto.
        rewrite <- H1. field.
        apply vcmul_vnonzero_neq0_imply_k_neq0 with (v2); auto.
        rewrite <- H0. auto.
  - destruct H0. destruct H0. apply vparallel_sym.
    unfold vparallel, vparallel_ver2.
    right. right. exists x. auto.
Qed.


(* ======================================================================= *)
(** *** 3-dim vector operations *)

(** V3斜对称矩阵 *)
Definition skew_sym_mat_of_v3 (v : vec 3) : mat 3 3 :=
  let '(x,y,z) := v2t_3 v in 
  mk_mat_3_3
    0    (-z)  y
    z     0    (-x)
    (-y)  x     0.

(** V3叉乘，向量积 *)
Definition vcross3 (v1 v2 : vec 3) : vec 3 := ((skew_sym_mat_of_v3 v1) * v2).

(** 矩阵是否为SO3（李群，旋转群） *)
Definition so3 (m : mat 3 3) : Prop := 
  let so3_mul_unit : Prop := ((m ') * m) = mat1 3 in
  let so3_det : Prop := (det3 m) = 1 in
  so3_mul_unit /\ so3_det.

(** 计算两个向量的夹角 *)
Definition vangle3 (v0 v1 : vec 3) : R := 
  acos (m2t_1x1 (v0 ᵀ * v1)).

(** (1,0,0) 和 (1,1,0) 的夹角是 45度，即 π/4 *)
Example vangle3_ex1 : vangle3 (l2v 3 [1;0;0]) (l2v 3 [1;1;0]) = PI/4.
Proof.
  compute.
      (* Search acos. *)
Abort. (* 暂不知哪里错了，要去查叉乘的意义 *)

(** 根据两个向量来计算旋转轴 *)
Definition rot_axis_by_twovec (v0 v1 : vec 3) : vec 3 :=
  let s : R := (vlen v0 * vlen v1)%R in
  s c* (vcross3 v0 v1).

(* 谓词：两向量不共线（不平行的） *)
(* Definition v3_non_colinear (v0 v1 : V3) : Prop :=
    v0 <> v1 /\ v0 <> (-v1)%M.
 *)
