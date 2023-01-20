(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : Complex number
  author      : ZhengPu Shi
  date        : 2022.08
  
  ref         :
  1. 《复变函数与积分变换》第4版 华中科技大学 李红
  2. Coqtail project
  3. Coquelicot project
  
  remark      :
  1. Record定义，可以用 let (a,b,c) := x 来分解各个字段，也还可以 intro [x y z] 
   来分解，相比显式的写出 buildXX 这个构造函数名要简洁不少。
*)

(* Require Import ProofIrrelevance. (* proof_irrelevance *) *)

Require Export RExt.
Open Scope R.

(** * 自动化策略，后期会移动至全局位置 *)

(** 逻辑运算的化简 *)
Ltac logic_simp :=
  (* 将合取式、蕴涵式等去掉，转换为简单的形式 *)
  repeat match goal with
    (* 目标是合取式 *)
    | |- _ /\ _ => split
    (* 目标是蕴涵式 *)
    | |- _ -> _ => intros
    end.

(** 解决“可能以不同方向重写前提，并最终完成目标”的问题？
    例如：前提中有 E1,E2,...En 这么多等式，要证明目标，可能的形式有：
         Ei,Ej,Ek'
    其中，Ei 表示重写第 i 个等式，Ek' 表示反向重写第k个等式。
    换言之，解决路径是：
       开始: e1 或 e1'; reflexivity
       e1: e2 或 e2'; reflexivity
       e1': e2 或 e2'; reflexivity
       e2: e3 或 e3'; reflexivity
       如此迭代。

    暂时写不出比较通用的算法，但可以手动建立有限的几种形式。
 *)
(* Require Import CpdtTactics. *)
Module Export Try_Rewrite.
  Open Scope R.

  Ltac rewriteHyp :=
    let u H := (rewrite H) in
    let v H := (rewrite <- H) in
    match goal with
    | H1:_=_, H2:_=_, H3:_=_ |- _ =>
        try (u H1; u H2; u H3; reflexivity);
        try (u H1; u H2; v H3; reflexivity);
        try (u H1; v H2; u H3; reflexivity);
        try (u H1; v H2; v H3; reflexivity);
        try (v H1; u H2; u H3; reflexivity);
        try (v H1; u H2; v H3; reflexivity);
        try (v H1; v H2; u H3; reflexivity);
        try (v H1; v H2; v H3; reflexivity)
    | H1:_=_, H2:_=_ |- _ =>
        try (u H1; u H2; reflexivity);
        try (u H1; v H2; reflexivity);
        try (v H1; u H2; reflexivity);
        try (v H1; v H2; reflexivity)
    | H1:_=_ |- _ =>
        try (u H1; reflexivity);
        try (v H1; reflexivity)
    end.

  (** 示例1。subst,auto,lra,ring 等都不能解决 *)
  Goal forall a b c (f:R->R),
      a + b = b + c ->
      a + c = b + c ->
      f (a + b) = f (a + c).
  Proof.
    (* 测试了 crush，虽然能解决，但是花费了 0.5 s *)
    (* Time crush. (* 0.5s *) *)
    
    (* 手动证明：H,H0' *)
    (* logic_simp. *)
    (* rewrite H; rewrite <- H0; reflexivity. *)
    
    (* 自动证明 *)
    logic_simp.
    rewriteHyp.
  Qed.

End Try_Rewrite.


(* ======================================================================= *)
(** ** 1.1 复数 *)


(* --------------------------------------------------------------------- *)
(** *** 1.1.1 复数的基本概念 *)

(* 声明作用域 *)
Declare Scope C_scope.
Delimit Scope C_scope with C.
Open Scope C_scope.

(* 关于复数的定义，第一版定义为 pair，目前第二版定义为记录。
原因是，复数有不同的表示，可以是直角坐标表示，比如这里，也可以是三角表示，
所以，单独使用对偶容易混淆。暂时使用专门的名称来表示 *)

(** 复数的定义 *)
Record C := mkC {
  Cre : R;  (* 实部 *)
  Cim : R   (* 虚部 *)
}.

(** 用户友好的记号 *)
Notation "a '+i' b" := (mkC a b) (at level 10) : C_scope.

(** 由两个实数构造复数 *)
Definition RR2C (x y : R) : C := x +i y.

(** 由复数得到两个实数 *)
Definition C2RR (z : C) : R * R := (Cre z, Cim z).

(** 实数到复数，作为实部，虚部赋0 *)
Definition IRC (x : R) : C := x +i 0.

Coercion IRC : R >-> C.

(** 由复数得到实数，只保留实部，丢弃虚部 *)
Definition C2R (z : C) : R := Cre z.

(** 一些常数 *)
Definition C0 := RR2C 0 0.
Definition C1 := RR2C 1 0.
Definition Ci := RR2C 0 1.

(* 绑定作用域 *)
Bind Scope C_scope with C Cre Cim C0 C1.

Section ex.
  Let z : C := (sqrt 2) +i 1.
  
  Goal Cre z = sqrt 2. reflexivity. Qed.
  Goal Cim z = 1. auto. Qed.
End ex.

(** 复数为零，iff，x=y=0 *)
Lemma Ceq0_iff_re0_im0 : forall z : C, z = 0 <-> (Cre z = 0 /\ Cim z = 0).
Proof.
  intros [x y]. split; intros H.
  - inversion H. simpl. auto.
  - simpl in *. destruct H. subst. auto.
Qed.

(** 非零复数，iff，x^2 + y^2 <> 0 *)
Lemma Cneq0_iff_plus_sqr_re_sqr_im_neq0 : forall z : C, z <> 0 <-> 
  Cre z * Cre z + Cim z * Cim z <> 0.
Proof.
  intros [x y]. split; simpl; intros H.
  - intro. apply Rplus_sqr_eq_0 in H0. destruct H0; subst. auto.
  - intro. inversion H0; subst. lra.
Qed.

(** 非零复数 iff 实部和虚部不全为零 *)
Lemma Cneq0_iff_re_neq0_or_im_neq0 : forall z : C,
  z <> 0 <-> (Cre z <> 0 \/ Cim z <> 0).
Proof.
  intros [x y]; simpl; split; intro H.
  - case (Req_EM_T x 0); case (Req_EM_T y 0); intros Ha Hb; subst; auto.
  - intros H1. inversion H1. subst. destruct H; auto.
Qed.


(** 共轭复数 *)
Definition Cconj (z : C) : C := let (x, y) := z in (x +i (-y)).

Notation "\ z" := (Cconj z) (at level 30, right associativity) : C_scope.

(** 共轭的共轭等于自身 *)
Lemma Cconj_conj : forall z : C, \\z = z.
Proof. intros [x y]. simpl. f_equal. ring. Qed.


(* --------------------------------------------------------------------- *)
(** *** 1.1.2 复数的四则运算 *)


(** 若前提中有复数，则先分解为两个实数 *)
Ltac CtoR := match goal with
  | z:C |- _ => destruct z as [?r ?r]
  end.

(** 证明复数运算等式 *)
Ltac ceq :=
  intros;
  (* 将前提中所有复数分解为实数 *)
  repeat CtoR;
  (* 化简 *)
  compute;
  (* 若是复数等式，则转换为两个实数等式 *)
  try (match goal with | |- @eq C _ _ => f_equal end);
  (* 若是实数等式，则进行等式求解 *)
  try (match goal with | |- @eq R _ _ => try ring; try field end).

(** 复数的加法运算 *)
Definition Cadd (z1 : C) (z2 : C) : C :=
  let (x1, y1) := z1 in
  let (x2, y2) := z2 in
    (x1 + x2) +i (y1 + y2).
Infix "+" := Cadd : C_scope.

(** 复数加法满足结合律 *)
Lemma Cadd_assoc : forall z1 z2 z3, (z1 + z2) + z3 = z1 + (z2 + z3).
Proof. ceq. Qed.

(** 复数加法满足交换律 *)
Lemma Cadd_comm : forall z1 z2, z1 + z2 = z2 + z1.
Proof. ceq. Qed.

(** 复数的取反运算 *)
Definition Copp (z : C) : C :=
  let (x, y) := z in
    (-x) +i (-y).
Notation "- z" := (Copp z) : C_scope.

(** 复数的减法运算 *)
Definition Csub (z1 : C) (z2 : C) : C :=
  let (x1, y1) := z1 in
  let (x2, y2) := z2 in
    (x1 - x2) +i (y1 - y2).
Infix "-" := Csub : C_scope.

(** 复数减法满足反对称性 *)
Lemma Csub_antisym : forall z1 z2 : C, z1 - z2 = - (z2 - z1).
Proof. ceq. Qed.

(** 复数的乘法运算 *)
Definition Cmul (z1 : C) (z2 : C) : C :=
  let (x1, y1) := z1 in
  let (x2, y2) := z2 in
    (x1 * x2 - y1 * y2) +i (x1 * y2 + x2 * y1).
Infix "*" := Cmul : C_scope.

(** 复数乘法满足结合律 *)
Lemma Cmul_assoc : forall z1 z2 z3, (z1 * z2) * z3 = z1 * (z2 * z3).
Proof. ceq. Qed.

(** 复数乘法满足交换律 *)
Lemma Cmul_comm : forall z1 z2, z1 * z2 = z2 * z1.
Proof. ceq. Qed.

(** 复数乘法对加法满足分配律 *)
Lemma Cmul_add_distr_l : forall z1 z2 z3, z1 * (z2 + z3) = z1 * z2 + z1 * z3.
Proof. ceq. Qed.

Lemma Cmul_add_distr_r : forall z1 z2 z3, (z1 + z2) * z3 = z1 * z3 + z2 * z3.
Proof. ceq. Qed.

Section ex.
  Goal 2 +i (-3) * 4 +i 5 = 23 +i (-2). ceq. Qed.
  Goal Ci * Ci = -1. ceq. Qed.
End ex.

(** 实数乘以复数，即数乘 *)
Definition Cscal (a : R) (z : C) : C :=
  let (x, y) := z in (a * x) +i (a * y).

(** 复数的倒数 *)
Definition Cinv (z : C) : C :=
  let (x, y) := z in
  let r := (x * x + y * y)%R in
    (x / r) +i (-y / r).
Notation "/ z" := (Cinv z) : C_scope.

(** 复数的除法运算 *)
Definition Cdiv (z1 : C) (z2 : C) : C :=
  let (x1, y1) := z1 in
  let (x2, y2) := z2 in
  let r2 := (x2 * x2 + y2 * y2)%R in
  let u := ((x1 * x2 + y1 * y2) / r2)%R in
  let v := ((x2 * y1 - x1 * y2) / r2)%R in
    u +i v.
Infix "/" := Cdiv : C_scope.

(** 验证除法定义 *)
Lemma Cdiv_ok : forall z1 z2 : C, z2 <> 0 -> z1 = z2 * (z1 / z2).
Proof.
  ceq.
  all: apply Cneq0_iff_plus_sqr_re_sqr_im_neq0 in H; auto.
Qed.

(** 乘以自身的共轭的化简式 *)
Lemma Cmul_conj_self : forall z : C, z * \z =
  let (x,y) := z in (x*x+y*y) +i 0.
Proof. ceq. Qed.

(** 乘以某个共轭复数的化简式 *)
Lemma Cmul_conj_any : forall z1 z2 : C, z1 * \z2 =
  let (x1,y1) := z1 in
  let (x2,y2) := z2 in
    (x1 * x2 + y1 * y2) +i (x2 * y1 - x1 * y2).
Proof. ceq. Qed.

(** 利用上述性质得到复数除法的另一种形式 *)
Lemma Cdiv_eq : forall z1 z2 : C, z2 <> 0 -> 
  z1 / z2 = (z1 * \z2) / (z2 * \z2).
Proof.
  intros [x1 y1] [x2 y2] H. unfold Cdiv at 1.
  rewrite Cmul_conj_self.
  rewrite Cmul_conj_any. simpl. f_equal; field.
  all: apply (Cneq0_iff_plus_sqr_re_sqr_im_neq0 (x2+i y2)); auto.
Qed.

Section ex.
  Goal 3 +i (-2) / 2 +i 3 = -Ci. ceq. Qed.
End ex.

(** 共轭复数运算的一些性质 *)

(** 相加以后再共轭，等于共轭后再相加 *)
Lemma Cconj_add : forall z1 z2 : C, \(z1 + z2) = \z1 + \z2.
Proof. ceq. Qed.

(** 相减以后再共轭，等于共轭后再相减 *)
Lemma Cconj_sub : forall z1 z2 : C, \(z1 - z2) = \z1 - \z2.
Proof. ceq. Qed.

(** 相乘以后再共轭，等于共轭后再相乘 *)
Lemma Cconj_mul : forall z1 z2 : C, \(z1 * z2) = \z1 * \z2.
Proof. ceq. Qed.

(** 相除以后再共轭，等于共轭后再相除 *)
Lemma Cconj_div : forall z1 z2 : C, z2 <> 0 -> \(z1 / z2) = \z1 / \z2.
Proof.
  intros. ceq.
  all: replace (- r0 * - r0)%R with (r0 * r0)%R; try ring;
  apply Cneq0_iff_plus_sqr_re_sqr_im_neq0 in H; auto.
Qed.

(** 乘以共轭，等于模的平方 *)
Lemma Cmul_conj : forall z : C, z * \z =
  let (x, y) := z in (x * x + y * y) +i 0.
Proof. ceq. Qed.

(** 实部用共轭来表示 *)
Lemma Cre_eq : forall z : C, Cre z = C2R ((1/2) * (z + \z)).
Proof. ceq. Qed.

(** 虚部用共轭来表示 *)
Lemma Cim_eq : forall z : C, Cim z = C2R ((1 / (2 * Ci)) * (z - \z)).
Proof. ceq. Qed.

(** 例1 *)
Example ex1_1 : forall z1 z2, 
  (2 * Cre (z1 * \z2))%R = C2R (z1 * \z2 + \z1 * z2).
Proof. ceq. Qed.

(** 再次理解，复数是什么？
  1. 复数是用两个实数x,y同 i,+ 连接而成的这样一种形式，而i,+是什么，未说明。
  2. 现在，可以将复数 z = x + i y 理解为实数乘法和加法，只是 i 是特殊的。
  3. 历史上，第一次引进 -1 的平方根作为数时，作为想象中的数，称为“虚数”，
    后来把形如 x + i y 的数叫做复数，意思是“复合”起来的数。
*)

(** 用实数运算及i来构造复数 *)
Module complex_construction_by_real.
  
  Open Scope R.
  (** 因为 i 已经被使用，所以用 j 来代替 i *)
  Parameter j : R.
  Parameter sqr_neg1 : j * j = -1.
  
  Definition Complex (x y : R) : R := x + y * j.
  
  Lemma eq1 : forall x, x = Complex x 0.
  Proof. ceq. Qed.
  
  Lemma eq2 : j = 0 + 1 * j.
  Proof. ceq. Qed.
  
  Lemma eq3 : forall x y, (x + 0 * j) + (0 + 1 * j) * (y + 0 * j) = Complex x y.
  Proof. ceq. Qed.

  (** 形式上，已经构造出了复数。
      但是，由于假设了一个“在实数域中存在数j，使得j * j = -1”的前提，
      而该前提是错误的，因此后续证明都不可信。
      也许，复数与二维平面上的点一一映射，这种理解更加合理，i只是一个记号而已。
   *)

End complex_construction_by_real.



(* --------------------------------------------------------------------- *)
(** *** 1.1.3 复（数）平面 *)
 
(** 实数对、复数、坐标平面上的点三者的对应关系。
 复数集合、坐标平面 一个复数 x+iy 唯一对应一个有序实数对 (x,y)，
 而有序实数对与坐标平面上的点一一对应。
 现在，坐标平面上的点写成 x + i y，那么横轴上的点表示实数，纵轴上的点表示纯序数，
 整个坐标平面可称为复平面。
 今后，复数、复平面不加区分。
 在点、数等同的观点下，复数集合就是一个平面点集。
 于是，某些特殊的平面点集可用复数所满足的某种关系式来表示。
*)

Section cplane.
  
  (** 上半平面 *)
  Let set1 : Prop := forall z : C, Cim z >= 0.
  
  (** 以 0,1,1+i,i 为顶点的正方形 *)
  Let set2 : Prop := forall z : C, 
    let (x, y) := (Cre z, Cim z) in
    (0 <= x <= 1 /\ 0 <= y <= 1).

  (** 实部为1的一条直线 *)
  Let set3 : Prop := forall z : C, Cre z = 1.

End cplane.



(* ======================================================================= *)
(** ** 1.2 复数的三角表示 *)

(* --------------------------------------------------------------------- *)
(** *** 1.2.1 复数的模与辐角 *)

(** 除了将复数实部和虚部分别看做是直角坐标系下的横坐标与纵坐标，
 复数还可以与平面向量对应，将实部和虚部分别看做向量的水平和垂直分量。
 需要注意的是，向量具有平移不变性（即，起点可以放在任意一点），
 若把向量的起点放在（复平面的）坐标原点，则此向量与向量的终点恰好对应于同一个复数。
 即：复数x+iy, 平面一点(x,y)，向量x+iy[起点放在原点后]，这三者彼此对应。
*)

(** 提示：由于复数可以表示平面向量，所以有关平面向量的问题可能利用复变函数来研究。
 于是，复变函数论逐渐被应用于理论物理、弹性力学、流体力学等学科，成为重要的数学工具。
 同时，人们也改变了对复数的看法，不再认为是虚无缥缈的东西。*)

(** 复数的模：复数z不为0时，它所对应向量的长度称为z的模
 复数的模，也称绝对值、幅值 *)


(*  - - - - - - - - -  - - - - - - - - - - - - - - - - - - - - - - - - *)
(** **** 复数的模 *)

(** 复数的模的平方 *)
Definition Cnorm2 (z : C) : R := let (x, y) := z in x * x + y * y. 

(** 复数的模 *)
Definition Cnorm (z : C) : R := sqrt (Cnorm2 z).

Notation "| z |" := (Cnorm z) (at level 20) : C_scope.

  
(** 模相等，iff，模平方相等 *)
Lemma Cnormeq_iff_norm2eq : forall z1 z2, |z1| = |z2| <-> Cnorm2 z1 = Cnorm2 z2.
Proof. intros. ceq. logic_simp. auto with R. rewriteHyp. Qed.

(** 复数为零，iff，模平方为0 *)
Lemma Ceq0_iff_norm2_eq0 : forall z : C, (z = 0) <-> (Cnorm2 z = 0).
Proof.
  intros [x y]. unfold Cnorm2; split; intros.
  - inversion H. subst. compute. ring.
  - apply Rplus_sqr_eq_0 in H. destruct H; subst; auto.
Qed.

(** 复数为零，iff，模为0 *)
Lemma Ceq0_iff_norm_eq0 : forall z : C, (z = 0) <-> (|z| = 0).
Proof.
  intros [x y]. rewrite Ceq0_iff_norm2_eq0.
  unfold Cnorm, Cnorm2. split; intros H.
  - rewrite H. autorewrite with R; auto.
  - apply Rsqrt_plus_sqr_eq0_iff in H. destruct H; subst; ring.
Qed.

(** 复数的模平方非负 *)
Lemma Cnorm2_ge0 : forall z : C, 0 <= Cnorm2 z.
Proof.
  destruct z. unfold Cnorm2; simpl.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

(** 复数的模非负 *)
Lemma Cnorm_ge0 : forall z : C, 0 <= |z|.
Proof. intros z. unfold Cnorm. apply sqrt_pos. Qed.

(** 复数的模平方等于模的平方 *)
Lemma Cnorm2_eq : forall z : C, Cnorm2 z = (|z|)².
Proof.
  intros z. unfold Cnorm. rewrite Rsqr_sqrt; auto.
  apply Cnorm2_ge0.
Qed.

(** 复数不为零，iff，模平方不为0 *)
Lemma Cneq0_iff_norm2_neq0 : forall z : C, z <> 0 <-> Cnorm2 z <> 0.
Proof.
  intros [x y].
  rewrite Cneq0_iff_plus_sqr_re_sqr_im_neq0. simpl. tauto.
Qed.

(** 复数不为零，iff，模不为0 *)
Lemma Cneq0_iff_norm_neq0 : forall z : C, z <> 0 <-> |z| <> 0.
Proof.
  intros. split; intros H H1.
  - apply Ceq0_iff_norm_eq0 in H1. auto.
  - apply Ceq0_iff_norm_eq0 in H1. auto.
Qed.

(** 复数的模平方恒正，iff，该复数非零 *)
Lemma Cnorm2_pos_iff_neq0 : forall z : C, 0 < Cnorm2 z <-> z <> 0.
Proof.
  intros [x y]. unfold Cnorm2. split; intros.
  - intro. inversion H0. subst. lra.
  - apply Cneq0_iff_re_neq0_or_im_neq0 in H. simpl in *. destruct H.
    + apply Rplus_lt_le_0_compat; try apply Rle_0_sqr.
      apply Rsqr_pos_lt; auto.
    + apply Rplus_le_lt_0_compat; try apply Rle_0_sqr.
      apply Rsqr_pos_lt; auto.
Qed.

(** 模的平方等于乘以共轭 *)
Lemma Cnorm2_eq_mulConj : forall z, Cnorm2 z = C2R (z * \z).
Proof. ceq. Qed.

(** 复数的倒数等于 共轭除以模平方 *)
Lemma Cinv_eq_conjDivNorm2 : forall z : C, z <> 0 -> Cinv z = \z / (Cnorm2 z).
Proof.
  assert (H: forall a b, a +i b <> 0 -> (a*a + b*b <> 0)%R).
  { ra. intro. apply Rplus_sqr_eq0_iff in H0. destruct H0.
    destruct H. ceq;auto. }
  intros. ceq; apply H; auto.
Qed.

(** 实数提升为复数后的模等于原本实数的绝对值 *)
Lemma Cnorm_IRC : forall x : R, |IRC x| = Rabs x.
Proof.
  intros x. unfold Cnorm, Cnorm2; simpl.
  autorewrite with R. auto.
Qed.

(** 复数求模再求模结果不变。 | |z| | = |z|，其实是 | IRC (|z|) | = |z| *)
Lemma Cnorm_norm : forall z : C, | |z| | = |z|.
Proof.
  intro z; rewrite Cnorm_IRC.
  apply Rabs_right.
  apply Rle_ge; apply Cnorm_ge0.
Qed.

(** 共轭的模等于原本的模 *)
Lemma Cnorm_conj : forall z : C, |\z| = |z|.
Proof. intros [x y]. apply Cnormeq_iff_norm2eq. ceq. Qed.

(** 相反数的模等于原本的模 *)
Lemma Cnorm_opp : forall z : C, | -z | = |z|.
Proof. intros [x y]. simpl. apply Cnormeq_iff_norm2eq. simpl. ring. Qed.

(** 差的模满足对称性 *)
Lemma Cnorm_sub_sym : forall z1 z2 : C, |z1 - z2| = |z2 - z1|.
Proof. intros; rewrite Csub_antisym; rewrite Cnorm_opp; auto. Qed.

(** 数乘的模等于数乘以模 *)
Lemma Cnorm_scal : forall (a : R) (z : C), |Cscal a z| = ((Rabs a) * |z|)%R.
Proof.
  intros a [x y]. simpl. unfold Cnorm,Cnorm2.
  replace (a * x * (a * x) + a * y * (a * y))%R
  with ((a * a) * (x * x + y * y))%R; try ring.
  rewrite sqrt_mult_alt; auto with R; try nra.
  autorewrite with R; auto.
Qed.

(** 乘积的模等于模的乘积 *)
Lemma Cnorm_mul : forall z1 z2 : C, |z1 * z2| = (|z1| * |z2|)%R.
Proof.
  intros [x1 y1] [x2 y2]. unfold Cnorm,Cnorm2. simpl.
  rewrite <- sqrt_mult. f_equal. ring.
  all: apply Rplus_sqr_ge0.
Qed.

(** 非零复数，倒数的模等于模的倒数 *)

(** ToDo:
    在这个证明中，使用了 inv_sqrt 引理，但从 8.16 开始，提示这个引理即将弃用，
    不过我觉得这里有个问题：

    Check inv_sqrt. (* inv_sqrt
     : forall x : R, 0 < x -> (/ sqrt x)%R = sqrt (/ x) *)

    Check sqrt_inv. (* sqrt_inv
     : forall x : R, sqrt (/ x) = (/ sqrt x)%R *)

    看起来，sqrt_inv 少了一个前提，简单了。
    但是，这个引理到底对吗？当 x = 0 时，作何解释？
 *)
Lemma Cnorm_inv : forall z : C, z <> 0 -> | /z | = (/(|z|))%R.
Proof.
  intros [x y] H. unfold Cnorm, Cnorm2; simpl.
  match goal with
  | |- sqrt ?a = (/(sqrt ?b))%R =>
    replace a with (/b)%R; try field
  end.
  - rewrite sqrt_inv; auto.
  - apply Cneq0_iff_norm2_neq0 in H. auto.
Qed.


(*  - - - - - - - - -  - - - - - - - - - - - - - - - - - - - - - - - - *)
(** **** 辐角 *)

(** 复数的主辐角，本书规定 (-pi,pi]，有的书固定 [0,pi) *)
(*
  算法伪代码：
  if (x = 0) {
    if (y < 0) { -pi/2 } else { pi/2 }
  } else {
    if (x < 0) {
      if (y < 0) { atan(y/x) - pi } else { atan(y/x) + pi }
    } else {
      atan(y/x)
    }
  }

  ToDo: 由于复数为0时，俯角是任意值，这里隐含定义了俯角为 pi/2，不确定有没有问题?
*)
Definition Carg (z : C) : R :=
  let (x, y) := (Cre z, Cim z) in
  let r : R := atan (y / x)%R in
    if (Req_EM_T x 0)
    then (if Rcase_abs y then (- (PI / 2))%R else (PI / 2)%R)
    else (if Rcase_abs x 
      then (if Rcase_abs y then (r - PI)%R else (r + PI)%R)
      else r).

Notation "∠ z" := (Carg z) (at level 10) : C_scope.


(** 自动分解 Req_EM_T, Rcase_abs 情形，以证明 Carg 有关的等式 *)
Ltac tacCarg :=
  intros; 
  cbn;
  repeat (match goal with
  | |- context [Req_EM_T ?a ?b] => destruct Req_EM_T; try lra
  end);
  repeat (match goal with
  | |- context [Rcase_abs ?a] => destruct Rcase_abs; try lra
  end).
  
Lemma Carg_case1 : forall x y, x > 0 -> ∠ (x +i y) = atan (y/x).
Proof. tacCarg. Qed.
  
Lemma Carg_case2 : forall x y, x = 0 -> y > 0 -> ∠ (x +i y) = (PI / 2)%R.
Proof. tacCarg. Qed.
  
Lemma Carg_case3 : forall x y, x < 0 -> y >= 0 -> ∠ (x +i y) = (atan(y/x)+PI)%R.
Proof. tacCarg. Qed.

Lemma Carg_case4 : forall x y, x < 0 -> y < 0 -> ∠ (x +i y) = (atan(y/x)-PI)%R.
Proof. tacCarg. Qed.

Lemma Carg_case5 : forall x y, x = 0 -> y < 0 -> ∠ (x +i y) = (- PI/2)%R.
Proof. tacCarg. Qed.


(** 负实数的辐角 *)
Lemma Carg_negR : forall x, x < 0 -> ∠ x = PI.
Proof.
  intros x H. tacCarg.
  unfold Rdiv. rewrite Rmult_0_l. rewrite atan_0. ring.
Qed.

(** 负实数的共轭的辐角 *)
Lemma Carg_conj_negR : forall x, x < 0 -> ∠ (\x) = PI.
Proof.
  intros x H. tacCarg.
  rewrite Ropp_0. unfold Rdiv. rewrite Rmult_0_l. rewrite atan_0. ring.
Qed.

(** 非零且非负实数的共轭的辐角 *)
Lemma Carg_conj_non0_nonnegR : forall z, 
  z <> 0 -> (~(Cre z < 0 /\ Cim z = 0)) ->
  ∠ (\z) = ∠ z.
Proof.
  intros x H. tacCarg. all: rewrite Ropp_0; auto.
Qed.


(** 辐角的定义，是多值函数 *)
Definition CArg (c : C) : Z -> R := fun k => (∠c + 2 * (IZR k) * PI)%R.

(** 将任意角度规范化在主辐角的范围内，即 [-π,π) 
步骤：
  0) r1 ∈ (-∞, +∞)
  1) r2 = r1 / 2π
  2) z1 = floor r2
  3) r3 = r1 - z1 * 2π, r3 ∈ [0, 2π)
  4) r4 = r3 - π, r4 ∈ [-π,π)
*)
Definition CargNorm (theta : R) : R :=
  let r1 : R := theta in
  let r2 : R := (r1 / (2*PI))%R in
  let z1 : Z := R2Z_floor r2 in
  let r3 : R := (r1 - (Z2R z1) * 2 * PI)%R in
    r3 - PI.

(** 定义辅角之间的等价关系：辅角规范化后相等的角 *)
Definition CArgeq (theta1 theta2 : R) : Prop := CargNorm theta1 = CargNorm theta2.
Infix "∠=" := (CArgeq) (at level 70) : C_scope.

Lemma CargNorm_range_left : forall r : R, - PI <= CargNorm r.
Proof.
  intros. unfold CargNorm.
  assert (0 <= r - Z2R (R2Z_floor (r / (2 * PI))) * 2 * PI); ra.
  rewrite Rmult_assoc.
  remember (2 * PI)%R as a.
  remember (Z2R (R2Z_floor (r / a))) as b.
  assert (b <= (r / a)%R).
  - rewrite Heqb.
    apply Z2R_R2Z_floor_le.
  - assert (0 < a).
    { rewrite Heqa. apply mult_PI_gt0; ra. }
    apply Rmult_le_compat_r with (r:=a) in H; auto with R.
    unfold Rdiv in H. rewrite Rmult_assoc in H.
    rewrite Rinv_l in H; ra.
Qed.

Lemma CargNorm_range_right : forall r : R, CargNorm r < PI.
Proof.
  intros. unfold CargNorm.
  assert (r - Z2R (R2Z_floor (r / (2 * PI))) * (2 * PI) < (2 * PI)); ra.
  remember (2 * PI)%R as a.
  remember (Z2R (R2Z_floor (r / a))) as b.
  assert (b * a > r - a); ra.
  assert (0 < a).
  { rewrite Heqa. apply mult_PI_gt0; ra. }
  assert (b > r / a - 1)%R.
  { rewrite Heqb. apply Rlt_gt. apply Z2R_R2Z_floor_gt. }
  (* 自动化能力还是太弱，这类问题还要手动证？？*)
  apply Rmult_gt_compat_r with (r:=a) in H0; auto.
  ring_simplify in H0.
  replace (a * (r / a))%R with r in H0; auto. field. auto with R.
Qed.

Lemma CargNorm_range : forall r : R, (- PI) <= CargNorm r < PI.
Proof.
  intros. split.
  apply CargNorm_range_left.
  apply CargNorm_range_right.
Qed.

(** 非零复数 -> 实部等于模乘以辐角余弦 *)
Lemma Cre_eq_mul_norm_cos_arg : forall z : C, z <> 0 -> 
  Cre z = (|z| * cos(∠z))%R.
Proof.
  intros [x y] H; unfold Cnorm,Cnorm2,Carg; simpl.
  destruct Req_EM_T.
  - subst; autorewrite with R.
    destruct Rcase_abs; autorewrite with R; auto.
  - destruct Rcase_abs; autorewrite with R; auto.
    + replace 
      (cos (if Rcase_abs y then atan (y / x) - PI else atan (y / x) + PI))%R
      with (- cos (atan (y / x)))%R.
      * rewrite cos_atan.
        (* x = sqrt(x^2+y^2) * (-1 / sqrt(1 + (y/x)^2) *)
        unfold Rdiv at 1. rewrite Rinv_sqrt_plus_1_sqr_div_a_b; auto.
        replace (Rabs x) with (- x)%R; try field.
        { autorewrite with R. field. auto with R. }
        { rewrite Rabs_left; auto. }
      * destruct Rcase_abs; autorewrite with R; auto.
    + rewrite cos_atan.
      unfold Rdiv at 1. rewrite Rinv_sqrt_plus_1_sqr_div_a_b; auto.
      replace (Rabs x) with (x)%R; try field.
      { autorewrite with R. field. auto with R. }
      { rewrite Rabs_right; auto. }
Qed.

(** 非零复数 -> 虚部等于模乘以辐角正弦 *)
Lemma Cim_eq_mul_norm_sin_arg : forall z : C, z <> 0 -> 
  Cim z = (|z| * sin(∠z))%R.
Proof.
  intros [x y] H; unfold Cnorm,Cnorm2,Carg; simpl.
  destruct Req_EM_T.
  - subst; autorewrite with R.
    destruct Rcase_abs; autorewrite with R; auto with R.
    assert (Rabs y = -y)%R; auto with R. ra.
  - destruct Rcase_abs; autorewrite with R; auto.
    + replace 
      (sin (if Rcase_abs y then atan (y / x) - PI else atan (y / x) + PI))%R
      with (- sin (atan (y / x)))%R.
      * rewrite sin_atan.
        (* x = sqrt(x^2+y^2) * (-1 / sqrt(1 + (y/x)^2) *)
        unfold Rdiv at 1. rewrite Rinv_sqrt_plus_1_sqr_div_a_b; auto.
        autorewrite with R.
        replace (Rabs x) with (- x)%R; try field; auto with R.
      * destruct Rcase_abs; autorewrite with R; auto with R.
    + rewrite sin_atan.
      unfold Rdiv at 1. rewrite Rinv_sqrt_plus_1_sqr_div_a_b; auto.
      autorewrite with R.
      replace (Rabs x) with (x)%R; try field; auto with R.
Qed.

(** 非零复数 -> 辐角余弦等于实部除以模 *)
Lemma cos_Carg_eq_div_cre_norm : forall z : C, z <> 0 ->
  cos(∠z) = (Cre z / |z|)%R.
Proof.
  intros. rewrite Cre_eq_mul_norm_cos_arg; auto. field.
  apply Cneq0_iff_norm_neq0; auto.
Qed.

(** 非零复数 -> 辐角正弦等于虚部除以模 *)
Lemma sin_Carg_eq_div_cim_norm : forall z : C, z <> 0 ->
  sin(∠z) = (Cim z / |z|)%R.
Proof.
  intros. rewrite Cim_eq_mul_norm_sin_arg; auto. field.
  apply Cneq0_iff_norm_neq0; auto.
Qed.


(* --------------------------------------------------------------------- *)
(** *** 1.2.2 复数模的三角不等式 *)

(** 实部的绝对值小于等于模 *)
Lemma Cre_le_norm : forall z, Rabs (Cre z) <= |z|.
Proof.
  intros [x y]; unfold Cnorm, Cnorm2; simpl.
  rewrite <- sqrt_Rsqr_abs.
  apply sqrt_le_1_alt.
  apply Rle_trans with (x²+0)%R. intuition.
  apply Rplus_le_compat_l. auto with R.
Qed.

(** 虚部的绝对值小于等于模 *)
Lemma Cim_le_norm : forall z, Rabs (Cim z) <= |z|.
Proof.
  intros [x y]; unfold Cnorm, Cnorm2; simpl.
  rewrite <- sqrt_Rsqr_abs.
  apply sqrt_le_1_alt.
  apply Rle_trans with (0 + y²)%R. intuition.
  apply Rplus_le_compat_r. auto with R.
Qed.

(** 模小于等于实部和虚部绝对值之和 *)
Lemma Cnorm_le_plus_cre_cim : forall z : C, |z| <= Rabs (Cre z) + Rabs (Cim z).
Proof.
  intros [x y]; unfold Cnorm, Cnorm2; simpl.
  apply Rsqr_incr_0_var.
  - rewrite Rsqr_sqrt; try ra.
    ring_simplify.
    autorewrite with R.
    rewrite <- ?Rsqr_abs.
    rewrite ?xx_Rsqr.
    ring_simplify.
    assert (0 <= 2 * Rabs x * Rabs y); ra.
    assert (0 <= Rabs x); auto with R.
    assert (0 <= Rabs y); auto with R. ra.
  - apply Rle_trans with (Rabs (x + y)); auto with R.
    apply Rabs_triang.
Qed.

(** 该不等式被多处使用，所以预先证明。编号为1x，x从0开始 *)
Lemma R_neq10 : forall x1 x2 y1 y2 : R,
  x1 * x2 + y1 * y2 <= sqrt (x1 * x1 + y1 * y1) * sqrt (x2 * x2 + y2 * y2).
Proof.
  intros.
  destruct (Rcase_abs (x1*x2+y1*y2)).
  + apply Rle_trans with (r2:=0); try lra.
    apply Rmult_le_pos; auto with R.
  + apply Rsqr_incr_0; auto with R.
    autorewrite with R; auto with R.
    unfold Rsqr in *. ring_simplify.
    (* 分别消去最左端、最右端 *)
    rewrite ?Rplus_assoc; apply Rplus_le_compat_l.
    rewrite <- ?Rplus_assoc; apply Rplus_le_compat_r.
    remember (x1 * y2)%R as a.
    remember (x2 * y1)%R as b.
    replace (2 * x1 * x2 * y1 * y2)%R with (2 * a * b)%R by ra.
    replace (x1 ^ 2 * y2 ^ 2)%R with (a * a)%R by ra.
    replace (x2 ^ 2 * y1 ^ 2)%R with (b * b)%R by ra.
    autorewrite with R. auto with R.
Qed.

(** 该不等式被多处使用，所以预先证明。编号为1x，x从0开始 *)
Lemma R_neq11 : forall x1 x2 y1 y2 : R,
  -(x1 * x2 + y1 * y2) <= sqrt (x1 * x1 + y1 * y1) * sqrt (x2 * x2 + y2 * y2).
Proof.
  intros.
  destruct (Rcase_abs (x1*x2+y1*y2)).
  + autorewrite with R.
    rewrite <- sqrt_mult; auto with R.
    apply Rsqr_incr_0; auto with R; try nra.
    rewrite Rsqr_sqrt; try ra.
    ring_simplify.
    (* 分别消去最左端、最右端 *)
    rewrite ?Rplus_assoc; apply Rplus_le_compat_l.
    rewrite <- ?Rplus_assoc; apply Rplus_le_compat_r.
    remember (x1 * y2)%R as a.
    remember (x2 * y1)%R as b.
    replace (2 * x1 * x2 * y1 * y2)%R with (2 * a * b)%R by ra.
    replace (x1 ^ 2 * y2 ^ 2)%R with (a * a)%R by ra.
    replace (x2 ^ 2 * y1 ^ 2)%R with (b * b)%R by ra.
    autorewrite with R. auto with R.
  + apply Rle_trans with (r2:=0); try lra.
    apply Rmult_le_pos; auto with R.
Qed.

(** 和的模小于等于模的和 *)
Lemma Cnorm_add_le_Cadd_norm : forall z1 z2 : C, |z1 + z2| <= |z1| + |z2|.
Proof.
  intros [x1 y1] [x2 y2]. unfold Cnorm,Cnorm2. simpl.
  apply Rsqr_incr_0; auto with R.
  rewrite ?Rsqr_plus,?Rsqr_sqrt; auto with R.
  ring_simplify.
  replace (x1 ^ 2 + 2 * x1 * x2 + x2 ^ 2 + y1 ^ 2 + 2 * y1 * y2 + y2 ^ 2)%R
  with (x1 ^ 2 + x2 ^ 2 + y1 ^ 2 + y2 ^ 2 + 2 * x1 * x2 + 2 * y1 * y2)%R;
  try ring.
  remember (x1 ^ 2 + x2 ^ 2 + y1 ^ 2 + y2 ^ 2)%R.
  rewrite ?Rplus_assoc. apply Rplus_le_compat_l.
  replace (2 * x1 * x2 + 2 * y1 * y2)%R
  with (2 * (x1 * x2 + y1 * y2))%R; try ring.
  rewrite ?Rmult_assoc. apply Rmult_le_compat_l; try lra.
  apply R_neq10.
Qed.

(** 和的模大于等于模的差 *)
Lemma Cnorm_add_ge_Csub_norm : forall z1 z2 : C, 
  Rabs (|z1| - |z2|) <= |z1 + z2|.
Proof.
  intros [x1 y1] [x2 y2]. unfold Cnorm,Cnorm2. simpl.
  apply Rsqr_incr_0; auto with R.
  rewrite <- Rsqr_abs.
  rewrite ?Rsqr_minus,?Rsqr_plus,?Rsqr_sqrt; auto with R.
  ring_simplify.
  replace (x1 ^ 2 + 2 * x1 * x2 + y1 ^ 2 + 2 * y1 * y2 + x2 ^ 2 + y2 ^ 2)%R
  with ((x1 ^ 2 + y1 ^ 2 + x2 ^ 2 + y2 ^ 2) + (2 * (x1 * x2 + y1 * y2)))%R;
  try ring.
  remember (x1 ^ 2 + y1 ^ 2 + x2 ^ 2 + y2 ^ 2)%R. unfold Rminus.
  apply Rplus_le_compat_l.
  replace (2 * (x1 * x2 + y1 * y2))%R
  with (- (2 * (- (x1 * x2 + y1 * y2))))%R; try lra.
  apply Ropp_le_contravar.
  rewrite Rmult_assoc. apply Rmult_le_compat_l; try lra.
  apply R_neq11.
Qed.


(** 差的模大于等于模的差的绝对值 *)
Lemma Cnorm_sub_le_Csub_norm : forall z1 z2 : C, 
  Rabs (|z1| - |z2|) <= |z1 - z2|.
Proof.
  intros [x1 y1] [x2 y2]. unfold Cnorm,Cnorm2. simpl.
  apply Rsqr_incr_0; auto with R.
  rewrite <- Rsqr_abs.
  rewrite ?Rsqr_minus,?Rsqr_sqrt; auto with R.
  ring_simplify.
  replace (x1 ^ 2 - 2 * x1 * x2 + y1 ^ 2 - 2 * y1 * y2 + x2 ^ 2 + y2 ^ 2)%R
  with (x1 ^ 2 + y1 ^ 2 + x2 ^ 2 + y2 ^ 2 - 2 * x1 * x2 - 2 * y1 * y2)%R;
  try ring.
  remember (x1 ^ 2 + y1 ^ 2 + x2 ^ 2 + y2 ^ 2)%R. unfold Rminus.
  rewrite ?Rplus_assoc. apply Rplus_le_compat_l.
  replace (-(2 * x1 * x2) + - (2 * y1 * y2))%R
  with ((-2) * (x1 * x2 + y1 * y2))%R; try ring.
  replace (- (2 * sqrt (x1 * x1 + y1 * y1) * sqrt (x2 * x2 + y2 * y2)))%R 
  with ((-2) * (sqrt (x1 * x1 + y1 * y1) * sqrt (x2 * x2 + y2*y2)))%R; try ring.
  apply Rmult_le_compat_neg_l; try lra.
  apply R_neq10.
Qed.

(** 差的模大于等于模的差 *)
Lemma Cnorm_sub_ge_Csub_norm : forall z1 z2 : C, 
  Rabs (|z1| - |z2|) <= |z1 - z2|.
Proof.
  intros [x1 y1] [x2 y2]. unfold Cnorm,Cnorm2. simpl.
  apply Rsqr_incr_0; auto with R.
  rewrite <- Rsqr_abs.
  rewrite ?Rsqr_minus,?Rsqr_plus,?Rsqr_sqrt; auto with R.
  ring_simplify.
  replace (x1 ^ 2 - 2 * x1 * x2 + y1 ^ 2 - 2 * y1 * y2 + x2 ^ 2 + y2 ^ 2)%R
  with ((x1 ^ 2 + y1 ^ 2 + x2 ^ 2 + y2 ^ 2) - (2 * (x1 * x2 + y1 * y2)))%R;
  try ring.
  remember (x1 ^ 2 + y1 ^ 2 + x2 ^ 2 + y2 ^ 2)%R. unfold Rminus.
  apply Rplus_le_compat_l.
  apply Ropp_le_contravar.
  rewrite Rmult_assoc. apply Rmult_le_compat_l; try lra.
  apply R_neq10.
Qed.


(* --------------------------------------------------------------------- *)
(** *** 1.2.3 复数的三角表示 *)

(** 复数三角表示的定义 *)
(* 注意:
   1. Record指定了字段的名称，Inductive不关心字段名称。二者本质上是相同的
   2. 三角表示只定义了非零复数，复数0并未定义。
      若规定模 >0 后，则排除了复数0，所以，复数0从 C 到 Ctrigo 无法转换
      若规定模 >=0，则包含复数0。若模长恰为0，则任意辅角都对应同一个复数。
   3. 所以，复数三角表示的相等，可以用一个等价关系来表达。
 *)
Inductive Ctrigo := mkCtrigo (r θ : R) (H1 : 0 <= r).

(** 复数三角表示相等：要么都是零向量，要么模长和辅角同时相等 *)
Definition Ctrigo_eq (c1 c2 : Ctrigo) : Prop :=
  let (r1,t1,_) := c1 in
  let (r2,t2,_) := c2 in
  if ((r1 =? 0) && (r2 =? 0)) then True
  else (r1 = r2 /\ t1 ∠= t2).
  
(** 复数三角表示 -> 复数(坐标表示) *)
Definition Ctrigo2C (c : Ctrigo) : C :=
  let '(mkCtrigo r t _) := c in
    (r * cos t) +i (r * sin t).

(** 复数(坐标表示) -> 复数三角表示 *)
(* 注意，这里的定义，与书上的定义不同，书上用CArg，而不是主辐角，所以有无穷多个值 *)
Definition C2Ctrigo (c : C) : Ctrigo :=
  mkCtrigo (|c|) (∠c) (Cnorm_ge0 c).

(** 复数三角表示的模 *)
Lemma Cnorm_trigo (c : Ctrigo) : let (r,t,_) := c in |Ctrigo2C c| = r.
Proof.
  destruct c as [r t]. cbn. unfold Cnorm,Cnorm2.
  replace (r * cos t * (r * cos t) + r * sin t * (r * sin t))%R
  with ((r * r) * ((cos t)² + (sin t)²))%R.
  - rewrite cos2_sin2. autorewrite with R. auto with R.
  - unfold Rsqr. ring.
Qed.

Lemma Rmult_lt_0_reg : forall r1 r2 : R, 0 <= r1 -> r1 * r2 < 0 -> r2 < 0.
Proof. intros. ra. Qed.

Lemma cos_eq0 : forall (k : Z),
    cos (PI / 2 + (IZR k) * PI)%R = 0.
Proof.
  Admitted.

(** CargNorm 以 2π 为周期 *)
Theorem CargNorm_period : forall (t:R) (k:Z),
    CargNorm (t + IZR k * 2 * PI)%R = CargNorm t.
Admitted.

(** 在 [-π,π) 之间的角度，CargNorm 作用后不变 *)
Theorem CargNorm_range_unique : forall (t:R), - PI <= t < PI -> CargNorm t = t.
Admitted.

(** ToDo: 一个发现，Coq中对这些三角函数的周期性普遍都没有证明。至少默认的库中
    我找不到相关引理。*)

(** tan 以 2π 为周期 *)
Theorem tan_period : forall (t:R) (k:Z),
    tan (t + IZR k * 2 * PI)%R = tan t.
Admitted.


(** 复数三角表示时，若模长为证，则其辅角满足如下关系式 *)
Lemma Carg_trigo (c : Ctrigo) : let (r,t,_) := c in 
  0 < r -> ∠ (Ctrigo2C c) = CargNorm t.
Proof.
  destruct c as [r t H]; intros.
  tacCarg; subst; ra.
  - assert (sin t < 0); ra.
    assert (cos t = 0); ra.
    assert (forall t, cos t = 0 -> sin t < 0 ->
                 exists k : Z,
                   let T : R := ((IZR k) * 2 * PI)%R in
                   t = (- (PI / 2) + T)%R).
    admit.
    specialize (H3 t H2 H1). destruct H3.
    rewrite H3. rewrite CargNorm_period.
    rewrite CargNorm_range_unique; auto with R.
    assert (PI > 0); auto with R; ra.
  - assert (cos t = 0); ra.
    assert (sin t > 0).
    { assert (sin t <> 0). intro. destruct (cos_sin_0 t); auto. ra. }
    assert (forall t, cos t = 0 -> sin t > 0 ->
                 exists k : Z,
                   let T : R := ((IZR k) * 2 * PI)%R in
                   t = ((PI / 2) + T)%R).
    admit.
    specialize (H3 t H1 H2). destruct H3.
    rewrite H3. rewrite CargNorm_period.
    rewrite CargNorm_range_unique; auto with R.
    assert (PI > 0); auto with R; ra.
  - assert (cos t < 0); ra.
    assert (sin t < 0); ra.
    replace (r * sin t / (r * cos t))%R with (sin t / cos t)%R; try field;ra.
    replace (sin t / cos t)%R with (tan t); auto with R.
    (* 可知，此时 t 在 [-π,π) + T 之间 *)
    assert (forall t, cos t < 0 -> sin t < 0 ->
                 exists k : Z,
                   let T : R := ((IZR k) * 2 * PI)%R in
                   (- PI + T < t < T)%R).
    admit.
    specialize (H3 t H1 H2). destruct H3. simpl in H3.
    (* 然而，这一段中，tan 的行为还要分另种情况 *)
    (* 先使用 tan x 的周期性 *)
    Abort.
  (* 也算展开太多，细节太繁琐了。利用 Carg 的性质也许简洁 *)

  

(** 例 1.2 *)
Goal Ctrigo_eq
  (C2Ctrigo (1 +i 1))
  (mkCtrigo (sqrt 2) (PI/4) (sqrt_pos 2)).
Proof.
  tacCarg. unfold CArgeq.
  assert (|1 +i 1| <> 0).
  { intro. cbv in H. apply sqrt_eq_0 in H; ra. }
  apply Reqb_neq in H. rewrite H. simpl. split.
  + cbv. f_equal. ring.
  + replace (1 / 1)%R with 1; ra. rewrite atan_1. f_equal.
Qed.

(** 例 1.3 *)
Goal Ctrigo_eq
  (C2Ctrigo ((-1) +i (-3)))
  (mkCtrigo (sqrt 10) (atan 3 - PI) (sqrt_pos 10)).
Proof.
  tacCarg. unfold CArgeq.
  assert (|(-1) +i (-3)| <> 0).
  { intro. cbv in H. apply sqrt_eq_0 in H; ra. }
  apply Reqb_neq in H. rewrite H. simpl. split.
  + cbv. f_equal. ring.
  + replace (-3 / -1)%R with 3; ra.
Qed.

(* 以上，这类题目证明还是很繁琐，因实数构造问题
 这个例子也看出了大量的自动化的需求，比如带有 sqrt, cos, sin 等的运算，
 比如 Rsqr 2 与 sqr 2 的问题（它们混在一起）。
 能将这个证明简化到几步完成，而且还比较通用，也是个不错的课题。 *)


(** 例1.4，已知一个复数的三角表示，求该复数的倒数的三角表示。
这里仅证明，因为实数在Coq中的复杂构造方式，所以手动计算的结果Coq不一定能自动给出 *)
(* Goal forall r t, 
  let z := mkCtrigo r t in
  let z1 := Ctrigo2C z in
  let z2 := /z1 in
  let z3 := C2Ctrigo z2 in
    z1 <> 0 -> z3 = mkCtrigo (1/r) (-t).
Proof.
  intros. unfold z3,z2,z1.
  (* 方法一：最笨的方法是，直接展开，按照代数的方法一步步凑 *)
(*   cbn. unfold C2Ctrigo. f_equal. *)
  (* 方法二：按照书上的证明思路，利用数学推导和一些改写引理来做 *)
  rewrite Cinv_eq_conjDivNorm2; auto.
  Search (mkCtrigo).
   2:{ auto.
  let z2 :
    (1/z)   let r  z =  a := 0 in a > 0.
 *)


(* (** |z^n| = |z|^n *)
Lemma Cnorm_pow : forall z n, |z ^ n| = ((|z|) ^ n)%R.
Proof.
intros z n; induction n.
 simpl; apply Cnorm_C1.
 simpl; rewrite Cnorm_Cmult, IHn; reflexivity.
Qed. *)
