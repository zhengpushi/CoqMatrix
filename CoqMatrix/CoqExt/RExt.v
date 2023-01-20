(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Coq.Reals.
  author    : ZhengPu Shi
  date      : 2021.05
  
  remark    :
  1. possible reason of "field" failure
    a. notation "/", need unfold Rdiv first.
    b. unknown variable name, need be rewrite first.
  2. why need this library?
    (1). lots of properties are lack in standard library.
    (2). more automation, especially inequality.
    (3). We want to solve any problem of equality or inequality in one step.
  3. why auto fail? and how to better naming a term?
    (1). use two lemmas like A -> B and B -> A instead of A <-> B
    (2). x * x and x² are mixed, and x² is defined as x * x, and Coq Standard 
      Library prefer x², so we'd better choose x². But, notice that we should 
      rewrie x² to x * x before using ring or field, it's a bit annoying.
    (3). 1 and R1 are mixed, and 1 is (IZR (Zpos xH)), and will be reduced to R1
      finally, and Coq Standard Library prefer 1, so we choose 1 as well.
    (4). x - y and x + (-y) is same, but we prefer x - y.
    (5). x / y and x * (-y), we prefer x / y as well.
*)


Require Export BasicConfig.
Require Import HierarchySetoid.

Require Export ZExt.
Require Export Reals.
Open Scope R_scope.

Require Export Psatz.
Require Export Lra.


(* ######################################################################### *)
(** * 标准库 Reals 的定制：提示库 R，定义 Opaque，自动求解器 *)

(** autounfold 数据库 *)
Global Hint Unfold
  Rminus        (* a - b = a + - b *)
  Rdiv          (* a / b = a * / b *)
  Rsqr          (* r² = r * r *)
  : R.

(** autorewrite 数据库，用于等式变换 *)
Global Hint Rewrite
  (* Abs *)
  Rabs_Ropp           (* Rabs (-x) = Rabs x *)
  Rabs_Rabsolu        (* Rabs (Rabs x) = Rabs x *)
  (* 加法 *)
  Rplus_0_l           (* 0 + r = r *)
  Rplus_0_r           (* r + 0 = r *)
  (* 加法逆 *)
  Ropp_0              (* - 0 = 0 *)
  Rminus_0_r          (* r - 0 = r *)
  Ropp_involutive     (* - - r = r *)
  Rplus_opp_r         (* r + - r = 0 *)
  Rplus_opp_l         (* - r + r = 0 *)
  (* 乘法 *)
  Rsqr_0              (* 0² = 0 *)
  Rsqr_0              (* 1² = 1 *)
  Rmult_0_l           (* 0 * r = 0 *)
  Rmult_0_r           (* r * 0 = 0 *)
  Rmult_1_l           (* 1 * r = r *)
  Rmult_1_r           (* r * 1 = r *)
(*   Ropp_mult_distr_r_reverse     (* r1 * - r2 = - (r1 * r2) *) *)
(*   Ropp_mult_distr_l_reverse     (* - r1 * r2 = - (r1 * r2) *) *)
  (* 整数幂 *)
  pow1                (* 1 ^ n = 1 *)
  pow_O               (* x ^ 0 = 1 *)
  pow_1               (* x ^ 1 = x *)
  (* 平方和 *)
  Rsqr_mult           (* (x * y)² = x² * y² *)
  (* 平方根 *)
  sqrt_Rsqr_abs       (* (sqrt x²) = Rabs x *)
  (* Rsqr_sqrt           (* 0 <= x -> (sqrt x)² = x *) *)
  (* sqrt_Rsqr           (* 0 <= x -> sqrt x² = x *) *)
  sqrt_0              (* sqrt 0 = 0 *)
  : R.

(** auto 数据库，用于不等式的解决 *)
Global Hint Resolve
  (* 等式 *)
  eq_sym              (* a = b -> b = a *)
  sqrt_0              (* sqrt 0 = 0 *)
  Rsqr_eq_0           (* x² = 0 -> x = 0 *)
(*   sqrt_sqrt           (* 0 <= x -> sqrt x * sqrt x = x *) *)
  Rsqr_sqrt           (* 0 <= x -> (sqrt x)² = x *)
  sqrt_Rsqr           (* 0 <= x -> sqrt x² = x *)
  sin2_cos2           (* (sin x)² + (cos x)² = 1 *)

  (* 普通不等式 *)
  Rlt_0_1             (* 0 < 1 *)
  PI_RGT_0            (* PI > 0 *)
  Rabs_pos            (* 0 <= Rabs x *)
  Rabs_no_R0          (* r <> 0 -> Rabs r <> 0 *)
  sqrt_pos            (* 0 <= sqrt x *)
  Rle_0_sqr           (* 0 <= r² *)
(*   Rsqr_inj            (* 0 <= x -> 0 <= y -> x² = y² -> x = y *) *)
  Rinv_0_lt_compat    (* 0 < r -> 0 < / r *)
  
  (* 形如 0 <= r1 + r2 *)
  Rplus_le_le_0_compat  (* 0 <= r1 -> 0 <= r2 -> 0 <= r1 + r2 *)
  Rplus_lt_le_0_compat  (* 0 < r1 -> 0 <= r2 -> 0 < r1 + r2 *)
  Rplus_le_lt_0_compat  (* 0 <= r1 -> 0 < r2 -> 0 < r1 + r2 *)
  Rplus_lt_0_compat   (* 0 < r1 -> 0 < r2 -> 0 < r1 + r2 *)

  (* 形如 0 <= r1 * r2 *)
  Rmult_lt_0_compat   (* 0 < r1 -> 0 < r2 -> 0 < r1 * r2 *)
  Rle_0_sqr           (* 0 <= x² *)
  Rsqr_pos_lt         (* x <> 0 -> 0 < x² *)

  (* 形如 r1 <= r2 *)
  Rlt_gt              (* r1 < r2 -> r2 > r1 *)  (* THIS IS ALWAYS NEED! *)
  Rgt_lt              (* r1 > r2 -> r2 < r1 *)  (* THIS ONE, slow but useful *)
  Rge_le              (* r1 >= r2 -> r2 <= r1 *)
  Rle_ge              (* r1 <= r2 -> r2 >= r1 *)
  Rlt_le              (* r1 < r2 -> r1 <= r2 *)
  Rsqr_pos_lt         (* x <> 0 -> 0 < x² *)

  (* 形如 r1 <> r2 *)
  Rgt_not_eq          (* r1 > r2 -> r1 <> r2 *)
  Rlt_not_eq          (* r1 < r2 -> r1 <> r2 *)

  (* 含平方根 *)
  sqrt_lt_R0          (* 0 < x -> 0 < sqrt x *)
  sqrt_inj            (* 0 <= x -> 0 <= y -> sqrt x = sqrt y -> x = y *)
  : R.


(** Control Opaque / Transparent of the definitions *)
Global Opaque 
  PI 
  sqrt
  Rpower 
  sin 
  cos
  tan
  asin
  atan
  acos
.

(** Coq对等式和不等式自动证明的支持情况
参考：https://coq.inria.fr/distrib/current/refman/addendum/micromega.html
Micromega: 通过有序环(ordered ring)结构上的算术目标的求解器。
1. Import Psatz 来访问求解在 Q,R,Z,nat,N 上的算术目标的各种策略。
   若想单独访问，如整数(含Z,nat,N)则用 Lia, 有理数和实数分别用 Lqa, Lra。
2. 各个策略的介绍
lia 算术决策过程 (整数)(线性)
nia 算术决策过程 (整数)(非线性,不完备的)
lra 算术决策过程 (实数、有理数)(线性)
nra 算术决策过程 (实数、有理数)(非线性,不完备的)
psatz D n 算术决策过程(非线性，不完备的)
  其中，D是Z、Q或R，n是可选的整数，表示搜索深度限制。
3. 这些策略能解决的问题
解决参数为“可在域D∈{Z,Q,R}上解释的原子算术表达式”的命题公式，公式的语法为：
p ::= c | x | -p | p+p | p-p | p*p | p^n
A ::= p=p | p>p | p<p | p<=p | p>=p
F ::= A | P | True | False | F/\F | F\/F | F<->F | F->F | ~F | F=F
其中，
c是D中的常数
x是D中的数值变量
-,+,* 分别是 减法、加法和乘法
p^n 是自然数常数幂
F 被解释为Prop 或 bool。
继续解释....
(1) 当 F 解释为 bool 时，布尔操作符是 &&,||,eqb,implb,negb, A也通过布尔来解释，
    比如，对于Z，有 Z.eqb,Z.gtb,Z.ltb,Z.geb,Z.leb 等
(2) 对于Q，使用有理数相等==，而不是Leibniz相等=。
(3) c的范围：对于Z和Q，是全部可能的取值；对于R，识别如下的表达式作为常数
c ::= R0 | R1 | Rmult c c | Rplus c c | Rminus c c | IZR z | Q2R q | Rdiv c c
      | Rinv c
 *)
Section TEST_psatz.
  Goal forall x y, x ^ 2 + y * y >= x * y.
    intros.
    (* psatz R 1. (* require external tool CSDP *) *)
    nra.
  Qed.

End TEST_psatz.

(** arithmetric on reals : lra + nra *)
Ltac ra :=
  intros; unfold Rsqr in *; try lra; try nra.


(* ######################################################################### *)
(** * 补充“实数”有关的性质 *)


(* ======================================================================= *)
(** ** Rsqr、Rpow2与x*x 的自动处理 *)

(** 注意，Coq中平方和有多种表示方式：
    x * x，是 Rmult x x 的 Notation
    x ^ 2, 是 pow x 2 的 Notation
    x²   , 是 Rsqr x 的 Notation，定义为 x * x
    而Coq库中，到底使用哪个定义来表示平方和？引理的丰富程度如何？用Search检索
        x * x，9个
        x ^ 2, 14个
        x², 100多个
    所以，以x²为主，其余形式转换为这种形式，缺失引理补充。

    不过，另一个问题是，lra 策略在 x * x 和 pow x 2 上工作，而在 x² 上不工作，
    所以，在 try lra 时，改用 try (unfold Rsqr in *; lra)
    另外，ring 和 field 也需要展开 Rsqr。

    总结，有两种典型情形：
    1. 使用ring、field、lra等策略时：unfold Rsqr in *; ring.
    2. 其他情形：autorewrit with R; auto with R.
要
 *)

(** We always prefer x², an exception is when using ring or field tactic. *)
Lemma xx_Rsqr x : x * x = x².
Proof.
  auto.
Qed.
Global Hint Rewrite xx_Rsqr : R.

(** r ^ 2 = r² *)
Lemma Rpow2_Rsqr r : r ^ 2 = r².
Proof.
  ra.
Qed.
Global Hint Rewrite Rpow2_Rsqr : R.


(* ======================================================================= *)
(** ** R1 and 1 *)

(** We always prefer 1 *)
Lemma R1_eq_1 : R1 = 1.
Proof.
  auto.
Qed.
Global Hint Rewrite R1_eq_1 : R.

Lemma Rsqr_1 : 1² = 1.
Proof.
  ra.
Qed.
Global Hint Rewrite Rsqr_1 : R.
Global Hint Resolve Rsqr_1 : R.

(** /1 = 1 *)
Global Hint Rewrite Rinv_1 : R.
Global Hint Resolve Rinv_1 : R.

Lemma zero_le_1 : 0 <= 1.
Proof.
  auto with R.
Qed.
Global Hint Resolve zero_le_1 : R.

Lemma zero_neq_1 : 0 <> 1.
Proof.
  auto with R.
Qed.
Global Hint Resolve zero_neq_1 : R.

Module TEST_R1_and_1.
  Goal 1 = R1. auto with R. Qed.
  Goal R1² = 1. auto with R. Qed.
  Goal 1² = R1. auto with R. Qed.
  Goal /R1 = R1. auto with R. Qed.
  Goal /R1 = 1. auto with R. Qed.
  Goal /1 = R1. auto with R. Qed.
  Goal 0 <= R1. auto with R. Qed.
End TEST_R1_and_1.


(* ======================================================================= *)
(** ** 减号的消去 *)

Lemma Rsub_opp r1 r2 : r1 - (- r2) = r1 + r2.
Proof.
  ring.
Qed.
Global Hint Rewrite Rsub_opp : R.           (* r1 - (- r2) = r1 + r2 *)


(* ======================================================================= *)
(** ** “平方和”的性质 *)

Lemma Rle_0_xx : forall r, 0 <= r * r.
Proof.
  ra.
Qed.

(** 两个实数的平方和非负 *)
Lemma Rplus_sqr_ge0 : forall r1 r2 : R, 0 <= r1² + r2².
Proof.
  ra.
Qed.

(** 两个实数的平方为正，iff，不全为0 *)
Lemma Rplus_sqr_gt0 : forall r1 r2 : R, 0 < r1² + r2² <-> 
  (r1 <> 0 \/ r2 <> 0).
Proof.
  ra.
Qed.

(** 平方和为0，则第二个数为0 *)
Lemma Rplus_sqr_eq_0_r : forall r1 r2, r1² + r2² = 0 -> r2 = 0.
Proof.
  ra.
Qed.

(** 实数不等式：2 * a * b <= a² + b² *)
Lemma R_neq1 : forall r1 r2 : R, 2 * r1 * r2 <= r1² + r2².
Proof.
  (* 利用 (a-b)² = a² + b² - 2ab *)
  intros. apply Rge_le. apply Rminus_ge.
  rewrite <- Rsqr_minus. auto with R.
Qed.

(** r1² + r2² = 0 <-> r1 = 0 /\ r2 = 0 *)
Lemma Rplus_sqr_eq0_iff : forall r1 r2, r1² + r2² = 0 <-> r1 = 0 /\ r2 = 0.
Proof.
  ra.
Qed.

(** r1 <> 0 \/ r2 <> 0 <-> r1² + r2² <> 0 *)
Lemma Rplus_sqr_neq0_iff2 : forall r1 r2, r1 <> 0 \/ r2 <> 0 <-> r1² + r2² <> 0.
Proof. ra. Qed.

(** r1*r1 + r2*r2 <> 0 -> 0 < r1*r1 + r2*r2 *)
Lemma Rplus_sqr_sqr_neq0_iff_Rplus_sqr_sqr_gt0 : forall r1 r2 : R,
  r1² + r2² <> 0 <-> 0 < r1² + r2².
Proof. ra. Qed.

(** r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 <-> r1² + r2² + r3² <> 0 *)
Lemma Rplus_sqr_neq0_iff3 : forall r1 r2 r3 : R,
  r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 <-> r1² + r2² + r3² <> 0.
Proof. ra. Qed.

(** r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0 <-> 
    r1² + r2² + r3² + r4² <> 0 *)
Lemma Rplus_sqr_neq0_iff4 : forall r1 r2 r3 r4 : R,
  r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0 <-> r1² + r2² + r3² + r4² <> 0.
Proof. ra. Qed.

Global Hint Resolve
  Rle_0_xx           (* 0 <= x * x *)
  Rplus_sqr_ge0      (* 0 <= r1² + r2² *)
  Rplus_sqr_gt0      (* 0 < r1² + r2² *)
  Rplus_sqr_eq_0_l   (* r1² + r2² = 0 -> r1 = 0 *)
  Rplus_sqr_eq_0_r   (* r1² + r2² = 0 -> r2 = 0 *)
  Rplus_sqr_neq0_iff2 (* r1<>0 \/ r2<>0 <-> r1² + r2²<>0 *)
  Rplus_sqr_neq0_iff3 (* r1,r2,r3, ... *)
  Rplus_sqr_neq0_iff4 (* r1,r2,r3,r4, ... *)
  Rplus_sqr_sqr_neq0_iff_Rplus_sqr_sqr_gt0 (* r1² + r2²<>0 <-> 0 <r1² + r2² *)
  R_neq1              (* 2 * a * b <= a² + b² *)
  : R.

Section test.
  (** r * r = 0 <-> r = 0 *)
  Goal forall r, r * r = 0 <-> r = 0. ra. Qed.
  Goal forall r, r * r <> 0 <-> r <> 0. ra. Qed.
  Goal forall r1 r2 : R, 0 <= r1 * r1 + r2 * r2. ra. Qed.
  Goal forall r1 r2 : R,  r1 <> 0 \/ r2 <> 0 <-> r1 * r1 + r2 * r2 <> 0. ra. Qed.
  Goal forall r1 r2 : R,  r1 * r1 + r2 * r2 <> 0 <-> 0 < r1 * r1 + r2 * r2. ra. Qed.
  Goal forall r1 r2 r3 : R,
      r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 <-> r1 * r1 + r2 * r2 + r3 * r3 <> 0. ra. Qed.
  Goal forall r1 r2 r3 r4 : R,
      r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0 <->
        r1 * r1 + r2 * r2 + r3 * r3 + r4 * r4 <> 0. ra. Qed.
End test.


(* ======================================================================= *)
(** ** “绝对值”的性质 *)

Lemma Rabs_neg_left : forall r, 0 <= r -> Rabs (-r) = r.
Proof.
  intros. rewrite Rabs_Ropp. apply Rabs_right; nra.
Qed.

Lemma Rabs_neg_right : forall r, r < 0 -> Rabs (-r) = -r.
Proof.
  intros. rewrite Rabs_Ropp. apply Rabs_left; nra.
Qed.

Global Hint Resolve
  Rabs_right     (* r >= 0 -> Rabs r = r *)
  Rabs_pos_eq    (* 0 <= r -> Rabs r = r *)
  Rabs_left      (* r < 0 -> Rabs r = - r *)
  Rabs_left1     (* r <= 0 -> Rabs r = - r *)
  Rabs_neg_left  (* 0 <= r -> Rabs (-r) = r *)
  Rabs_neg_right (* r < 0 -> Rabs (-r) = -r *)
  : R.


(* ======================================================================= *)
(** ** “平方根”的性质 *)

Lemma sqrt_square_abs : forall r, sqrt (r * r) = Rabs r.
Proof.
  intros. destruct (Rcase_abs r).
  - replace (r * r) with ((-r) * (-r)) by nra.
    rewrite sqrt_square; try nra. auto with R.
  - rewrite sqrt_square; auto with R.
Qed.

Lemma sqrt_1 : sqrt 1 = 1.
Proof.
  apply Rsqr_inj; autorewrite with R; auto with R.
Qed.

Lemma sqrt_le0_eq_0 : forall r, r <= 0 -> sqrt r = 0.
Proof.
  intros. Transparent sqrt. unfold sqrt. destruct (Rcase_abs r); auto.
  assert (r = 0); try lra. subst. compute. 
  destruct (Rsqrt_exists). destruct a.
  symmetry in H1. auto with R.
Qed.

Lemma sqrt_lt0_eq_0 : forall r, r < 0 -> sqrt r = 0.
Proof.
  intros. apply sqrt_le0_eq_0. auto with R.
Qed.

Lemma le0_imply_sqrt_eq0 : forall (x : R), x < 0 -> sqrt x = 0.
Proof.
  intros. unfold sqrt. destruct (Rcase_abs x); auto.
  (* although, x < 0, x >= 0, all appear, lra fail to solve it. *)
  exfalso. lra.
Qed.

Lemma sqrt_gt0_imply_gt0 : forall (x : R), 0 < sqrt x -> 0 < x.
Proof.
  intros. replace 0 with (sqrt 0) in H; auto with R.
  apply sqrt_lt_0_alt in H; auto.
Qed.

Lemma sqrt_gt0_imply_ge0 : forall (x : R), 0 < sqrt x -> 0 <= x.
Proof.
  intros. apply Rlt_le. apply sqrt_gt0_imply_gt0; auto.
Qed.

Lemma sqrt_eq1_imply_eq1 : forall (x : R), sqrt x = 1 -> x = 1.
Proof.
  intros.
  assert ((sqrt x)² = 1). rewrite H. autounfold with R in *; ring.
  rewrite <- H0.
  apply eq_sym. apply Rsqr_sqrt.
  assert (0 < sqrt x). rewrite H; auto with R.
  apply sqrt_gt0_imply_gt0 in H1. auto with R.
Qed.

(** ( √ r1 * √ r2)^2 = r1 * r2 *)
Lemma Rsqr_sqrt_sqrt r1 r2 : 0 <= r1 -> 0 <= r2 ->
  ((sqrt r1) * (sqrt r2))² = r1 * r2.
Proof.
  destruct (Rcase_abs r1), (Rcase_abs r2); try lra.
  autorewrite with R; auto with R.
  rewrite ?Rsqr_sqrt; auto with R.
Qed.

(** 两个实数的平方和再开根号为零，iff 这两个实数为零 *)
Lemma Rsqrt_plus_sqr_eq0_iff : forall r1 r2 : R,
  sqrt (r1² + r2²) = 0 <-> r1 = 0 /\ r2 = 0.
Proof.
  intros. autorewrite with R. split; intros H.
  - apply sqrt_eq_0 in H.
    + split; eauto with R.
    + apply Rplus_sqr_ge0.
  - destruct H; subst. autorewrite with R; auto with R.
Qed.

(** 两个实数分别开根号后的乘积非负 *)
Lemma Rmult_sqrt_sqrt_ge0 : forall r1 r2 : R, 0 <= (sqrt r1) * (sqrt r2).
Proof.
  intros. apply Rmult_le_pos; auto with R.
Qed.

(** 两个实数分别开根号后的求和非负 *)
Lemma Rplus_sqrt_sqrt_ge0 : forall r1 r2 : R, 0 <= (sqrt r1) + (sqrt r2).
Proof.
  intros. apply Rplus_le_le_0_compat; auto with R.
Qed.

Lemma Rsqr_plus_sqr_neq0_l : forall r1 r2, r1 <> 0 -> sqrt (r1² + r2²) <> 0.
Proof.
  intros. auto 6 with R.
Qed.

Lemma Rsqr_plus_sqr_neq0_r : forall r1 r2, r2 <> 0 -> sqrt (r1² + r2²) <> 0.
Proof.
  intros. auto 6 with R.
Qed.

(** /(sqrt (1+(b/a)²)) = abs(a) / sqrt(a*a + b*b) *)
Lemma Rinv_sqrt_plus_1_sqr_div_a_b (a b : R) : a <> 0 ->
  (/ (sqrt (1+(b/a)²)) = (Rabs a) / sqrt(a*a + b*b)).
Proof.
  intros.
  replace (1 + (b/a)²) with ((a*a + b*b) / ((Rabs a)*(Rabs a))).
  - rewrite sqrt_div_alt.
    + rewrite sqrt_square. 
      * field. split; autorewrite with R; auto 6 with R.
      * auto with R.
    + autorewrite with R; auto with R.
  - unfold Rsqr.
    destruct (Rcase_abs a).
    + replace (Rabs a) with (-a). field; auto. rewrite Rabs_left; auto.
    + replace (Rabs a) with a. field; auto. rewrite Rabs_right; auto.
Qed.

Global Hint Rewrite
  sqrt_square_abs         (* sqrt (r * r) = Rabs r *)
  (* Rsqr_sqrt               (* 0 <= x -> (sqrt x)² = x *) *)
  sqrt_1                  (* sqrt 1 = 1 *)
  Rsqr_sqrt_sqrt          (* ( √ r1 * √ r2)² = r1 * r2 *)
  : R.

Global Hint Resolve
  sqrt_le0_eq_0           (* r <= 0 -> sqrt r = 0 *)
  sqrt_lt0_eq_0           (* r < 0 -> sqrt r = 0 *)
  le0_imply_sqrt_eq0      (* x < 0 -> sqrt x = 0 *)
  sqrt_gt0_imply_gt0      (* 0 < sqrt x -> 0 < x *)
  sqrt_gt0_imply_ge0      (* 0 < sqrt x -> 0 <= x *)
  sqrt_eq1_imply_eq1      (* sqrt x = 1 -> x = 1 *)
  Rsqr_sqrt_sqrt          (* ( √ r1 * √ r2)² = r1 * r2 *)
  Rmult_sqrt_sqrt_ge0     (* 0 <= (sqrt r1) * (sqrt r2) *)
  Rplus_sqrt_sqrt_ge0     (* 0 <= (sqrt r1) + (sqrt r2) *)
  sqrt_square             (* 0 <= x -> sqrt (x * x) = x *)
  Rsqr_plus_sqr_neq0_l    (* r1 <> 0 -> sqrt (r1² + r2²) <> 0 *)
  Rsqr_plus_sqr_neq0_r    (* r2 <> 0 -> sqrt (r1² + r2²) <> 0 *)
  : R.

Section TEST_Rsqrt.
  Goal sqrt R1 = R1. autorewrite with R; auto with R. Qed.
  
End TEST_Rsqrt.


(* ======================================================================= *)
(** ** “三角函数”的性质 *)

(*  sin (- (PI/2)) = -1 *)
Lemma sin_PI2_neg : sin (- (PI/2)) = -1.
Proof.
  rewrite sin_neg. rewrite sin_PI2. auto.
Qed.

(* cos (- (PI/2)) = 0 *)
Lemma cos_PI2_neg : cos (- (PI/2)) = 0.
Proof.
  rewrite cos_neg. apply cos_PI2.
Qed.

(* sin (r + PI) = - (sin r) *)
Lemma sin_plus_PI : forall r, sin (r + PI) = (- (sin r))%R.
Proof.
  apply neg_sin.
Qed.

(* sin (r - PI) = - (sin r) *)
Lemma sin_sub_PI : forall r, sin (r - PI) = (- (sin r))%R.
Proof.
  intros. replace (r - PI)%R with (- (PI - r))%R; try ring.
  rewrite sin_neg. rewrite Rtrigo_facts.sin_pi_minus. auto.
Qed.

(* cos (r + PI) = - (cos r) *)
Lemma cos_plus_PI : forall r, cos (r + PI) = (- (cos r))%R.
Proof.
  apply neg_cos.
Qed.

(* cos (r - PI) = - (cos r) *)
Lemma cos_sub_PI : forall r, cos (r - PI) = (- (cos r))%R.
Proof.
  intros. replace (r - PI)%R with (- (PI - r))%R; try ring.
  rewrite cos_neg. apply Rtrigo_facts.cos_pi_minus.
Qed.

(** 余弦平方加上正弦平方等于1 *)
Lemma cos2_sin2: forall x : R, (cos x)² + (sin x)² = 1.
Proof.
  intros. rewrite Rplus_comm. apply sin2_cos2.
Qed.

Global Hint Rewrite
  sin_PI2       (* sin (PI / 2) = 1 *)
  cos_PI2       (* cos (PI / 2) = 0 *)
  sin_PI2_neg   (* sin (- (PI/2)) = -1 *)
  cos_PI2_neg   (* cos (- (PI/2)) = 0 *)
  sin_plus_PI   (* sin (r + PI) = - (sin r) *)
  sin_sub_PI    (* sin (r - PI) = - (sin r) *)
  cos_plus_PI   (* cos (r + PI) = - (cos r) *)
  cos_sub_PI    (* cos (r - PI) = - (cos r) *)
  cos2_sin2     (* (cos x)² + (sin x)² = 1 *)
  : R.

Section TEST_sin_cos_tan.
  Goal forall x, cos x * cos x + sin x * sin x = R1.
  intros; autorewrite with R; auto with R. Qed.
  
  Goal forall x, sin x * sin x + cos x * cos x = R1.
  intros; autorewrite with R; auto with R. Qed.

End TEST_sin_cos_tan.


(* ======================================================================= *)
(** ** Rpower *)

(**
Rpower rules:
<<
  1. Definition of Rpower
  a^n       = a * a * ... * a    (* there are n numbers *)
  a^0       = 1 (a ≠ 0)
  a^(-n)    = 1 / a^n (a ≠ 0)
  a^(m/n)   = n√ a^m  (a > 0)
  a^(-m/n)  = 1 / n√ a^m  (a > 0)
>>
 *)
Lemma Rpower_neq0 x y : x <> 0 -> Rpower x y <> 0.
Proof.
  zify.
  
  Abort.


(* ######################################################################### *)
(** * 实数等式、不等式的自动处理 *)

(* ======================================================================= *)
(** ** r = 0 *)

Section TEST_r_eq_0.
  Goal forall r r1 r2 : R, r * r1 = r * r2 -> r1 <> r2 -> r = 0. ra. Qed.
  Goal forall r r1 r2 : R, r1 * r = r2 * r -> r1 <> r2 -> r = 0. ra. Qed.
  Goal forall k x, k * x = x -> x = 0 \/ (x <> 0 /\ k = R1). ra. Qed.
  Goal forall r, r = 0 -> r² = 0. ra. Qed.
End TEST_r_eq_0.

(* ======================================================================= *)
(** ** 0 <= x *)

(** deprecated *)
(* Ltac zero_le := *)
(*   intros; autorewrite with R; *)
(*   repeat (match goal with *)
(*   | |- 0 <= ?r1 * ?r2 => apply Rmult_le_pos *)
(*   | |- _ => idtac *)
(*   end; *)
(*   auto with R; try lra). *)

Section TEST_zero_le.
  Goal forall r, 0 <= r * r. ra. Qed.
  Goal forall r, 0 <= r². ra. Qed.
  Goal forall r1 r2, 0 <= r1 * r1 + r2 * r2. ra. Qed.
  Goal forall r1 r2, 0 <= r1² + r2². ra. Qed.
  Goal forall r1 r2, 0 <= r1 * r1 + r2². ra. Qed.
  Goal forall r1 r2, 0 <= r1² + r2 * r2. ra. Qed.
  Goal forall r, 0 <= r -> 0 <= r * 5. ra. Qed.
  Goal forall r, 0 <= r -> 0 <= r * 5 * 10. ra. Qed.
  Goal forall r, 0 <= r -> 0 <= r * (/5) * 10. ra. Qed.
End TEST_zero_le.


(* ======================================================================= *)
(** ** 0 < x *)

(** deprecated *)
(* Ltac zero_lt := *)
(*   intros; autorewrite with R; *)
(*   match goal with *)
(*   | H : ?r1 <> 0 |- 0 < ?r1² + ?r2² => apply Rneq0_imply_Rplus_gt0_2_1 *)
(*   | H : ?r2 <> 0 |- 0 < ?r1² + ?r2² => apply Rneq0_imply_Rplus_gt0_2_2 *)
(*   | H : 0 < ?r1  |- 0 < ?r1² + ?r2² => apply Rgt0_imply_Rplus_gt0_2_1 *)
(*   | H : 0 < ?r2  |- 0 < ?r1² + ?r2² => apply Rgt0_imply_Rplus_gt0_2_2 *)
(*   | H : 0 < ?r1  |- 0 < ?r1 * ?r2 => apply Rmult_lt_0_compat *)
(*   (* these methods are too ugly, but could work now *) *)
(*   | |- (0 < ?r1 + ?r2)%R => apply Rplus_lt_0_compat *)
(*   | |- (0 < ?r1 * ?r2)%R => apply Rmult_lt_0_compat *)
(*   | |- (0 < ?r1²)%R => apply Rlt_0_sqr *)
(*   | |- _ => idtac *)
(*   end; *)
(*   auto with R; try lra. *)
  
Section TEST_zero_lt.
  Goal forall r, 0 <> r -> 0 < r * r. ra. Qed.
  Goal forall r, 0 <> r -> 0 < r². ra. Qed.
  Goal forall r, 0 < r -> 0 < r * r. ra. Qed.
  Goal forall r, 0 < r -> 0 < r². ra. Qed.
  Goal forall r1 r2, r1 <> 0 -> 0 < r1 * r1 + r2 * r2. ra. Qed.
  Goal forall r1 r2, r1 <> 0 -> 0 < r1² + r2 * r2. ra. Qed.
  Goal forall r1 r2, r1 <> 0 -> 0 < r1 * r1 + r2². ra. Qed.
  Goal forall r1 r2, r1 <> 0 -> 0 < r1² + r2². ra. Qed.
  
  Goal forall r1 r2, r2 <> 0 -> 0 < r1 * r1 + r2 * r2. ra. Qed.
  Goal forall r1 r2, r2 <> 0 -> 0 < r1² + r2 * r2. ra. Qed.
  Goal forall r1 r2, r2 <> 0 -> 0 < r1 * r1 + r2². ra. Qed.
  Goal forall r1 r2, r2 <> 0 -> 0 < r1² + r2². ra. Qed.
  
  Goal forall r1 r2, 0 < r1 -> 0 < r1 * r1 + r2 * r2. ra. Qed.
  Goal forall r1 r2, 0 < r2 -> 0 < r1 * r1 + r2 * r2. ra. Qed.
  
  Goal forall r, 0 < r -> 0 < r * 10. ra. Qed.
  Goal forall r, 0 < r -> 0 < r + 10. ra. Qed.
  Goal forall r, 0 < r -> 0 < r * 100 + 23732. ra. Qed.
  
End TEST_zero_lt.

(** 以下性质会用在复数的三角表示转换为直角表示的构造中，虽然 lra 可以解决，
    但是使用专门的引理会简化定义。*)
Goal forall a b, a <> b -> a <= b -> a < b. ra. Qed.

Lemma Rneq_le_lt : forall a b, a <> b -> a <= b -> a < b.
Proof. ra. Qed.


(* ======================================================================= *)
(** ** x <> 0 *)

(* (** deprecated *) *)
(* Ltac neq_zero := *)
(*   intros; autorewrite with R in *; *)
(*   repeat match goal with *)
(*   (* symmetry *) *)
(*   | H : 0 <> ?a |- ?b <> 0 => apply not_eq_sym in H *)
(*   | H : 0 <> ?a |- 0 <> ?b => apply not_eq_sym in H; apply not_eq_sym *)
(*   (* normal *) *)
(*   | _ : 0 < ?r |- ?r <> 0 => apply zero_lt_imply_Rneq0 *)
(*   | _ : ?r1 <> 0 |- ?r1² <> 0 => apply Rneq0_imply_Rsqr_neq0 *)
(*   | _ : ?r1² <> 0 |- ?r1 <> 0 => apply Rsqr_neq0_imply_Rneq0 *)
(*   | _ : ?r1 + ?r2 <> 0, _ : ?r1 = 0 |- ?r2 <> 0 =>  *)
(*     apply Rplus_neq0_imply_Rneq0_2_1 *)
(*   | _ : ?r1 + ?r2 <> 0, _ : ?r2 = 0 |- ?r1 <> 0 =>  *)
(*     apply Rplus_neq0_imply_Rneq0_2_2 *)
(*   (* default *) *)
(* (*   | |- ?b <> 0 => apply zero_lt_imply_Rneq0 *) *)
(*   | |- _ => idtac *)
(*   end; *)
(*   auto with R. *)

Section TEST_neq_zero.
  Goal forall r, r² <> 0 <-> r <> 0. ra. Qed.
  Goal forall r, r² <> 0 -> r <> 0. ra. Qed.
  Goal forall r, r <> 0 -> r * r <> 0. ra. Qed.
  Goal forall r, r <> 0 -> r² <> 0. ra. Qed.

  Goal forall r, 0 <> r * r -> r <> 0. ra. Qed.
  Goal forall r, r * r <> 0 -> 0 <> r. ra. Qed.
  Goal forall r, 0 <> r * r -> 0 <> r. ra. Qed.
  
  Goal forall r1 r2 r3 r4 : R,
    r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0 <-> 
    r1 * r1 + r2 * r2 + r3 * r3 + r4 * r4 <> 0.
  Proof. ra. Qed.

End TEST_neq_zero.


(* ======================================================================= *)
(** ** a < b *)

Lemma Rdiv_le_imply_Rmul_gt a b c : b > 0 -> a * /b < c -> a < b * c.
Proof.
  intros.
  apply (Rmult_lt_compat_l b) in H0; auto.
  replace (b * (a * /b)) with a in H0; auto.
  field. auto with R.
Qed.
Global Hint Resolve Rdiv_le_imply_Rmul_gt : R.

Lemma Rmul_gt_imply_Rdiv_le a b c : b > 0 -> a < b * c -> a * /b < c.
Proof.
  intros.
  apply (Rmult_lt_compat_l (/b)) in H0; auto with R.
  autorewrite with R in *.
  replace (/b * a) with (a / b) in *; try field; auto with R.
  replace (/b * (b * c)) with c in *; try field; auto with R.
Qed.
Global Hint Resolve Rmul_gt_imply_Rdiv_le : R.
  
(* Global Hint Resolve  *)
(*     Rminus_gt_0_lt  (* 0 < b - a -> a < b *) *)
(*     Rlt_Rminus      (* a < b -> 0 < b - a *) *)
(*     Rlt_minus       (* r1 < r2 -> r1 - r2 < 0 *) *)
(*     : R. *)
    
Ltac tac_le :=
  autounfold with R;
  match goal with
  | |- 0 < ?a + - ?b => apply Rlt_Rminus
  | |- ?a * (?b * /?c) < ?e => replace (a * (b * /c)) with ((a * b) * /c)
  | |- ?a * /?b < ?c => assert (a < b * c); assert (0 < b)
  | |- _ => idtac
  end; try lra; auto with R.
  
Section TEST_tac_le.

  (** 以下证明不能自动完成 *)
  Goal forall h T, 0 < h -> h < 9200 -> -60 < T -> T < 60 -> h / (273.15 + T) < 153.
    ra. Abort.

  (** 简化书写 *)
  Variable h T : R.
  Hypothesis Hh1 : 0 < h.
  Hypothesis Hh2 : h < 9200.
  Hypothesis HT1 : -60 < T.
  Hypothesis HT2 : T < 60.
  
  Goal h * 0.0065 < 273.15 + T. ra. Qed.

  (** 上面不能自动完成的证明，可手动完成 *)
  Goal h / (273.15 + T) < 153.
    autounfold with R.
    assert (273.15 + T > 0). ra.
    assert (h < (273.15 + T) * 153). ra. auto with R.
  Qed.

  (** 另一个例子，自动证明无法完成，但使用构造的ltac可以完成 *)
  Goal h / (273.15 + T) < 1 / 0.0065.
  Proof.
    autounfold with R.
    assert (273.15 + T > 0). ra.
    assert (h < (273.15 + T) * (1/0.0065)). ra. auto with R.
  Qed.
  
  Goal h / (273.15 + T) < 1 / 0.0065.
  Proof.
    tac_le.
  Qed.

  (** 另一个例子 *)
  Goal  0 < 1 - (0.0065 * (h * / (273.15 + T))).
  Proof.
    (* construct condition manually, then try to automate *)
    assert (h / (273.15 + T) < 1/0.0065).
    tac_le. ra.
  Qed.
  
  Goal 0 < 1 - (0.0065 * (h * / (273.15 + T))).
  Proof.
    do 3 tac_le.
  Qed.

End TEST_tac_le.


(* ======================================================================= *)
(** ** Compare with PI *)
Section compare_with_PI.
  
  (** 如何证明有关 PI 的不等式？*)
  Goal 2 < PI.
  Proof.
  Abort.

  (** 一种方法：公理化的给出PI的上下界，然后利用传递性转化为实际值，再lra求解 *)
  Definition PI_ub : R := 3.14159266.
  Definition PI_lb : R := 3.14159265.
  Axiom PI_lt : PI < PI_ub.
  Axiom PI_gt : PI_lb < PI.

  Goal 2 < PI.
  Proof.
    apply Rlt_trans with PI_lb; unfold PI_lb. lra. apply PI_gt.
  Qed.
  
End compare_with_PI.


(* ======================================================================= *)
(** ** 这些是早期的实现，有些转换并不完善，已逐步放弃并整合到其他地方 *)

(* (** a + b <> 0 *) *)
(* Ltac plus_neq0 := *)
(*   match goal with *)
(*   | |- ?a + ?b <> 0 => apply Rgt_not_eq,Rlt_gt,Rplus_lt_0_compat;  *)
(*     auto with R fcs *)
(*   end. *)

(* (** 0 < a *) *)
(* Ltac zero_lt := *)
(*   repeat match goal with *)
(*   (* 0 *) *)
(*   | H: ?a <> 0 |- 0 < ?a * ?a => apply Rlt_0_sqr; apply H *)
(*   | |- 0 < ?a + ?b => apply Rplus_lt_0_compat *)
(*   | |- 0 < ?a * ?b => apply Rmult_lt_0_compat *)
(*   | |- 0 < sqrt ?a => apply sqrt_lt_R0 *)
(*   | |- 0 < ?a / ?b => unfold Rdiv *)
(*   | |- 0 < / ?a => apply Rinv_0_lt_compat *)
(*   | |- 0 < ?a ^ _ => simpl *)
(*   | |- 0 < (?a)² => unfold Rsqr *)
(*   | |- 0 < ?a => auto with R fcs; try lra *)
(*   (* R0 *) *)
(*   | |- R0 < ?a * ?b => apply Rmult_lt_0_compat; try lra; auto with R fcs *)
(*   | |- R0 < sqrt ?a => apply sqrt_lt_R0 *)
(*   | |- R0 < ?a / ?b => unfold Rdiv *)
(*   | |- R0 < / ?a => apply Rinv_0_lt_compat *)
(*   | |- R0 < ?a ^ _ => simpl *)
(*   | |- R0 < (?a)² => unfold Rsqr *)
(*   | |- R0 < ?a => auto with R fcs; try lra *)
(*   end. *)


(* (** simplify expression has sqrt and pow2 *) *)
(* Ltac simpl_sqrt_pow2 := *)
(*   repeat ( *)
(*   (* (_²) -> x * x *) *)
(*   unfold Rsqr; *)
(*   (* (sqrt r1 * sqrt r2)^2 = r1 * r2 *) *)
(*   try rewrite sqrt_mult_sqrt; *)
(*   (* (sqrt x) ^ 2 = x *) *)
(*   try rewrite pow2_sqrt; *)
(*   (* sqrt (x ^ 2) = x *) *)
(*   try rewrite sqrt_pow2; *)
(*   (* (sqrt x * sqrt x) = x *) *)
(*   try rewrite sqrt_sqrt *)
(*   ). *)

(* (** 0 <= a *) *)
(* Ltac zero_le := *)
(*   (* simplify sqrt+pow2 *) *)
(*   repeat ( *)
(*   try simpl_sqrt_pow2; *)
(*   try match goal with *)
(*   (* 0 <= sqrt x *) *)
(*   | |- 0 <= sqrt _ => apply sqrt_pos *)
(*   (* 0 <= a * a *) *)
(*   | |- 0 <= ?a * ?a => apply Rle_0_sqr *)
(*   (* 0 <= a -> 0 <= b -> 0 <= a + b *)  *)
(*   | |- 0 <= ?a + ?b => apply Rplus_le_le_0_compat *)
(*   (* 0 <= a -> 0 <= b -> 0 <= a * b *) *)
(*   | |- 0 <= ?a * ?b => apply Rmult_le_pos *)
(*   (* if fail, proof < again *) *)
(* (*   | |- 0 <= ?a => apply Rlt_le; zero_le *)
(*   | |- R0 <= ?a => apply Rlt_le; zero_le *) *)
(*   end). *)

(* (** a * b <> 0 *) *)
(* Ltac mult_neq0 := *)
(*   match goal with *)
(*   | |- ?a * ?b <> 0 => apply Rgt_not_eq,Rlt_gt;zero_le *)
(*   end. *)

(* (** a <> 0 *) *)
(* Ltac neq0 := *)
(*   repeat match goal with *)
(*   | |- ?a /\ ?b => repeat split *)
(*   | |- ?a <> 0 => apply Rgt_not_eq,Rlt_gt; zero_le *)
(*   end. *)


(** Simplification for trigonometric functions *)

(* Lemma xx_sqr : forall x:R, x * x = Rsqr x. *)
(* Proof. auto. Qed. *)

(* Lemma cos2_sin2' : forall x:R, Rsqr (cos x) + Rsqr (sin x) = 1. *)
(* Proof. intros. autorewrite with R. auto with R. Qed. *)

(* Lemma cos_sin : forall x:R, cos x * sin x = sin x * cos x. *)
(* Proof. ra. Qed. *)

(* Lemma x_neg_x : forall x:R, x + - x = 0. *)
(* Proof. ra. Qed. *)

(* Lemma neg_x_x : forall x:R, -x + x = 0. *)
(* Proof. intros. lra. Qed. *)

(* Lemma x_mul_neg_x : forall x y : R, y * -x = - (x * y). *)
(* Proof. intros. lra. Qed. *)

(* Lemma neg_x_mul_x : forall x y : R, -y * x = - (y * x). *)
(* Proof. intros. lra. Qed. *)

(* Lemma sqrR1_R1 : R1² = R1. *)
(* Proof. unfold Rsqr. ring. Qed. *)

(* Lemma one_R1 : 1 = R1. *)
(* Proof. ring. Qed. *)

(* Lemma inv1_R1 : /1 = R1. *)
(* Proof. field. Qed. *)

(* Lemma invR1_R1 : /R1 = R1. *)
(* Proof. field. Qed. *)

(* Lemma sqrtR1_R1 : sqrt R1 = R1. *)
(* Proof. apply Rsqr_inj. zero_le. lra. rewrite Rsqr_sqrt. *)
(*   rewrite sqrR1_R1. auto. lra. *)
(* Qed. *)

(* Lemma sqrt1_R1 : sqrt 1 = R1. *)
(* Proof. rewrite one_R1. apply sqrtR1_R1. Qed. *)

(* Lemma coscos_sinsin : forall x : R, (cos x * cos x + sin x * sin x) = 1. *)
(* Proof. intros. rewrite ?xx_sqr. rewrite ?cos2_sin2. auto. Qed. *)

(* Lemma sinsin_coscos : forall x : R, (sin x * sin x + cos x * cos x) = 1. *)
(* Proof. intros. rewrite ?xx_sqr. rewrite ?sin2_cos2. auto. Qed. *)

(* (** r1 - (-r2) = r1 + r2 *) *)
(* Lemma Rsub_Rneg : forall (r1 r2 : R), r1 - (- r2) = r1 + r2. *)
(* Proof. intros. ring. Qed. *)

(* (** Simplify trigonometric function and expression of real number *) *)
(* Ltac trigo_simp :=  *)
(*   rewrite ?Rmult_opp_opp;   (* -x * -x = x * x *) *)
(* (*   rewrite ?xx_sqr;          (* x * x = Rsqr x  *) *) *)
(*   rewrite ?Rsub_Rneg,       (* r1 - (-r2) = r1 + r2 *) *)
(*           ?sin2_cos2,       (* sin^2 + cos^2 = 1 *) *)
(*           ?cos2_sin2,       (* cos^2 + sin^2 = 1 *) *)
(*           ?coscos_sinsin,   (* cos*cos + sin*sin = 1 *) *)
(*           ?sinsin_coscos,   (* sin*sin + cos*cos = 1 *) *)
(*           ?cos_sin,         (* cos * sin = sin * cos *) *)
(*           ?x_mul_neg_x,     (* y * -x = - (x * y) *) *)
(*           ?neg_x_mul_x,     (* -y * x = - (x * y) *) *)
(*           ?x_neg_x,         (* x + -x = 0 *) *)
(*           ?neg_x_x,         (* -x + x = 0 *) *)
(*           ?sqrtR1_R1,       (* sqrt R1 = R1 *) *)
(*           ?sqrt1_R1,        (* sqrt 1 = 1 *) *)
(*           ?sqrR1_R1,        (* R1² = R1 *) *)
(* (*           ?Rinv_1,           (* /1 = 1 *) *) *)
(*           ?inv1_R1,         (* /1 = R1 *) *)
(*           ?invR1_R1,        (* /R1 = R1 *) *)
(*           ?one_R1           (* 1 = R1 *) *)
(*   ; *)
(*   autorewrite with R;       (* +0, 0+, *0, 0*, *1, 1* *) *)
(*   try field; *)
(*   auto. *)

(* (* sqrt x = R1 -> x = R1 *) *)
(* Lemma sqrt_eqR1_imply_R1 : forall (x : R), sqrt x = R1 -> x = R1. *)
(* Proof. *)
(*   intros. *)
(*   assert ((sqrt x)² = R1). rewrite H. unfold Rsqr. lra. rewrite <- H0. *)
(*   rewrite Rsqr_sqrt; auto. *)
(*   assert (0 < sqrt x). rewrite H. lra.  *)
(*   apply sqrt_gt0_imply_gt0 in H1. lra. *)
(* Qed. *)


(* ######################################################################### *)
(** * Conversion between R and other types *)

(** 标准库提供的 up 函数，接近于上取整的行为，但不完全相同。
    直观的： r∈[2.0,3.0) -> up(r) = 3
    由如下定理保证：
    Check archimed. (* IZR (up r) > r /\ IZR (up r) - r <= 1 *)

    我们需要计算机中常用的两个函数：下取整 floor, 上取整 ceiling。
    1. 下取整
    r∈[2.0,3.0), floor(r)=2
    所以，floor(r) = up(r) - 1
    2. 上取整
    r∈(2.0,3.0), ceiling(r)=3
    r=2.0, ceiling(r)=2
    所以，ceiling(r)分两种情况，
    若 IZR(up(r))=r，则 ceiling(r)=up(r)-1，否则 ceiling(r)=up(r)

    对负数的行为也是一样的，举例说明：
    floor    2.0 = 2
    floor    2.5 = 2
    floor   -2.0 = -2
    floor   -2.5 = -3

    ceiling  2.0 = 2
    ceiling  2.5 = 3
    ceiling -2.0 = -2
    ceiling -2.5 = -2
 *)

(** ** 补充一些 up, IZR 有关的性质 *)

(** up_IZR 的消去 *)
Lemma up_IZR : forall z, up (IZR z) = (z + 1)%Z.
Proof.
  intros.
  rewrite up_tech with (r:=IZR z); auto; ra.
  apply IZR_lt. lia.
Qed.

(** IZR_up 等式成立，则对应唯一的整数 *)
Lemma IZR_up_unique : forall r, r = IZR (up r - 1) -> exists! z, IZR z = r.
Proof.
  intros.
  exists (up r - 1)%Z. split; auto.
  intros. subst.
  rewrite up_IZR in *.
  apply eq_IZR. auto.
Qed.

(** r 处于(z,z+1)的开区间，则不可能等于任何整数 *)
Lemma IZR_in_range_imply_no_integer : forall r z,
    IZR z < r ->
    r < IZR (z + 1) ->
    ~(exists z', IZR z' = r).
Proof.
  intros. intro. destruct H1. subst.
  apply lt_IZR in H0.
  apply lt_IZR in H. lia.
Qed.


(** ** R与Z互相转换 *)

(** Z到R *)
Definition Z2R (z : Z) : R := IZR z.

(** 对R下取整，取地板：截断为不大于它的最接近的整数 *)
Definition R2Z_floor (r : R) : Z := (up r) - 1.

(** 对R上取整，取顶板：截断为不小于它的最接近的整数 *)
Definition R2Z_ceiling (r : R) : Z :=
  let z := up r in
  if Req_EM_T r (IZR (z - 1)%Z)
  then z - 1
  else z.


(** r∈[z,z+1.0) -> floor(r) = z *)
Lemma R2Z_floor_spec : forall r z,
    IZR z <= r < IZR z + 1.0 -> R2Z_floor r = z.
Proof.
  intros. unfold R2Z_floor in *. destruct H.
  assert (up r = z + 1)%Z; try lia.
  rewrite <- up_tech with (z:=z); auto.
  rewrite plus_IZR. lra.
Qed.

(** r=z -> ceiling r = z /\ r∈(z,z+1.0) -> ceiling r = z+1 *)
Lemma R2Z_ceiling_spec : forall r z,
    (r = IZR z -> R2Z_ceiling r = z) /\
      (IZR z < r < IZR z + 1.0 -> R2Z_ceiling r = (z+1)%Z).
Proof.
  intros. unfold R2Z_ceiling in *. split; intros.
  - destruct (Req_EM_T r (IZR (up r - 1))).
    + rewrite H. rewrite up_IZR. lia.
    + rewrite H in n. destruct n.
      rewrite up_IZR. f_equal. lia.
  - destruct H. destruct (Req_EM_T r (IZR (up r - 1))).
    + apply IZR_in_range_imply_no_integer in H; auto.
      * destruct H. exists (up r - 1)%Z; auto.
      * rewrite plus_IZR. ra.
    + rewrite up_tech with (r:=r); auto; ra.
      rewrite plus_IZR. ra.
Qed.


(** Z2R (R2Z_floor r) 小于等于 r *)
Lemma Z2R_R2Z_floor_le : forall r, Z2R (R2Z_floor r) <= r.
Proof.
  intros. unfold Z2R,R2Z_floor. rewrite minus_IZR.
  destruct (archimed r). ra.
Qed.

(** Z2R (R2Z_floor r) 小于等于 r *)
Lemma Z2R_R2Z_floor_gt : forall r, r - 1 < Z2R (R2Z_floor r).
Proof.
  intros. unfold Z2R,R2Z_floor. rewrite minus_IZR.
  destruct (archimed r). ra.
Qed.


(** ** 自然数与实数的转换 *)
Definition nat2R (n : nat) : R := Z2R (nat2Z n).
Definition R2nat_floor (r : R) : nat := Z2nat (R2Z_floor r).
Definition R2nat_ceiling (r : R) : nat := Z2nat (R2Z_ceiling r).


(* ######################################################################### *)
(** * Reqb,Rleb,Rltb: Boolean comparison of R *)

Definition Reqb (r1 r2 : R) : bool := HierarchySetoid.Aeqb r1 r2.
Definition Rleb (r1 r2 : R) : bool := if Rle_lt_dec r1 r2 then true else false.
Definition Rltb (r1 r2 : R) : bool := if Rlt_le_dec r1 r2 then true else false.
Infix "=?"  := Reqb : R_scope.
Infix "<=?" := Rleb : R_scope.
Infix "<?"  := Rltb : R_scope.


(** Reflection of (=) and (=?) *)
Lemma Reqb_eq : forall x y, x =? y = true <-> x = y.
Proof.
  apply Aeqb_true.
Qed.

Lemma Reqb_neq : forall x y, x =? y = false <-> x <> y.
Proof.
  apply Aeqb_false.
Qed.

Lemma Reqb_comm : forall r1 r2, (r1 =? r2) = (r2 =? r1).
Proof.
  intros. cbv. destruct Req_EM_T,Req_EM_T; subst; auto. easy.
Qed.

Lemma Reqb_refl : forall r, r =? r = true.
Proof.
  intros. cbv. destruct Req_EM_T; auto.
Qed.

Lemma Reqb_trans : forall r1 r2 r3, r1 =? r2 = true -> 
  r2 =? r3 = true -> r1 =? r3 = true.
Proof.
  intros. cbv in *. destruct Req_EM_T,Req_EM_T,Req_EM_T; subst; auto.
Qed.



(* ######################################################################### *)
(** * Approximate of two real numbers *)

(** r1 ≈ r2, that means |r1 - r2| <= diff *)
Definition Rapprox (r1 r2 diff : R) : Prop := Rabs (r1 - r2) <= diff.

(** boolean version of approximate function *)
Definition Rapproxb (r1 r2 diff : R) : bool := Rleb (Rabs (r1 - r2)) diff.



(* ######################################################################### *)
(** * Mathematical Hierarchy *)

(* Global Instance EqReflect_R : EqReflect Reqb. *)
(* Proof. *)
(*   constructor. intros. *)
(*   destruct (a =? b) eqn:E1. *)
(*   - apply Reqb_eq in E1. constructor. auto. *)
(*   - apply Reqb_neq in E1. constructor. auto. *)
(* Defined. *)


(* ######################################################################### *)
(** * 自动证明无法解决的一些例子 *)

(** 示例1，在 Complex 关于 Carg 的证明中出现 *)
Goal forall a b r, a > 0 -> b <= r / a -> 0 <= r - b *a.
Proof.
  intros.
  ra. (* 自动证明不能完成 *)
  apply Rmult_le_compat_r with (r:=a) in H0; ra.
  unfold Rdiv in H0. rewrite Rmult_assoc in H0.
  rewrite Rinv_l in H0; ra.
Qed.

Lemma mult_PI_gt0 : forall r, 0 < r -> 0 < r * PI.
Proof.
  ra. auto with R.
Qed.  
