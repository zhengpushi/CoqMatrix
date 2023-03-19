(*
Copyright 2023 ZhengPu Shi
This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : derivative of a function
  author    : ZhengPu Shi
  date      : 2023.03
  
  remark    :
  1. 注意，这里仅仅是公理化的表示了微积分的基本运算和性质，并不是完整的微积分理论研究。

     Note that this is only an axiomatic representation of the basic operations and 
     properties of calculus, and is not a complete theoretical study of calculus

  2. Coq标准库中包含了关于导函数的一个库Rderiv。
     按理，我们关于导函数问题的推理应该从这个库所建立的数学引理开始。
     但是那些引理的结构比较复杂，在目前阶段，我们可以先直接引入一些熟知的关于导函数的等式
     作为公理，在此基础上进行证明开发工作。

     The Coq standard library contains a library on derivative functions, Rderiv.
     It is logical that our reasoning about the derivative function problem should 
     start from the mathematical lemmas established by this library.
     However, the structure of those lemmas is rather complicated, and at this stage 
     we can directly introduce some familiar equations about derivative functions as 
     axioms and develop proofs based on them.

  3. reference :
     (1) 陈老师的讲义
     (2) 高等数学学习手册，徐小湛
 *)


Require Import FunctionalExtensionality.
(* Require Export Reals. *)
From CoqMatrix Require Import RExt.
(* Require Export Lra. *)
(* From CoqMatrix Require Import HierarchySetoid. *)

Open Scope R_scope.


(** New scope for real function *)
Declare Scope fun_scope.
Delimit Scope fun_scope with F.
Open Scope fun_scope.


(* ######################################################################### *)
(** * Real Functions *)


(** ** 实数界 *)
Section setR.
  
  (** R上的一个子集 *)
  Definition setR := R -> Prop.

  Let X : setR := fun (x : R) => x > 0.
  (* Variable Y : setR. *)

  (** 全体 *)
  Definition allR : setR := fun _ => True.
  
End setR.


(** ** 邻域 *)
Section neighbourhoodR.

  Definition neighbourhoodR (a delta : R) : setR :=
    fun x => delta > 0 /\ Rabs (x - a) < delta.

End neighbourhoodR.


(** ** 有界实数界 *)
Section boundR.
  
  (** 一个集合是有界的 *)
  Definition boundR (X : setR) : Prop :=
    exists (M : R), (M > 0) /\ (forall x, X x -> Rabs x <= M).

  (** 一个集合是无界的 *)
  Definition unboundR (X : setR) : Prop :=
    forall (M : R), (M > 0) -> (exists x, X x /\ Rabs x > M).

  (** 集合有界的等价定义 *)
  Definition boundR' (X : setR) : Prop :=
    exists (A B : R), (A < B) /\ (forall x, X x -> (A <= x <= B)).

  Theorem boundR_eq_boundR' : forall X, boundR X <-> boundR' X.
  Admitted.
End boundR.


(** ** Definition of real functions *)
Section fun_def.

  (** To proof the quanlity of two functions *)
  Theorem fun_eq : forall (u v : R->R), (forall t, u t = v t) <-> u = v.
  Proof.
    intros. split; intros.
    - extensionality x; auto.
    - rewrite H. auto.
  Qed.
  
  (** Type of a function from real number to real number *)
  Definition tpRFun := R -> R.

  (** Type of a function from real function to another real function *)
  Definition tpRFunctional := (R->R) -> (R->R).

End fun_def.


(** ** Domain of real functions *)
Section fun_domain.

  (** 一个函数的定义域：使得函数表达式有意义的一切实数组成的集合 *)
  Parameter domain_of : tpRFun -> setR.

  (** 常见的定义域 *)
  Axiom domain_of_inv : domain_of (fun u => 1/u) = (fun u => u <> 0).
  Axiom domain_of_sqrt : domain_of (fun u => sqrt u) = (fun u => u >= 0).
  Axiom domain_of_ln : domain_of ln = (fun u => u > 0).
  Axiom domain_of_tan : domain_of tan = (fun u => ~(exists (k : Z), u = 2 * (IZR k) * PI + PI/2)).

End fun_domain.


(** ** Range of real functions *)
Section fun_range.

  (** 一个函数的值域：函数在定义域内取值后的到的函数值的集合 *)
  Definition range_of (f : tpRFun) : setR :=
    fun y => exists x, (domain_of f) x -> f x = y.

End fun_range.


(** ** Composition of real functions. *)
Section fun_comp.

  (** composition of real functions *)
  Definition fcomp(u v : tpRFun) : tpRFun := fun x => u (v x).
  Infix "∘" := fcomp (at level 20, right associativity) : fun_scope.

  Fact fcomp_rw : forall u v, (fun x => u (v x)) = u ∘ v.
  Proof. auto. Qed.

  (** 两个函数可以复合的条件是：内函数的值域与外函数的定义域的交集非空 *)
  Definition fcomp_valid (u v : tpRFun) : Prop :=
    let Du := domain_of u in
    let Rv := range_of v in
    exists x, (Du x /\ Rv x).

  Section test.
    Goal let f := fun x => x * x + (1/x) in
         let g := fun x => x + (1/x) in
         fcomp_valid f g ->
         f ∘ g = fun x =>
                   let x2 := x*x in
                   x2 + 1/x2 + (x/(x2+1)) + 2.
    Proof.
      intros. unfold f, g, fcomp, fcomp_valid in *. apply fun_eq. intros. field.
      Abort.

  End test.
End fun_comp.
Infix "∘" := fcomp (at level 20, right associativity) : fun_scope.


(** ** Commonly used functions *)
Section common_funs.

  (** constant function *)
  Definition fconst (C : R) : tpRFun := fun _ => C.
  Definition fzero : tpRFun := fconst R0.
  Definition fone : tpRFun := fconst R1.

  Definition fid : tpRFun := fun x => x.

  (** Absolute function *)
  Fact Rabs_pos_iff : forall x, Rabs x = x <-> x >= 0.
  Proof.
    intros. split; intros.
    - destruct (Rgeb_reflect x 0); auto.
      assert (x <= 0); try lra.
      apply Rabs_left1 in H0. lra.
    - apply Rabs_right. auto.
  Qed.

  Fact Rabs_neg_iff : forall x, Rabs x = - x <-> x <= 0.
  Proof.
    intros. split; intros.
    - destruct (Rleb_reflect x 0); auto.
      assert (x >= 0); try lra.
      apply Rabs_right in H0. lra.
    - apply Rabs_left1. auto.
  Qed.

  (** 取整函数 *)
  (* Check R2Z_floor. *)
  (* Check R2Z_ceiling. *)
  
  (** Sign function *)
  Definition sgn : tpRFun :=
    fun x => if x >? 0
           then 1
           else (if x =? 0 then 0 else -1).

  Lemma sgn_1_iff : forall x, sgn x = 1 <-> x > 0.
  Proof.
    intros. unfold sgn. split; intros.
    - destruct (Rltb_reflect 0 x); try lra.
      destruct (Reqb_reflect x 0); try lra.
    - destruct (Rltb_reflect 0 x); try lra.
  Qed.    

  Lemma sgn_neg1_iff : forall x, sgn x = -1 <-> x < 0.
  Proof.
    intros. unfold sgn. split; intros.
    - destruct (Rltb_reflect 0 x); try lra.
      destruct (Reqb_reflect x 0); try lra.
    - destruct (Rltb_reflect 0 x); try lra.
      destruct (Reqb_reflect x 0); try lra.
  Qed.    

  Lemma sgn_mul_eq_abs : forall x, ((sgn x) * x)%R = Rabs x.
  Proof.
    intros. unfold sgn.
    destruct (Rltb_reflect 0 x).
    + rewrite Rabs_right; lra.
    + rewrite Rabs_left1; try lra.
      destruct (Reqb_reflect x 0); try lra.
  Qed.

  Lemma sgn_mul_abs_eq : forall x, ((sgn x) * (Rabs x))%R = x.
  Proof.
    intros. unfold sgn.
    destruct (Rltb_reflect 0 x).
    + rewrite Rabs_right; lra.
    + rewrite Rabs_left1; try lra.
      destruct (Reqb_reflect x 0); try lra.
  Qed.
  
End common_funs.



(** ** Basic Elementary Functions (基本初等函数) *)
Section basic_elementary_fun.

  (** *** 1. 幂函数 y = x ^ a *)
  Definition fpower (a : R) : tpRFun := fun x => Rpower x a.

  (** 常见的幂函数 *)
  Fact fpower_1_eq : fpower 1 = fid.
  Proof. unfold fpower. apply fun_eq. intros. rewrite Rpower_1; auto. Admitted.
  Fact fpower_n1_eq : fpower (-1) = fun x => 1/x. Admitted.

  Fact fpower_2_eq : fpower 2 = fun x => x * x. Admitted.
  Fact fpower_2_eq' : fpower 2 = fun x => Rsqr x. Admitted.
  Fact fpower_2_eq'' : fpower 2 = Rsqr. Admitted.
  Fact fpower_3_eq : fpower 3 = fun x => x * x * x. Admitted.
  Fact fpower_1_2_eq : fpower (1/2) = sqrt. Admitted.

  (** *** 2. 指数函数 y = a ^ x *)
  Definition fexp (a : R) : tpRFun := fun x => Rpower a x.
  
  Axiom domain_of_fexp : forall (a : R), (a > 0 /\ a <> 1) -> domain_of (fexp a) = allR.
  Fact range_of_fexp (a : R) : range_of (fexp a) = fun x => x > 0. Admitted.

  (** 指数函数的运算法则 *)
  Fact fexp_add : forall a x y, a > 0 -> fexp a (x + y) = (fexp a x) * (fexp a y).
  Admitted.
  Fact fexp_sub : forall a x y, a > 0 -> fexp a (x - y) = (fexp a x) / (fexp a y).
  Admitted.
  Fact fexp_mul : forall a x y, a > 0 -> fexp a (x * y) = fexp (fexp a x) y.
  Admitted.
  Fact fexp_div : forall a b x, a > 0 /\ b > 0 -> fexp (a/b) x = (fexp a x) / (fexp b x).
  Admitted.

  (** *** 3. 对数函数 y = log_a x *)
  Definition flog (a : R) : tpRFun := fun x => ln x / ln a.
  Definition flg : tpRFun := flog 10.
  
  Axiom domain_of_flog : forall (a : R),
      (a > 0 /\ a <> 1) -> domain_of (flog a) = (fun x => x > 0).
  Fact range_of_flog (a : R) : range_of (flog a) = allR. Admitted.

  (** 特殊函数值 *)
  Fact flog_a_1 (a : R) : flog a 1 = 0.
  Proof. unfold flog. Search ln. rewrite ln_1. field. Admitted.

  Fact flog_a_a (a : R) : flog a a = 1. Admitted.
  Fact fln_1 : ln 1 = 0. Admitted.
  Fact fln_e : let e := 2.71828 in ln e = 1. Admitted.

  (** 常用公式 *)
  Fact fln_mul : forall a x y, flog a (x * y) = (flog a x) + (flog a y). Admitted.
  Fact fln_div : forall a x y, flog a (x / y) = (flog a x) - (flog a y). Admitted.
  Fact fln_exp : forall a x y, flog a (fexp x y) = y * (flog a x). Admitted.
  Fact fln_chgbottom : forall a b x, flog a x = (flog b x) / (flog b a). Admitted.
  Fact fexp_fln : forall x, exp (ln x) = x. Admitted.
  Fact fln_fexp : forall x, ln (exp x) = x. Admitted.
  
  Fact fln_eq1 : forall u v : R, Rpower u v = exp (ln (Rpower u v)).
  Proof. intros. rewrite fexp_fln. auto. Qed.
  Fact fln_eq2 : forall u v : R, Rpower u v = exp (v * ln u).
  Proof. intros. Admitted.


  (** *** 4. Triangle functions (三角函数) *)

  (** Convert between degree and radian *)
  Definition deg2rad (d : R) : R := d * (PI / 180).  (* 1 degree = 0.01745.. rad *)
  Definition rad2deg (r : R) : R := r * (180 / PI).  (* 1 rad = 27.29578.. degree *)

  (** definition of triangle functions *)
  (* Check sin. *)
  (* Check cos. *)
  (* Check tan. *)
  (* Check cot. *)
  Definition cot : tpRFun := fun x => 1 / (tan x).
  (* Check sec. *)
  Definition sec : tpRFun := fun x => 1 / (cos x).
  Definition csc : tpRFun := fun x => 1 / (sin x).

  (** 基本关系 *)
  Fact sin_csc : forall x, (sin x) * (csc x) = 1. Admitted.
  Fact cos_sec : forall x, (cos x) * (sec x) = 1. Admitted.
  Fact tan_cot : forall x, (tan x) * (cot x) = 1. Admitted.
  Fact sec_eq : forall x, sec x = 1 / (cos x). Admitted.
  Fact csc_eq : forall x, csc x = 1 / (sin x). Admitted.
  Fact tan_eq : forall x, tan x = (sin x) / (cos x). Admitted.
  Fact cot_eq : forall x, cot x = (cos x) / (sin x). Admitted.
  Fact sin2_add_cos2 : forall x, (sin x)² + (cos x)² = 1. Admitted.
  Fact sec2_sub_tan2 : forall x, (sec x)² - (tan x)² = 1. Admitted.
  Fact csc2_sub_cot2 : forall x, (csc x)² - (cot x)² = 1. Admitted.
  Fact sin2_eq : forall x, (sin x)² = 1 - (cos x)². Admitted.
  Fact cos2_eq : forall x, (cos x)² = 1 - (sin x)². Admitted.
  Fact sec2_eq : forall x, (sec x)² = 1 - (tan x)². Admitted.
  Fact tan2_eq : forall x, (tan x)² = 1 - (sec x)². Admitted.
  Fact csc2_eq : forall x, (csc x)² = 1 - (csc x)². Admitted.
  Fact cot2_eq : forall x, (cot x)² = 1 - (cot x)². Admitted.

  (** 诱导公式 *)
  Fact sin_PI2_sub : forall x, sin (PI/2 - x) = cos x. Admitted.
  Fact sin_PI2_add : forall x, sin (PI/2 + x) = cos x. Admitted.
  Fact sin_PI_sub : forall x, sin (PI - x) = sin x. Admitted.
  Fact sin_PI_add : forall x, sin (PI + x) = - sin x. Admitted.
  Fact sin_3PI2_sub : forall x, sin (3 * PI / 2 - x) = - cos x. Admitted.
  Fact sin_3PI2_add : forall x, sin (3 * PI / 2 + x) = - cos x. Admitted.
  Fact sin_2PI_add : forall x, sin (2 * PI + x) = - sin x. Admitted.

  Fact cos_PI2_sub : forall x, cos (PI/2 - x) = sin x. Admitted.
  Fact cos_PI2_add : forall x, cos (PI/2 + x) = - sin x. Admitted.
  Fact cos_PI_sub : forall x, cos (PI - x) = - cos x. Admitted.
  Fact cos_PI_add : forall x, cos (PI + x) = - cos x. Admitted.
  Fact cos_3PI2_sub : forall x, cos (3 * PI / 2 - x) = - sin x. Admitted.
  Fact cos_3PI2_add : forall x, cos (3 * PI / 2 + x) = sin x. Admitted.
  Fact cos_2PI_add : forall x, cos (2 * PI + x) = cos x. Admitted.

  Fact tan_PI2_sub : forall x, tan (PI/2 - x) = cot x. Admitted.
  Fact tan_PI2_add : forall x, tan (PI/2 + x) = - cot x. Admitted.
  Fact tan_PI_sub : forall x, tan (PI - x) = - tan x. Admitted.
  Fact tan_PI_add : forall x, tan (PI + x) = tan x. Admitted.
  Fact tan_3PI2_sub : forall x, tan (3 * PI / 2 - x) = cot x. Admitted.
  Fact tan_3PI2_add : forall x, tan (3 * PI / 2 + x) = - cot x. Admitted.
  Fact tan_2PI_add : forall x, tan (2 * PI + x) = - tan x. Admitted.
  
  Fact cot_PI2_sub : forall x, cot (PI/2 - x) = tan x. Admitted.
  Fact cot_PI2_add : forall x, cot (PI/2 + x) = - tan x. Admitted.
  Fact cot_PI_sub : forall x, cot (PI - x) = - cot x. Admitted.
  Fact cot_PI_add : forall x, cot (PI + x) = cot x. Admitted.
  Fact cot_3PI2_sub : forall x, cot (3 * PI / 2 - x) = tan x. Admitted.
  Fact cot_3PI2_add : forall x, cot (3 * PI / 2 + x) = - tan x. Admitted.
  Fact cot_2PI_add : forall x, cot (2 * PI + x) = - cot x. Admitted.

  (** 特殊三角函数值 *)
  Fact sin_0 : sin 0 = 0. Admitted.
  Fact sin_PI6 : sin (PI / 6) = 1 / 2. Admitted.
  Fact sin_PI4 : sin (PI / 4) = (sqrt 2) / 2. Admitted.
  Fact sin_PI3 : sin (PI / 3) = (sqrt 3) / 2. Admitted.
  Fact sin_PI2 : sin (PI / 2) = 1. Admitted.
  Fact sin_2PI3 : sin (2 * PI / 3) = (sqrt 3) / 2. Admitted.
  Fact sin_3PI4 : sin (3 * PI / 4) = (sqrt 2) / 2. Admitted.
  Fact sin_5PI6 : sin (5 * PI / 6) = 1 / 2. Admitted.
  Fact sin_PI : sin PI = 0. Admitted.
  Fact sin_3PI2 : sin (3 * PI / 2) = -1. Admitted.
  Fact sin_2PI : sin (2 * PI) = 0. Admitted.

  Fact cos_0 : cos 0 = 1. Admitted.
  Fact cos_PI6 : cos (PI / 6) = (sqrt 3) / 2. Admitted.
  Fact cos_PI4 : cos (PI / 4) = (sqrt 2) / 2. Admitted.
  Fact cos_PI3 : cos (PI / 3) = 1 / 2. Admitted.
  Fact cos_PI2 : cos (PI / 2) = 0. Admitted.
  Fact cos_2PI3 : cos (2 * PI / 3) = - 1 / 2. Admitted.
  Fact cos_3PI4 : cos (3 * PI / 4) = - (sqrt 2) / 2. Admitted.
  Fact cos_5PI6 : cos (5 * PI / 6) = - (sqrt 3) / 2. Admitted.
  Fact cos_PI : cos PI = -1. Admitted.
  Fact cos_3PI2 : cos (3 * PI / 2) = 0. Admitted.
  Fact cos_2PI : cos (2 * PI) = 1. Admitted.

  Fact tan_0 : tan 0 = 1. Admitted.
  Fact tan_PI6 : tan (PI / 6) = (sqrt 3) / 3. Admitted.
  Fact tan_PI4 : tan (PI / 4) = 1. Admitted.
  Fact tan_PI3 : tan (PI / 3) = sqrt 3. Admitted.
  (* Fact tan_PI2 : tan (PI / 2) = inf. Admitted. *)
  Fact tan_2PI3 : tan (2 * PI / 3) = - (sqrt 3). Admitted.
  Fact tan_3PI4 : tan (3 * PI / 4) = - 1. Admitted.
  Fact tan_5PI6 : tan (5 * PI / 6) = - (sqrt 3) / 3. Admitted.
  Fact tan_PI : tan PI = 0. Admitted.
  (* Fact tan_3PI2 : tan (3 * PI / 2) = inf. Admitted. *)
  Fact tan_2PI : tan (2 * PI) = 0. Admitted.

  (* Fact cot_0 : cot 0 = inf. Admitted. *)
  Fact cot_PI6 : cot (PI / 6) = (sqrt 3). Admitted.
  Fact cot_PI4 : cot (PI / 4) = 1. Admitted.
  Fact cot_PI3 : cot (PI / 3) = (sqrt 3) / 3. Admitted.
  Fact cot_PI2 : cot (PI / 2) = 0. Admitted.
  Fact cot_2PI3 : cot (2 * PI / 3) = - (sqrt 3) / 3. Admitted.
  Fact cot_3PI4 : cot (3 * PI / 4) = - 1. Admitted.
  Fact cot_5PI6 : cot (5 * PI / 6) = - (sqrt 3). Admitted.
  (* Fact cot_PI : cot PI = inf. Admitted. *)
  Fact cot_3PI2 : cot (3 * PI / 2) = 0. Admitted.
  (* Fact cot_2PI : cot (2 * PI) = inf. Admitted. *)

  (** 和差公式 *)
  Fact sin_add : forall x y, sin (x + y) = sin x * cos y + cos x * sin y. Admitted.
  Fact sin_sub : forall x y, sin (x - y) = sin x * cos y - cos x * sin y. Admitted.

  Fact cos_add : forall x y, cos (x + y) = cos x * cos y - sin x * sin y. Admitted.
  Fact cos_sub : forall x y, cos (x - y) = cos x * cos y + sin x * sin y. Admitted.

  Fact tan_add : forall x y, tan (x + y) = (tan x + tan y) / (1 - tan x * tan y). Admitted.
  Fact tan_sub : forall x y, tan (x - y) = (tan x - tan y) / (1 + tan x * tan y). Admitted.

  Fact cot_add : forall x y, cot (x + y) = (cot x * cot y - 1) / (cot x + cot y). Admitted.
  Fact cot_sub : forall x y, cot (x - y) = (cot x * cot y + 1) / (cot x - cot y). Admitted.

  (** 倍角公式 *)
  Fact sin_2a : forall x, sin (2 * x) = 2 * sin x * cos x. Admitted.
  Fact cos_2a : forall x, cos (2 * x) = (cos x)² - (sin x)². Admitted.
  Fact cos_2a' : forall x, cos (2 * x) = 1 - 2 * (sin x)². Admitted.
  Fact cos_2a'' : forall x, cos (2 * x) = 2 * (cos x)² - 1. Admitted.
  Fact tan_2a : forall x, tan (2 * x) = (2 * tan x) / (1 - (tan x)²). Admitted.
  Fact cot_2a : forall x, cot (2 * x) = ((cot x)² - 1) / (2 * cot x). Admitted.

  (** 半角公式 *)

  (** 积化和差，和差化积 *)
  Fact sin_cos : forall x y, sin x * cos y = (1/2) * (sin (x + y) + sin (x - y)). Admitted.
  Fact cos_cos : forall x y, cos x * cos y = (1/2) * (cos (x + y) + cos (x - y)). Admitted.
  Fact sin_sin : forall x y, sin x * sin y = (1/2) * (cos (x - y) - cos (x + y)). Admitted.

  Fact sin_add_sin : forall x y, sin x + sin y = 2 * sin ((x+y)/2) * cos ((x-y)/2). Admitted.
  Fact sin_sub_sin : forall x y, sin x - sin y = 2 * sin ((x-y)/2) * cos ((x+y)/2). Admitted.
  Fact cos_add_cos : forall x y, cos x + cos y = 2 * cos ((x+y)/2) * cos ((x-y)/2). Admitted.
  Fact cos_sub_cos : forall x y, cos x - cos y = -2 * sin ((x+y)/2) * sin ((x-y)/2). Admitted.
  

  (** *** 5. 反三角函数 *)
  (* Check asin. *)
  (* Check acos. *)
  (* Check atan. *)
  (* Check acot. *)
  Parameter acot : tpRFun.

  (** 特殊函数值 *)
  Fact asin_0 : asin 0 = 0. Admitted.
  Fact asin_1_2 : asin (1 / 2) = PI / 6. Admitted.
  Fact asin_sqrt2_2 : asin ((sqrt 2) / 2) = PI / 4. Admitted.
  Fact asin_sqrt3_2 : asin ((sqrt 3) / 2) = PI / 3. Admitted.
  Fact asin_1 : asin 1 = PI / 2. Admitted.

  Fact acos_0 : acos 0 = (PI / 2). Admitted.
  Fact acos_1_2 : acos (1 / 2) = PI / 3. Admitted.
  Fact acos_sqrt2_2 : acos ((sqrt 2) / 2) = PI / 4. Admitted.
  Fact acos_sqrt3_2 : acos ((sqrt 3) / 2) = PI / 2. Admitted.
  Fact acos_1 : acos 1 = 0. Admitted.

  Fact atan_0 : atan 0 = 0. Admitted.
  Fact atan_sqrt3_3 : atan ((sqrt 3) / 3) = PI / 6. Admitted.
  Fact atan_1 : atan 1 = PI. Admitted.
  Fact atan_sqrt3 : atan (sqrt 3) = PI / 3. Admitted.

  Fact acot_0 : acot 0 = PI / 2. Admitted.
  Fact acot_sqrt3_3 : acot ((sqrt 3) / 3) = PI / 6. Admitted.
  Fact acot_1 : acot 1 = PI. Admitted.
  Fact acot_sqrt3 : acot (sqrt 3) = PI / 3. Admitted.


End basic_elementary_fun.

Hint Unfold
  fpower fexp flog flg
  deg2rad rad2deg
  : R.

(** ** Arithematic operations of real functions. *)
Section fun_arith.

  (** Addition of real functions *)
  Definition fadd (u v : tpRFun) : tpRFun := fun x => u x + v x.
  Definition fopp (u : tpRFun) := fun x => - u x.
  Definition fsub (u v : tpRFun) := fun x => u x - v x.
  Definition fmul (u v : tpRFun) := fun x => u x * v x.
  Definition finv (u : tpRFun) := fun x => / (u x).
  Definition fdiv (u v : tpRFun) := fun x => u x / v x.
  Definition fcmul (c : R) (u : tpRFun) := fun x => c * (u x).

End fun_arith.

Infix "+" := fadd : fun_scope.
Notation "- f" := (fopp f) : fun_scope.
Infix "-" := fsub : fun_scope.
Infix "*" := fmul : fun_scope.
Notation "/ f" := (finv f) : fun_scope.
Infix "/" := fdiv : fun_scope.
Infix "c*" := fcmul : fun_scope.


(** ** 有界函数 *)
Section boundf.

  (** f在X内是有界的 *)
  Definition boundf (f : tpRFun) (X : setR) : Prop :=
    exists M, M > 0 /\ (forall x, X x -> (Rabs (f x) <= M)).

  Definition unboundf (f : tpRFun) (X : setR) : Prop :=
    forall M, M > 0 -> (exists x, X x /\ (Rabs (f x) > M)).

  (** 有界性的等价刻画 *)
  Definition boundf' (f : tpRFun) (X : setR) : Prop :=
    exists (A B : R), (A < B) /\ (forall x, X x -> (A <= f x <= B)).

  Theorem boundf_eq_boundf' : forall f X, boundf f X <-> boundf' f X.
  Admitted.

  (** l是f在定义域内的下界 *)
  Definition lower_bound_of (f : tpRFun) (l : R) : Prop :=
    l > 0 /\ (forall x, (domain_of f x -> f x >= l)).
  
  (** u是f在定义域内的上界 *)
  Definition upper_bound_of (f : tpRFun) (u : R) : Prop :=
    u > 0 /\ (forall x, (domain_of f x -> f x <= u)).

  (** u是f在定义域内的界 *)
  Definition bound_of (f : tpRFun) (u : R) : Prop :=
    u > 0 /\ (forall x, (domain_of f x -> Rabs (f x) <= u)).

  (** 常见的有界函数
      以下函数在其定义域内是有界的（整体有界函数） *)
  Fact boundf_sin : boundf sin allR. Admitted.
  Fact bound_sin : bound_of sin 1. Admitted.
    
  Fact boundf_cos : boundf cos allR. Admitted.
  Fact bound_cos : bound_of cos 1. Admitted.
  
End boundf.


(** ** Properties of real functions. *)
Section fun_op_props.
  
  (** Convert from function operations to element operations *)
  
  Lemma fadd_ok : forall (u v : tpRFun) (x : R), (u + v) x = (u x + v x)%R.
  Proof. intros. reflexivity. Qed.

  Lemma fopp_ok : forall (v : tpRFun) (x : R), (- v) x = (- v x)%R.
  Proof. auto. Qed.

  Lemma fsub_ok : forall (u v : tpRFun) (x : R), (u - v) x = (u x - v x)%R.
  Proof. auto. Qed.

  Lemma fmul_ok : forall (u v : tpRFun) (x : R), (u * v) x = (u x * v x)%R.
  Proof. auto. Qed.

  Lemma finv_ok : forall (v : tpRFun) (x : R), (/ v) x = (/ v x)%R.
  Proof. auto. Qed.

  Lemma fdiv_ok : forall (u v : tpRFun) (x : R), (u / v) x = (u x / v x)%R.
  Proof. auto. Qed.

  Lemma fcmul_ok : forall (c : R) (u : tpRFun) (x : R), (c c* u) x = (c * u x)%R.
  Proof. auto. Qed.

  (** Properties for real function addition *)
  Lemma fadd_assoc : forall (u v w : tpRFun), (u + v) + w = u + (v + w).
  Proof. intros. apply fun_eq. intros. rewrite !fadd_ok. ring. Qed.

  Lemma fadd_comm : forall (u v : tpRFun), u + v = v + u.
  Proof. intros. apply fun_eq. intros. rewrite !fadd_ok. ring. Qed.

  (** Properties for real function multiplication *)
  Lemma fmul_assoc : forall (u v w : tpRFun), (u * v) * w = u * (v * w).
  Proof. intros. apply fun_eq. intros. rewrite !fmul_ok. ring. Qed.

  Lemma fmul_comm : forall (u v : tpRFun), u * v = v * u.
  Proof. intros. apply fun_eq. intros. rewrite !fmul_ok. ring. Qed.

  (** Properties for real function scalar multiplication *)
  Lemma fcmul_assoc1 : forall (c d : R) (u : tpRFun), c c* (d c* u) = (c * d) c* u.
  Proof. intros. apply fun_eq. intros. rewrite !fcmul_ok. ring. Qed.

  Lemma fcmul_assoc2 : forall (c : R) (u v : tpRFun), c c* (u * v) = (c c* u) * v.
  Proof. intros. apply fun_eq. intros. rewrite ?fmul_ok, ?fcmul_ok, ?fmul_ok. ring. Qed.

  Lemma fmul_add_distr_l : forall u v w, u * (v + w) = u * v + u * w.
  Proof. intros. apply fun_eq. intros. rewrite ?fmul_ok, ?fadd_ok, ?fmul_ok. ring. Qed.

  Lemma fmul_add_distr_r : forall u v w, (u + v) * w = u * w + v * w.
  Proof. intros. apply fun_eq. intros. rewrite ?fmul_ok, ?fadd_ok, ?fmul_ok. ring. Qed.

End fun_op_props.


(** ** Parity of function *)
Section fun_parity.

  Definition oddf (u : tpRFun) : Prop := forall x, (u (-x) = - (u x))%R.
  Definition evenf (u : tpRFun) : Prop := forall x, (u (-x) = u x)%R.

  Fact oddf_x : evenf fid. Admitted.
  Fact oddf_pow3 : evenf (fun x => x ^ 3). Admitted.
  Fact oddf_sin : evenf sin. Admitted.
  Fact oddf_tan : evenf tan. Admitted.

  Fact evenf_const : forall (C : R), evenf (fconst C). Admitted.
  Fact evenf_pow2 : evenf (fun x => x ^ 2). Admitted.
  Fact evenf_pow2n : forall (n : nat), evenf (fun x => x ^ (2 * n)). Admitted.
  Fact evenf_cos : evenf cos. Admitted.

  Theorem fadd_odd_odd_is_odd : forall u v, oddf u -> oddf v -> oddf (u + v).
  Admitted.

  Theorem fsub_odd_odd_is_odd : forall u v, oddf u -> oddf v -> oddf (u - v).
  Admitted.

  Theorem fmul_odd_odd_is_even : forall u v, oddf u -> oddf v -> evenf (u * v).
  Admitted.

  Theorem fdiv_odd_odd_is_even : forall u v, oddf u -> oddf v -> evenf (u / v).
  Admitted.

  Theorem fadd_even_even_is_even : forall u v, evenf u -> evenf v -> evenf (u + v).
  Admitted.

  Theorem fsub_even_even_is_even : forall u v, evenf u -> evenf v -> evenf (u - v).
  Admitted.

  Theorem fmul_even_even_is_even : forall u v, evenf u -> evenf v -> evenf (u * v).
  Admitted.

  Theorem fdiv_even_even_is_even : forall u v, evenf u -> evenf v -> evenf (u / v).
  Admitted.

  Theorem fcomp_any_even_is_even : forall u v, evenf v -> evenf (u∘v).
  Admitted.

  Theorem fcomp_odd_odd_is_odd : forall u v, oddf u -> oddf v -> oddf (u∘v).
  Admitted.

  Theorem fcomp_even_odd_is_even : forall u v, evenf u -> oddf v -> evenf (u∘v).
  Admitted.

End fun_parity.


(** ** 周期函数 *)
Section periodic_fun.

  (** 一个函数是周期函数 *)
  Definition periodicf (f : tpRFun) : Prop :=
    exists (l : R), l > 0 /\ (forall x, (domain_of f) x -> f (x + l)%R = f x).

  (** l 是 f 的周期 *)
  Definition periodic_of (f : tpRFun) (l : R) : Prop :=
    l > 0 /\ (forall x, (domain_of f) x -> f (x + l)%R = f x).

  (** 常见的周期函数 *)
  Fact periodicf_sin : periodicf sin. Admitted.
  Fact periodic_of_sin : periodic_of sin (2*PI). Admitted.

  Fact periodicf_cos : periodicf cos. Admitted.
  Fact periodic_of_cos : periodic_of cos (2*PI). Admitted.

  Fact periodicf_tan : periodicf tan. Admitted.
  Fact periodic_of_tan : periodic_of tan (2*PI). Admitted.

  
End periodic_fun.


(* ######################################################################### *)
(** * Derivative functions and related axioms *)

(** ** Definition of derivative operator *)
Section deriv_def.

  (** derivative opertor *)
  Parameter deriv : tpRFun -> tpRFun.

End deriv_def.

Notation "f '" := (deriv f) (at level 25) : R_scope.


(** 导数模型可以刻画很多自然科学和社会科学中的现象
    Derivative models can describe many phenomena in natural science and social science
 *)
Section practice_models_using_derivative.

  (* 2D曲线 => 切线斜率 *)
  Let k (f : tpRFun) x := f ' x.
  (* 2D曲线 => 法线斜率 *)
  Let k' (f : tpRFun) x := (- (1 / f ' x))%R.
  (* 路程 => 速度 *)
  Let v (s : tpRFun) t := s ' t.
  (* 速度 => 加速度 *)
  Let a (v : tpRFun) t := v ' t.
  (* 旋转角度 => 角速度 *)
  Let ω (θ : tpRFun) t := θ ' t.
  (* 电量 => 电流强度 *)
  Let I (Q : tpRFun) t := Q ' t.
  (* 人口数量 => 人口增长率 *)
  Let v1 (P : tpRFun) t := P ' t.

End practice_models_using_derivative.


(** ** 基本初等函数的导数公式 *)
Section deriv_basic_funcs.
  Axiom deriv_C : forall (C : R), (fun _ => C)' = fun _ => 0.
  Axiom deriv_fpower : forall a, (fpower a)' = a c* (fpower (a-1)).

  Fact deriv_id : fid ' = fone.
  Proof.
    rewrite <- fpower_1_eq. rewrite deriv_fpower.
    apply fun_eq. intros. cbv.
    autounfold with R. autorewrite with R.
    autorewrite with R; ra.
    Admitted. (* ToDo: check it?? *)
  
  Fact deriv_sqrt : (sqrt) ' = (fun x => 1 / (2 * sqrt x))%R.
  Proof.
    rewrite <- fpower_1_2_eq. rewrite deriv_fpower.
    apply fun_eq; intros. cbv.
    rewrite ?Rmult_assoc. f_equal.
    rewrite Rpower_plus.
    rewrite Rpower_Ropp. ring_simplify.
    replace (R1 * / (R1 + R1))%R with (/2)%R; try lra.
    rewrite Rpower_sqrt. rewrite Rpower_1.
    assert (t = Rsqr (sqrt t)).
    { rewrite Rsqr_sqrt; auto. admit. }
    rewrite H at 2. cbv. field.
  Admitted. (* ToDo: need more hypothesis *)

  Fact deriv_inv : (fun x => 1/x)%R ' = fun x => (-(/(x*x)))%R. Admitted.
  Fact deriv_inv' : (fun x => /x)%R ' = fun x => (-(/(x*x)))%R. Admitted.

  Fact deriv_sin : sin ' = cos. Admitted.
  Fact deriv_cos : cos ' = sin. Admitted.
  Fact deriv_tan : tan ' = sec * sec. Admitted.
  Fact deriv_cot : cot ' = - (csc * csc). Admitted.
  Fact deriv_sec : sec ' = (sec * tan). Admitted.
  Fact deriv_csc : csc ' = - (csc * cot). Admitted.

  Fact deriv_fexp : forall a, (fexp a) ' = (ln a) c* (fexp a). Admitted.
  Fact deriv_exp : exp ' = exp. Admitted.
  Fact deriv_flog : forall a, (flog a) ' = / ((ln a) c* fid). Admitted.
  Fact deriv_fln : ln ' = finv fid. Admitted.
  Fact deriv_asin : asin ' = (fun x => / (sqrt (1 - x * x)))%R. Admitted.
  Fact deriv_acos : acos ' = (fun x => - / (sqrt (1 - x * x)))%R. Admitted.
  Fact deriv_atan : atan ' = (fun x => / (1 + x * x))%R. Admitted.
  Fact deriv_acot : acot ' = (fun x => - / (1 + x * x))%R. Admitted.
  (* Fact deriv_asec : asec ' = (fun x => / (x * (sqrt (x * x - 1))))%R. Admitted. *)
  (* Fact deriv_acsc : acsc ' = (fun x => - / (x * (sqrt (x * x - 1))))%R. Admitted. *)
  
End deriv_basic_funcs.


(** 导数的四则运算法则 *)
Section deriv_rules.
  Axiom deriv_fadd : forall (u v : tpRFun), (u + v)' = u ' + v '.
  Axiom deriv_fsub : forall (u v : tpRFun), (u - v)' = u ' - v '.
  Axiom deriv_fcmul : forall (c : R) (u : tpRFun), (c c* u)' = c c* u '.
  Axiom deriv_fmul : forall (u v : tpRFun), (u * v)' = u ' * v + u * v '.
  Axiom deriv_fdiv : forall (u v : tpRFun),
      v <> (fun x => 0) -> (u / v)' = (u ' * v - u * v ') / (v * v).

  Fact deriv_finv : forall (v : tpRFun), (/v) ' = - ((v ') / (v * v)). Admitted.

  (** 导数的线性性质 *)
  Fact deriv_linear : forall c1 c2 u1 u2, (c1 c* u1 + c2 c* u2)' = c1 c* u1 ' + c2 c* u2 '.
  Proof. intros. rewrite ?deriv_fadd, ?deriv_fcmul. auto. Qed.

  (** 乘法求导推广 *)
  Fact deriv_fmul3 : forall u v w, (u*v*w)' = u ' * v * w + u * v ' * w + u * v * w '.
  Proof.
    intros. rewrite ?deriv_fmul. rewrite fmul_assoc; f_equal.
    rewrite fmul_add_distr_r. auto.
  Qed.
  
End deriv_rules.

(** 复合函数的求导法则：链式法则 *)
Section deriv_comp.

  Axiom deriv_comp : forall u v, (u∘v)' = (fun x => (u ' (v x)) * (v ' x))%R.

  Section ex_2_2_3_page73.
    Goal (fun x => fexp 2 (Rsqr (sin (/x))))' =
           (fun x => (- (ln 2) / (x*x)) * (fexp 2 (Rsqr (sin (/x)))) * sin (2/x))%R.
    Proof.
      remember (fun u => fexp 2 u) as y.
      remember (Rsqr) as u.
      remember (sin) as v.
      remember (fun x => /x)%R as w.
      rewrite (fcomp_rw y), (fcomp_rw u), (fcomp_rw v).
      rewrite ?deriv_comp.
      rewrite Heqy, Hequ, Heqv, Heqw. clear.
      apply fun_eq; intros.
      rewrite deriv_fexp.
      rewrite <- fpower_2_eq''. rewrite deriv_fpower.
      rewrite deriv_sin.
      rewrite deriv_inv'.
      (* all the derivivate have been eliminated *)
      cbv.
      (* now, all the functions were eliminated, only remain expressions of R type *)
      ring_simplify.
      (* 因为有 ln, Rpower, sin, 等，所以 lra 无法解决，
         但又不能总是手工消除，因为数学工作量本来就大，再加上形式化时引入的各种机制
         使问题变得更为复杂，故而手工消除不可取。
         因此，如果能有一种聪明的tactic，可以消除这类等式或不等式问题，将极大的提高
         实数问题的证明速度。*)
      Abort.

  End ex_2_2_3_page73.
    
End deriv_comp.

Section example_LCR_Problem.

  Variable L C R1 : R.
  Variables i uc ur : tpRFun.

  (* 克希霍夫定律 *)
  Axiom kxmf1 : L c* i ' + uc + (R1 c* i) = ur.
  Axiom kxmf2 : i = C c* uc '.

  (** 待证命题（消去 i，对等式变形即可）  *)
  Let main_thm : Prop := (L * C)%R c* uc ' ' + (R1 * C)%R c* uc ' + uc = ur.

  (* 方法1：在高阶上直接利用引理证明 *)
  Goal main_thm.
  Proof.
    hnf. rewrite <- kxmf1. rewrite kxmf2.
    rewrite deriv_fcmul.
    rewrite <- fcmul_assoc1. rewrite ?fadd_assoc. f_equal.
    rewrite fadd_comm. f_equal.
    rewrite fcmul_assoc1. auto.
  Qed.

  (* 方法2：展开到一阶，利用了 ring，避免底层操作 *)
  Goal main_thm.
  Proof.
    hnf. rewrite <- kxmf1. rewrite kxmf2.
    apply fun_eq. intros. rewrite deriv_fcmul.
    repeat (rewrite ?fadd_ok; rewrite ?fcmul_ok).
    ring.
  Qed.

(* 小结：函数等式的证明可以采用两种方法。
   一种是使用一组函数等式引理重写函数表达式来证明。
   另一种是直接把函数等式转变成实数等式来证明。
 *)

End example_LCR_Problem.


(** ** Equations *)
Section deriv_equations.
  
  Theorem fconst_simp : forall x y, (fconst x) y = x.
  Proof. intros. auto. Qed.

  Theorem fid_simp : forall x, fid x = x.
  Proof. intros. auto. Qed.

  Theorem deriv_fconst: forall C, (fconst C)' = fzero.
  Proof. intros. cbv. rewrite deriv_C. auto. Qed.

  Theorem deriv_fone : (fone)' = fzero.
  Proof. unfold fone. apply deriv_fconst. Qed.

  Theorem deriv_fzero : (fzero)' = fzero.
  Proof. unfold fzero. apply deriv_fconst. Qed.

  (** (1/v)' = -v'/(v^2) *)
  Theorem deriv_inv'' : forall (v : tpRFun),
      (* Here, different with "v <> fzero" *)
      (forall x, v x <> 0) ->
      (fone / v)' = (-1) c* (v ') / (v * v).
  Proof.
    intros. apply fun_eq. intros.
    unfold fone.
    repeat (
        try rewrite ?deriv_fdiv;
        try rewrite ?deriv_fconst;
        try rewrite ?fdiv_ok;
        try rewrite ?fmul_ok;
        try rewrite ?fcmul_ok;
        try rewrite ?fadd_ok;
        try rewrite ?fsub_ok;
        try rewrite ?fid_simp;
        try rewrite fconst_simp).
    - autorewrite with R. field.
      intro. specialize (H t). destruct H.
      ra. (* Tips: a good examples to show that "ra" is better than "lra" *)
    - intro. eapply fun_eq in H0. specialize (H t). rewrite H0 in H. lra.
  Qed.

End deriv_equations.



(* ######################################################################### *)
(** * Integration *)

