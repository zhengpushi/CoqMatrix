(* 
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.


  在解一元二次方程时碰到的一个问题：
  标准库提供了 Rsqr_sol_eq_0_1 引理，提供了求根公式，但是要求 nonzeroreal 类型，
  该类型是一个struct，内部使用了 Real 类型。
  
  现在想要建立一个 Real 类型的引理，如何将“nonzeroreal类型”予以回避，或者内部封装起来？
*)
  

Require Import Reals.
Open Scope R.

(* 检查一些定义 *)
Print nonzeroreal.
Check Rsqr_sol_eq_0_1.

(* nonzeroreal类型可直接使用 *)
Lemma quadratic_equation_prop1 : forall (a:nonzeroreal) (b c x:R) ,
  x = (-b + sqrt(b² - 4 * a * c)) * ( / (2 * a)) ->
  0 <= b² - 4 * a * c ->
  a * x² + b * x + c = 0.
  intros.
  apply Rsqr_sol_eq_0_1.
  - trivial.
  - left. unfold sol_x1, Delta. auto.
Qed.

(* Real类型暂时没有办法 *)
Lemma quadratic_equation_prop2 : forall (a b c x:R) ,
  x = (-b + sqrt(b² - 4 * a * c)) * ( / (2 * a)) ->
  0 <= b² - 4 * a * c ->
  a * x² + b * x + c = 0.
  intros.
  Abort.

(* 找到 Rsqr_sol_eq_0_1 源码，仿照其实现重写一个版本 *)
Lemma Rsqr_sol_eq_0_1' :
  forall (a:R) (b c x:R),
    a <> 0 ->
    0 <= b ^ 2 - 4 * a * c ->
    x = (- b + sqrt (b ^ 2 - 4 * a * c)) / (2 * a) \/ 
    x = (- b - sqrt (b ^ 2 - 4 * a * c)) / (2 * a) 
    -> a * x ^ 2 + b * x + c = 0.
Proof.
  intros.
  elim H1.
  - intro.
    rewrite H2. field_simplify; auto.
    rewrite <- (Rsqr_pow2 (sqrt (b ^ 2 - 4 * a * c))).
    rewrite Rsqr_sqrt; auto.
    field; auto.
  - intro.
    rewrite H2. field_simplify; auto.
    rewrite <- (Rsqr_pow2 (sqrt (b ^ 2 - 4 * a * c))).
    rewrite Rsqr_sqrt; auto.
    field; auto.
Qed.

