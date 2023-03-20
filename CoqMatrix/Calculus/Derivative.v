(*
Copyright 2023 ZhengPu Shi
This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : derivative of a function
  author    : ZhengPu Shi
  date      : 2023.03
  
  reference :
  (1) 陈老师的讲义
  (2) 高等数学学习手册，徐小湛

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
     However, the structure of those lemmas is rather compicated, and at this stage 
     we can directly introduce some familiar equations about derivative functions as 
     axioms and develop proofs based on them.

 *)

Require Import RealFunction.


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


(** ** Known equations of derivative *)
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
