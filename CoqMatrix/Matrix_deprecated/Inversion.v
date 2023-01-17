(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Inversion of square matrix
  author    : ZhengPu Shi
  date      : 2022.08
  
  remark    :
  1. 行列式(determinant)的三种方法，参考：https://zhuanlan.zhihu.com/p/435900775
  a. 按行/列展开，用代数余子式的定义来计算。
    每展开一次，相当于降了一阶。
    注意：按行/列展开，是拉普拉斯展开定理的特例。
  b. 利用初等变换。
  c. 逆序数法求行列式，也就是按定义。
  
  2. 利用行列式计算逆矩阵的算法，从Coq到OCaml，测试结果
  n=8, 1.1s;  n=9, 12s;  n=10, 120s
  主要问题：
  a. 看到CPU占用过高，但内存并不高。
  b. 可能是 nat 结构不合理，最好是 int 类型的下标。可以考虑OCaml直接写一个版本。
  c. 可能是 det 函数不断的递归导致。
  所以，用OCaml仿照同样的思路，可以写多个版本来测试，以便排除是否为算法问题导致。
  a. 版本1，仍然使用 NatFun 风格，但是是 int 下标
  b. 版本2，使用 array 结构
  c. 版本3，使用 matrix (bigarray) 结构
  
  版本1的测试结果
  n=8, 0.25s;  n=9, 2.4s;  n=10, 32s
  这一版还是很慢，可能是函数式风格的原因？？
  
  版本2的测试结果
  n=8, 1s;  n=9,7s; n=10,未测试
  这一版反而更慢了，array的开销为什么这么大，也许是for循环太多导致
  
*)


Require Import StrExt.
Require Export Matrix.
Require RAST.


(* ==================================== *)
(** ** 一些通用的策略，以后要整理到一个合适的位置 *)

(** 列表相等转换为元素相等 *)
(* Ltac tac_listeq := *)
(*   repeat match goal with *)
(*   | |- cons ?x1 ?l1 = cons ?x2 ?l2 => f_equal *)
(*   end. *)


(* ==================================== *)
(** ** 全排列（简称排列），用于验证行列式的定义 *)
Section permutation.

  Context {A:Type}.
  Context {A0:A}.

  (** 取出列表中的 第 k 个元素 与 其余元素构成的列表 *)
  Fixpoint pick (l : list A) (k : nat) : A * list A :=
    match k with
    | 0 => (hd A0 l, tl l)
    | S k' => match l with
             | [] => (A0, [])
             | x :: l' =>
                 let (a,l0) := pick l' k' in
                 (a, [x] ++ l0)
             end
    end.

  (** 列表全排列的辅助函数 *)
  Fixpoint perm_aux (n : nat) (l : list A) : list (list A) :=
    match n with
    | 0 => [[]]
    | S n' =>
        let d1 := map (fun i => pick l i) (seq 0 n) in
        let d2 := map 
                    (fun k : A * list A => let (x, lx) := k in
                                         let d3 := perm_aux n' lx in
                                         map (fun l1 => [x] ++ l1) d3) d1 in
        concat d2
    end.

  (** 列表全排列的辅助函数 *)
  Definition perm (l : list A) : list (list A) :=
    perm_aux (length l) l.

  (** 全排列的种数 *)
  Definition Pn (l : list A) := length (perm l).

  (** 全排列种数等于阶乘 *)
  Lemma Pn_eq : forall l, Pn l = fact (length l).
  Proof.
    intros l.
    induction l; simpl; auto.
  Abort.

End permutation.

Section test.
  (* Compute perm []. *)
  (* Compute perm [1]. *)
  (* Compute perm [1;2]. *)
  (* Compute perm [1;2;3]. *)
  (* Compute perm [1;2;3;4]. *)
End test.


(* ==================================== *)
(** ** 基于伴随矩阵的逆矩阵算法 *)
Section inversion.

  (** 矩阵元素要求是域结构 *)
  Context `{F:Field}.
  Declare Scope A_scope.
  Delimit Scope A_scope with A.
  Open Scope A_scope.
  Infix "+" := add0 : A_scope.
  Infix "*" := mul0 : A_scope.
  Notation "0" := zero0 : A_scope.
  Notation "1" := one0 : A_scope.
  Notation "- x" := (opp x) : A_scope.
  Notation "a - b" := (a + (-b)) : A_scope.
  Notation "/ x" := (inv x) : A_scope.
  Notation "a / b" := (a * (/b)) : A_scope.

  (* Add Ring ring_inst : make_ring_theory. *)
  Add Field field_inst : make_field_theory.

  (* ------------------------------------------- *)
  (** *** Determinant. *)
  
  (** Get the sub square matrix which remove r-th row and c-th column
    from a square matrix. *)
  Definition submat {n} (m : Square (S n)) (r c : nat) : @Square A n :=
    f2m (fun i j =>
      let i' := (if i <? r then i else S i) in
      let j' := (if j <? c then j else S j) in
      m2f m i' j').
  
  (** Calculate determinant
      方法：按照第0行展开 *)
  Fixpoint det {n} : Square n -> A :=
    match n with
    | 0 => fun _ => 1
    | S n' =>
        fun m =>
          fold_left
            add0
            (map (fun i =>
                    let a := if Nat.even i
                             then (m2f m 0 i)%nat
                             else (-(m2f m 0 i)%nat)%A
                    in
                    let d := det (submat m 0 i) in
                    (a * d))
               (seq 0 n))
            0
    end.
  
  (** Verify formula for determinant of specify matrix *)
  Section det_specify_matrix.

    (** 任给一些方阵 *)
    Variable m11 : @Square A 1.
    Variable m22 : @Square A 2.
    Variable m33 : @Square A 3.

    (** 给出其行列式公式 *)
    Definition det_m11 : A :=
      let a11 := m2t_1x1 m11 in
      a11.
    Definition det_m22 : A :=
      let '((a11,a12),(a21,a22)) := m2t_2x2 m22 in
      a11 * a22 - a12 * a21.
    Definition det_m33 : A :=
      let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) := m2t_3x3 m33 in
      a11*a22*a33 - a11*a23*a32 -
        a12*a21*a33 + a12*a23*a31 +
        a13*a21*a32 - a13*a22*a31.

    (** 验证这些公式正确 *)
    Lemma det_m11_ok : det m11 = det_m11. cbv. ring. Qed.
    Lemma det_m22_ok : det m22 = det_m22. cbv. ring. Qed.
    Lemma det_m33_ok : det m33 = det_m33. cbv. ring. Qed.

  End det_specify_matrix.
  
  (* ------------------------------------------- *)
  (** *** 克拉默法则 *)
  
  (** 对于 A X = b 的方程组，
      当方程可数和未知数个数相等时，即A构成方阵时，
      记 D = |A|, Di = |[b/i] A|，其中，[b/i] A 表示把 A 中第 i 列换成 b，
      若 |A| 不为零，则方程有解，并可以给出求解公式  *)
  
  (** 替换方阵某一列的内容 *)
  Definition mchgcol {n} (m : Square n) (k : nat) (v : mat n 1) : @Square A n :=
    f2m (fun i j => if j =? k then m2f v i 0%nat else m2f m i j).
  
  (** 克拉默法则 *)
  Definition cramerRule {n} (A : Square n) (b : mat n 1) : mat n 1 :=
    let D := det A in
    f2m (fun i j =>
      let Di := det (mchgcol A i b) in
        (Di / D)%A).
  
  
  (* ------------------------------------------- *)
  (** *** 伴随矩阵，简称伴随阵. *)
  
  (** 由各个元素的代数余子式以转置的样式构成的新矩阵，称为原矩阵的伴随矩阵
      adjoint matrix, adjugate matrix, 
      adj(A), A* *)

  Definition madj {n} : Square n -> Square n := 
    match n with
    | O => fun m => m 
    | S n' => fun m =>
      f2m (fun i j =>
        let s := if Nat.even (i + j) then 1 else -(1) in
        let d := det (submat m j i) in 
        s * d)
    end.
  
  
  (* ------------------------------------------- *)
  (** *** 逆矩阵 *)
  Definition minv {n} (m : Square n) :=
    mcmul (1 / det m) (madj m)
      (mul0:=mul0) (r:=n) (c:=n).

  (** Inversion matrix of of specify matrix *)
  Section inversion_for_specify_matrix.

    (** 任给一些方阵 *)
    Variable m11 : @Square A 1.
    Variable m22 : @Square A 2.
    Variable m33 : @Square A 3.

    (** 给出其逆矩阵公式 *)
    Definition inv_m11 : Square 1 :=
      let a11 := m2t_1x1 m11 in
      let d := det_m11 m11 in
      mk_mat_1_1 (A0:=0) (1/a11).
    Definition inv_m22 : Square 2 :=
      let '((a11,a12),(a21,a22)) := m2t_2x2 m22 in
      let d := det_m22 m22 in
      mk_mat_2_2 (A0:=0) (a22/d) (-a12/d) (-a21/d) (a11/d).

    (* 注意，以下公式可由matlab来提供，避免手写 *)
    Definition inv_m33 : Square 3 :=
      let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) := m2t_3x3 m33 in
      let d := det_m33 m33 in
      mk_mat_3_3 (A0:=0)
        ((a22*a33 - a23*a32)/d) (-(a12*a33 - a13*a32)/d) ((a12*a23 - a13*a22)/d)
        (-(a21*a33 - a23*a31)/d) ((a11*a33 - a13*a31)/d) (-(a11*a23 - a13*a21)/d)
        ((a21*a32 - a22*a31)/d) (-(a11*a32 - a12*a31)/d) ((a11*a22 - a12*a21)/d).

    (** 验证这些公式正确。
        注意，这里只验证了表达式与minv函数输出一致，还未验证逆矩阵性质 *)
    Lemma inv_m11_ok : det m11 <> 0 -> minv m11 == inv_m11.
    Proof. lma. field. cbv in H. intro. destruct H. ring_simplify. auto. Qed.

    Lemma inv_m22_ok : det m22 <> 0 -> minv m22 == inv_m22.
    Proof. lma; field; cbv in H; intro; destruct H; ring_simplify; auto. Qed.

    Lemma inv_m33_ok : det m33 <> 0 -> minv m33 == inv_m33.
    Proof.
      lma; field; cbv in H; intro; destruct H; ring_simplify; auto;
        rewrite <- H0; ring.
    Qed.
    
  End inversion_for_specify_matrix.

  (** 直接计算出1/2/3阶符号矩阵的逆矩阵 *)
  Section FindFormula.
    Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.
    Let m1 := mk_mat_1_1 (A0:=0) a11.
    Let m2 := mk_mat_2_2 (A0:=0) a11 a12 a21 a22.
    Let m3 := mk_mat_3_3 (A0:=0) a11 a12 a13 a21 a22 a23 a31 a32 a33.
    
    (* 虽然结果正确，但是太过冗长，以后使用 RAST 来化简 *)
    (* Compute (m2l (minv m1)). *)
    (* Compute (m2l (minv m2)). *)
    (* Compute (m2l (minv m3)). *)
  
  End FindFormula.

End inversion.


(* ==================================== *)
(** ** Q上的矩阵求逆 *)
Module MatrixInvQ.

  Export QArith.
  Open Scope Q.

  Definition mk_mat_3_1 := mk_mat_3_1 (A0:=0).
  Definition mk_mat_3_3 := mk_mat_3_3 (A0:=0).
  Definition mk_mat_4_1 := mk_mat_4_1 (A0:=0).
  Definition mk_mat_4_4 := mk_mat_4_4 (A0:=0).
  Definition det {n} :=
    det (n:=n) (add0:=Qplus) (zero0:=0) (mul0:=Qmult) (one0:=1) (opp:=Qopp).
  Definition cramerRule {n} :=
    cramerRule (n:=n) (add0:=Qplus) (zero0:=0)
      (mul0:=Qmult) (one0:=1) (opp:=Qopp) (inv:=Qinv).
  Definition madj {n} :=
    madj (n:=n) (add0:=Qplus) (zero0:=0) (mul0:=Qmult) (one0:=1) (opp:=Qopp).

  (** 由于Q的表示不唯一，使用 reduce 来转换为唯一形式 *)
  Definition m2l_red {r c} (m : mat r c) := map (fun l => map Qred l) (m2l m).
  
End MatrixInvQ.


(* ==================================== *)
(** ** 测试 *)

(** 数值矩阵部分，使用特定的域会便于计算，但涉及到符号时，会展开为复杂的表达式，
不便于符号矩阵的证明 *)
Module Exercise_Number.

  Import MatrixInvQ.
  
  (** 同济大学，线性代数（第五版），page22, 例14 *)
  Section example14.
    Let A := mk_mat_4_4 
      2 1 (-5) 1
      1 (-3) 0 (-6)
      0 2 (-1) 2
      1 4 (-7) 6.
    Let b := mk_mat_4_1 8 9 (-5) 0.

    Goal det A == 27. cbv. auto. Qed.

    (* Compute (m2l (cramerRule A b)). *)
    Goal (m2l_red (cramerRule A b) = [[3];[-4];[-1];[1]]). cbv. auto. Qed.

  End example14.
  
  Section example15.
    Let A := mk_mat_4_4 
      1 1 1 1
      1 2 4 8
      1 3 9 27
      1 4 16 64.
    Let b := mk_mat_4_1 3 4 3 (-3).

    Goal (m2l_red (cramerRule A b) = [[3];[-3#2];[2];[-1#2]]). cbv. auto. Qed.
  End example15.

End Exercise_Number.


(** 符号矩阵部分，在符号这一级方便证明 *)
(** 同济大学《线性代数（第五版）》，page25, 习题一 *)
Module Exercise_Symbol.

  (** 矩阵元素 *)
  Context `{F:Field}.
  Declare Scope A_scope.
  Delimit Scope A_scope with A.
  Open Scope A_scope.
  Infix "+" := add0 : A_scope.
  Infix "*" := mul0 : A_scope.
  Notation "0" := zero0 : A_scope.
  Notation "1" := one0 : A_scope.
  Notation "- x" := (opp x) : A_scope.
  Notation "a - b" := (a + (-b)) : A_scope.
  Notation "/ x" := (inv x) : A_scope.
  Notation "a / b" := (a * (/b)) : A_scope.
  Notation "2" := (1+1) : A_scope.
  Notation "3" := (1+2) : A_scope.

  Add Field field_inst : make_field_theory.

  Definition mk_mat_3_3 := mk_mat_3_3 (A0:=0).
  Definition mk_mat_4_4 := mk_mat_4_4 (A0:=0).
  Definition det {n} :=
    det (n:=n) (add0:=add0) (zero0:=zero0) (mul0:=mul0) (one0:=one0) (opp:=opp). 
  
  (* A上的幂函数 *)
  Fixpoint Apow (a : A) (n : nat) :=
    match n with
    | 0 => 1
    | S n' => (a * (Apow a n'))%A
    end.
  Infix "^" := (Apow).
  
  Example ex6_1 : forall a b : A,
    let m := (mk_mat_3_3 (a*a) (a*b) (b*b) (2*a) (a+b) (2*b) 1 1 1)%A in
      det m = (a - b)^3.
  Proof. intros. cbv. ring. Qed.
  
  Example ex6_2 : forall a b x y z : A,
    let m1 := (mk_mat_3_3
      (a*x+b*y) (a*y+b*z) (a*z+b*x)
      (a*y+b*z) (a*z+b*x) (a*x+b*y)
      (a*z+b*x) (a*x+b*y) (a*y+b*z))%A in
    let m2 := mk_mat_3_3 x y z y z x z x y in
      det m1 = ((a^3 + b^3) * det m2)%A.
  Proof. intros. cbv. ring. Qed.
  
  Example ex6_3 : forall a b e d : A,
    let m := (mk_mat_4_4
      (a*a) ((a+1)^2) ((a+2)^2) ((a+3)^2)
      (b*b) ((b+1)^2) ((b+2)^2) ((b+3)^2)
      (e*e) ((e+1)^2) ((e+2)^2) ((e+3)^2)
      (d*d) ((d+1)^2) ((d+2)^2) ((d+3)^2))%A in
        det m = 0.
  Proof. intros. cbv. ring. Qed.
  
  Example ex6_4 : forall a b e d : A,
    let m := (mk_mat_4_4
      1 1 1 1
      a b e d
      (a^2) (b^2) (e^2) (d^2)
      (a^4) (b^4) (e^4) (d^4))%A in
      det m = ((a-b)*(a-e)*(a-d)*(b-e)*(b-d)*(e-d)*(a+b+e+d))%A.
  Proof. intros. cbv. ring. Qed.
  
  (** 6.(5) 是无穷的，需要更多构造和证明，待以后补充 *)

End Exercise_Symbol.


(* ==================================== *)
(** ** 计算符号矩阵逆矩阵的 更简洁形式 *)
(** 在Coq中对符号矩阵直接计算行列式或逆矩阵等，含有大量冗余数据（比如zero,one）,
    尽管不影响证明，但是我们并不轻轻松的得到对用户友好的表示。
    换言之，例如 0 + 1 * a + b * 1 + 0 要能够自动化简为 a + b。
    当初开发基于伴随矩阵求逆矩阵的一个目的就是要能对符号矩阵求解，
    不但要能求解，最好还能得到友好的表达形式。

    本节的目的是使用一种AST，设法简化矩阵表达式。
    原理：
        由于矩阵运算包括这里的逆矩阵运算是建立在多态上的，
        所以我们定制一种矩阵元素类型，并将该类型上的运算用归纳的方式
        统一在AST下，然后利用AST来化简表示。

    另一种思路：
        可以借助 ring_simplify 来化简。比如：
        Goal forall aaa:A, aaa = det matxx.  (* 先构造一个证明环境 *)
        (* 然后在证明中可以化简表达式 *)
    
 *)
Module Simplify_by_RAST.

  (** 带有AST的R类型，用于简化表达式 *)
  Import RAST.
  
  (** 矩阵元素类型 *)
  Notation "0" := A0.
  Notation "1" := A1.
  Notation "2" := (1 + 1)%A.
  Notation "3" := (1 + 2)%A.
  Infix "+" := Aadd.
  Infix "-" := Asub.
  Infix "*" := Amul.

  Definition mk_mat_1_1 := mk_mat_1_1 (A0:=0).
  Definition mk_mat_2_2 := mk_mat_2_2 (A0:=0).
  Definition mk_mat_3_3 := mk_mat_3_3 (A0:=0).
  Definition minv {n} :=
    minv (n:=n)(add0:=Aadd)(zero0:=0)(opp:=Aopp)
      (mul0:=Amul)(one0:=1)(inv:=Ainv).
  
  (* simp 函数可以化简A类型上的项，我们需要对 list (list A) 进行化简 *)
  
  (** list (list A) 的化简 *)
  Definition dl_nsimp (dl : list (list A)) (n : nat) :=
    map (map (fun t => nsimp t n)) dl.
  
  (** list (list A) 上的 A -> R 的转换 *)
  Definition dl_A2R (dl : list (list A)) : list (list R) :=
    map (map A2R) dl.
  
  (* 以计算 1/2/3阶符号矩阵的逆矩阵为例，测试 RAST 的化简效果 *)
  
  Section Test.

    (* 定义多个变量 *)
    Variable r11 r12 r13 r21 r22 r23 r31 r32 r33 : R.
    Let a11 := ALit r11. Let a12 := ALit r12. Let a13 := ALit r13.
    Let a21 := ALit r21. Let a22 := ALit r22. Let a23 := ALit r23.
    Let a31 := ALit r31. Let a32 := ALit r32. Let a33 := ALit r33.
    
    (* 构造1/2/3阶矩阵 *)
    Let m1 := mk_mat_1_1 a11.
    Let m2 := mk_mat_2_2 a11 a12 a21 a22.
    Let m3 := mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.

    (* 计算逆矩阵 *)
    Let l1 := Eval cbv in m2l (minv m1).
    Let l2 := Eval cbv in m2l (minv m2).
    Let l3 := Eval cbv in m2l (minv m3).

    (* 可以看到，结果确实有冗余 *)
    (* Print l1.   (* [[(1 * (/ (0 + (a11 * 1)))) * (1 * 1)]] *) *)
    (* Print l2. *)
    (* Print l3. *)
    
    (* simp化简 *)
    (* Compute dl_nsimp l1 0. *)
    (* Compute dl_nsimp l1 1. *)
    (* Compute dl_nsimp l1 2. *)
    (* Compute dl_nsimp l1 3. *)
    (* Compute dl_nsimp l1 4. *)
    (* Compute dl_nsimp l1 5. *)
    (* Compute dl_nsimp l1 6. *)
    (* Compute dl_nsimp l1 7. *)
    (* Compute dl_nsimp l1 8. (* 已经最简 *) *)
    (* Compute dl_nsimp l1 9. *)
    (* 得到 R 类型上的结果 *)
    (* Compute dl_A2R (dl_nsimp l1 8). (** [[/r11]] *) *)

    (* Compute dl_A2R (dl_nsimp l2 5). *)
    (* Compute dl_A2R (dl_nsimp l2 10). *)
    (* Compute dl_A2R (dl_nsimp l2 15). *)
    (* Compute dl_A2R (dl_nsimp l2 20). (* 已经最简 *) *)
    (*
      = [[/ (r11 * r22 + - r12 * r21) * r22; - / (r11 * r22 + - r12 * r21) * r12];
      [- / (r11 * r22 + - r12 * r21) * r21; / (r11 * r22 + - r12 * r21) * r11]]
     *)

    (* Compute dl_A2R (dl_nsimp l3 5). *)
    (* Compute dl_A2R (dl_nsimp l3 20). *)
    (* Compute dl_A2R (dl_nsimp l3 30). *)
    (* Compute dl_A2R (dl_nsimp l3 40). *)
    (* Compute dl_A2R (dl_nsimp l3 42). (* 已经最简 *) *)
  (*
    = [[/ (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r22 * r33 +
    / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r23 * r32;
    - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r12 * r33 +
    - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r13 * r32;
    / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r12 * r23 +
    / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r13 * r22];
    [- / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r21 * r33 +
    - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r23 * r31;
    / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r11 * r33 +
    / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r13 * r31;
    - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r11 * r23 +
    - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r13 * r21];
    [/ (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r21 * r32 +
    / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r22 * r31;
    - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r11 * r32 +
    - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r12 * r31;
    / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r11 * r22 +
    / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r12 * r21]]
     : list (list R)
   *)
    
    (* 相比而言，matlab的输出结果更加友好
       注意：看起来是在显示时做了处理，如果拷贝出文本，看到的还是冗长的式子。

       这里是Matlab的输出，并拷贝出的结果（手动做了换行处理）：
[(r22*r33 - r23*r32)/(r11*r22*r33 - r11*r23*r32 - r12*r21*r33 + r12*r23*r31 + r13*r21*r32 - r13*r22*r31),
-(r12*r33 - r13*r32)/(r11*r22*r33 - r11*r23*r32 - r12*r21*r33 + r12*r23*r31 + r13*r21*r32 - r13*r22*r31),
(r12*r23 - r13*r22)/(r11*r22*r33 - r11*r23*r32 - r12*r21*r33 + r12*r23*r31 + r13*r21*r32 - r13*r22*r31);

 -(r21*r33 - r23*r31)/(r11*r22*r33 - r11*r23*r32 - r12*r21*r33 + r12*r23*r31 + r13*r21*r32 - r13*r22*r31),
(r11*r33 - r13*r31)/(r11*r22*r33 - r11*r23*r32 - r12*r21*r33 + r12*r23*r31 + r13*r21*r32 - r13*r22*r31),
-(r11*r23 - r13*r21)/(r11*r22*r33 - r11*r23*r32 - r12*r21*r33 + r12*r23*r31 + r13*r21*r32 - r13*r22*r31);

(r21*r32 - r22*r31)/(r11*r22*r33 - r11*r23*r32 - r12*r21*r33 + r12*r23*r31 + r13*r21*r32 - r13*r22*r31),
-(r11*r32 - r12*r31)/(r11*r22*r33 - r11*r23*r32 - r12*r21*r33 + r12*r23*r31 + r13*r21*r32 - r13*r22*r31),
(r11*r22 - r12*r21)/(r11*r22*r33 - r11*r23*r32 - r12*r21*r33 + r12*r23*r31 + r13*r21*r32 - r13*r22*r31)]

         这里是显示出来的效果（提取了公因式，并写成了分式的样子）：
[(r22*r33 - r23*r32)/s1, -(r12*r33 - r13*r32)/s1, (r12*r23 - r13*r22)/s1;
 -(r21*r33 - r23*r31)/s1, (r11*r33 - r13*r31)/s1, -(r11*r23 - r13*r21)/s1;
 (r21*r32 - r22*r31)/s1, -(r11*r32 - r12*r31)/s1, (r11*r22 - r12*r21)/s1]
 其中，s1 = r11*r22*r33 - r11*r23*r32 - r12*r21*r33 + r12*r23*r31 + r13*r21*r32 - r13*r22*r31
     *)

    (** 另一种思路，借用Coq的 ring_simplify *)
    Section Simplify_by_ring_simplify.
      (** 以3x3矩阵之逆矩阵的第(0,0)项为例 *)
      Let x := Eval cbv in  hd 0 (hd [] l3).
      (* Print x. *)

      (** 进入证明环境，命题本身不重要，只是为了借用化简能力 *)
      Goal forall a, a = A2R x.
      Proof.
        clear. unfold x. intros. simpl.
        ring_simplify. (* ring简化效果不佳 *)
        field_simplify. (* field简化很好 *)
        (* 手动记录这个结果：
           a = (r22 * r33 - r23 * r32) /
           (r11 * r22 * r33 - r11 * r23 * r32 - r22 * r31 * r13 -
           r33 * r12 * r21 + r23 * r12 * r31 + r32 * r21 * r13)
         *)
      Abort.

    End Simplify_by_ring_simplify.

    (** 无论何种方式，我们能够获取到简化的表达式，
        其正确性已经在前文完成 *)
      
  End Test.

  (** *** 构造用于矩阵元素的字符串名称 *)
  Section mat_element_string.
    
    (** 从 "a" 2 3 到 "a23" *)
    Definition nn2s (prefix:string) (i j:nat) : string :=
      (prefix ++ (nat2str (S i)) ++ (nat2str (S j)))%string.
    
    (** 构造矩阵需要的所有字符串变量 *)
    Definition mat_vars_s (r c:nat) : list (list string) :=
      map (fun i => map (nn2s "a" i) (seq 0 c)) (seq 0 r).

    (* 计算所有矩阵元素的字符串名称 *)
    (* Compute mat_vars_s 3 4. *)
    
    (* 当 100x100 规模时，约 2.5 s *)
    (* Time Eval cbv in (mat_vars_s 100 100). *)

    (* 取出单独的矩阵元素的字符串名称 *)
    (* Check nth 0 (mat_vars_s 3 4). *)
    (* Check nth 0 (nth 0 (mat_vars_s 3 4) []) "". *)
    (* Compute nth 0 (nth 0 (mat_vars_s 3 4) []) "". *)

  End mat_element_string.

  
  (** *** 任意维度的测试，自动构造变量 *)
  Module Test_any_dim.
        
    Open Scope nat.

    (** 虚拟的环境，可以将 string 映射到 A *)
    Variable env_s2A : string -> A.
    Coercion env_s2A : string >-> A.
    
    (** 矩阵的生成函数 *)
    Definition g_test r c := fun i j =>
      env_s2A (nth j (nth i (mat_vars_s r c) []) "").
    
    (* 当 200x200 规模时，计算一个元素，约 0.5 s。时间太长了 *)
    (* Time Compute g_test 200 200 5 6. *)

    (* 事先算好字符串，节省时间 *)
    Definition ORDERS := 6.  (* 设定阶数，行数、列数都等于它 *)
    Definition ROWS := ORDERS.
    Definition COLS := ORDERS.
    Definition mat_vars_given := Eval cbv in (mat_vars_s ROWS COLS).
    (* Print mat_vars_given. *)
    
    Definition g := fun i j =>
      env_s2A (nth j (nth i mat_vars_given []) "").
    
    (* 此时，取出元素速度较快 *)
    (* Compute g 1 2. *)
    
    Definition m : mat ROWS COLS := f2m g.
    
    (** 以下测试不要经常运行，太久 *)
    (* Time Compute minv m. *)
    (* Time Compute (m2l (minv m)). *)
    (* Time Definition m' := Eval cbv in (minv m). *)
    (* Time Definition dl := Eval cbv in (m2l m' (r:=ROWS) (c:=COLS)). *)

    (* Time Definition dl1 := Eval cbv in (dl_nsimp dl 2). (* 10 s *) *)
    (* Time Definition dl2 := Eval cbv in (dl_nsimp dl1 2). *) (* 20 s *)
    (* Time Definition dl3 := Eval cbv in (dl_nsimp dl2 2). *) (* 40 s *)
    
    (* Check dl1. *)
    (* Check (hd [] dl1). *)
    (* Check (hd A0 (hd [] dl1)). *)
    (* Compute (hd A0 (hd [] dl1)). *)
    (* Time Compute (hd A0 (hd [] (dl_nsimp dl 3))). *)
    (* Time Compute (hd A0 (hd [] (dl_nsimp dl 6))). (* 发现越来越复杂了 *) *)
    (* 注意，这里继续优化反而有问题，因为 nsimp 为是 ALit 而写的，
       这里的类型可能不适合 *)
    (* 重新写一版，针对 ALit 的*)
  
  End Test_any_dim.
  
  (* 几乎与 Test_any_dim 一样，只不过使用 ALit。
     即，定义在 R 上，并 ALit 到  A 类型，而不是直接定义在 A 上。*)
  Module Test_any_dim_ALit.
        
    Open Scope nat.
  
    (** 虚拟的环境，可以将 string 映射到 R。相比A，好处是R不会被展开 *)
    Variable env_s2R : string -> R.
    Coercion env_s2R : string >-> R.
    Coercion ALit : R >-> A.
    
    (** 矩阵的生成函数 *)
    Definition g_test r c := fun i j =>
      (ALit (env_s2R (nth j (nth i (mat_vars_s r c) []) ""))).
    
    (* 事先算好字符串，节省时间 *)
    Definition ORDERS := 4.  (* 设定阶数，行数、列数都等于它 *)
    Definition ROWS := ORDERS.
    Definition COLS := ORDERS.
    Definition mat_vars_given := Eval cbv in (mat_vars_s ROWS COLS).
    (* Print mat_vars_given. *)
    
    Definition g := fun i j =>
      (ALit (env_s2R (nth j (nth i mat_vars_given []) ""))).
    
    (* 此时，取出元素速度较快 *)
    (* Compute g 1 2. *)
    
    Definition m : mat ROWS COLS := f2m g.
    
    (* Time Compute minv m. *)
    (* Time Compute (m2l (minv m)). *)
    (* Time Definition m' := Eval cbv in (minv m). *)
    (* Time Definition dl := Eval cbv in (m2l m' (r:=ROWS) (c:=COLS)). *)

    (* Time Definition dl1 := Eval cbv in (dl_nsimp dl 2). *)
    (* Time Definition dl2 := Eval cbv in (dl_nsimp dl1 2). *)
    (* Time Definition dl3 := Eval cbv in (dl_nsimp dl2 10). *)
    (* Time Definition dl4 := Eval cbv in (dl_nsimp dl3 10). *)
    
    (* Eval cbv in (dl_nsimp dl2 20). *)
    (* Eval cbv in (dl_nsimp dl2 30). *)
    (* Eval cbv in (dl_nsimp dl2 40). *)
    (* Eval cbv in (dl_nsimp dl2 100). *)
    (* Eval cbv in (dl_nsimp dl2 150). *)

    (** 总结：
        1. matlab提供的符号矩阵确实很好。
        2. 这里的优化也许只要对单个表示（比如行列式）优化即可。
        3. 逆矩阵输出可能需要像matlab那样，用分式，并分离行列式这种公共表示更好
        4. 高于5、6阶，可能就没有什么意义了，人们并不会直接使用这么复杂的公式。
     *)

  
  End Test_any_dim_ALit.

End Simplify_by_RAST.


