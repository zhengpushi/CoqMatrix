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

Require Export MatrixThySig.
Require Export NatFun.MatrixThy.


(* ######################################################################### *)
(** * 通用的策略，以后要整理到一个合适的位置 *)

(** 列表相等转换为元素相等 *)
Ltac tac_listeq :=
  repeat match goal with
    | |- cons ?x1 ?l1 = cons ?x2 ?l2 => f_equal
    end.


(* ######################################################################### *)
(** * 全排列（简称排列） *)

(** 取出列表中第 k 个元素和剩下的列表 *)
Fixpoint pick {X} (X0 : X) (l : list X) (k : nat) : X * list X :=
  match k with
  | 0 => (hd X0 l, tl l)
  | S k' =>
      match l with
      | [] => (X0, [])
      | x :: l' =>
          let (a,l0) := pick X0 l' k' in
          (a, [x] ++ l0)
      end
  end.

(** 列表全排列的辅助函数 *)
Fixpoint perm_aux {X} (X0 : X) (n : nat) (l : list X) : list (list X) :=
  match n with
  | 0 => [[]]
  | S n' =>
      let d1 :=
        map (fun i => pick X0 l i) (seq 0 n) in
      let d2 :=
        map (fun k : X * list X =>
               let (x, lx) := k in
               let d3 := perm_aux X0 n' lx in
               map (fun l1 => [x] ++ l1) d3) d1 in
      concat d2
  end.

(** 列表全排列的辅助函数 *)
Definition perm {X} (X0 : X) (l : list X) : list (list X) :=
  perm_aux X0 (length l) l.

(* Compute perm 0 [1;2].
Compute perm 0 [1;2;3].
Compute perm 0 [1;2;3;4]. *)

(** 全排列的种数 *)
Definition Pn {X} X0 (l : list X) := length (perm X0 l).

(** 全排列种数等于阶乘 *)
Lemma Pn_eq : forall {X} X0 l, @Pn X X0 l = fact (length l).
Proof.
  intros X X0 l.
  induction l; simpl; auto.
Abort.


(* ######################################################################### *)
(** * Inversion of square matrix *)
Module Inversion (F : FieldSig).
  
  (** Carrier Type *)
  Module Export FieldThyInst := FieldThy F.
  
  (** Matrix Theory *)
  Module Export MatrixThyInst := MatrixThy F.
  
  (* ======================================================================= *)
  (** ** Determinant. *)
  
  (** Get the sub square matrix which remove r-th row and c-th column
    from a square matrix. *)
  Definition submat {n} (m : Square (S n)) (r c : nat) : Square n :=
    let g := mdata m in
    let g' :=
      (fun i j =>
         let i' := (if ltb i r then i else S i) in
         let j' := (if ltb j c then j else S j) in
         g i' j') in
    mk_mat n n g'.
  
  (** Determinant *)
  (* 原始版本 *)
  (*   Fixpoint det {n} : Square n -> X :=
    match n with
    | 0 => fun _ => X1
    | S n' => fun m =>
      let g := mdata m in
        fold_left Xadd (map (fun i =>
          let s := if Nat.even i then X1 else (-X1)%X in
          let a := g 0 i in
          let d := det (submat m 0 i) in
            (s * a * d)%X) (seq 0 n)) X0
    end. *)
  
  (* 优化1，s和a合并 *)
  Fixpoint det {n} : Square n -> X :=
    match n with
    | 0 => fun _ => X1
    | S n' =>
        fun m =>
          let g := mdata m in
          fold_left Xadd
            (map (fun i =>
                    let a := if Nat.even i then (g 0 i)%nat else (-(g 0 i)%nat)%X in
                    let d := det (submat m 0 i) in
                    (a * d)%X) (seq 0 n)) X0
    end.
  
  (** Verify formula for determinant of specify matrix *)
  Lemma det_1_1 : forall a, det (mk_mat_1_1 a) = a.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Lemma det_2_2 : forall a11 a12 a21 a22, 
      det (mk_mat_2_2 a11 a12 a21 a22) = (a11 * a22 - a12 * a21)%X.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Lemma det_3_3 : forall a11 a12 a13 a21 a22 a23 a31 a32 a33, 
      det (mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33) = 
        (a11*a22*a33 - a11*a23*a32 - 
           a12*a21*a33 + a12*a23*a31 + 
           a13*a21*a32 - a13*a22*a31)%X.
  Proof.
    intros. cbv. ring.
  Qed.
  
  (* ======================================================================= *)
  (** ** 克拉默法则. *)
  
  (** 替换方阵某一列的内容 *)
  Definition mchgcol {n} (m : Square n) (k : nat) (v : M n 1) : Square n :=
    let f := mdata m in
    let g := mdata v in
    let f' := fun i j => if (Nat.eqb j k) then (g i 0)%nat else f i j in
    mk_mat _ _ f'.
  
  (** 克拉默法则将给出X。注意，D不为零时才有解 *)
  Definition cramerRule {n} (X : Square n) (b : M n 1) : M n 1 :=
    let f := mdata X in
    let D := det X in
    let g := (fun i j =>
                let Di := det (mchgcol X i b) in
                (Di / D)%X) in
    mk_mat _ _ g.
  
  
  (* ======================================================================= *)
  (** ** 伴随矩阵，简称伴随阵. *)
  
  (** 有各个元素的代数余子式以转置的样式构成的新矩阵，称为原矩阵的伴随矩阵
    adjoint matrix, adjugate matrix, 
    adj(X), X* *)
  
  Definition madj {n} : Square n -> Square n := 
    match n with
    | O => fun m => m 
    | S n' =>
        fun m =>
          (let f := mdata m in
           let g :=
             (fun i j =>
                let s := if Nat.even (i + j) then X1 else (-X1)%X in
                let d := det (submat m j i) in 
                (s * d)%X) in
           mk_mat _ _ g)
    end.
  
  
  (* ======================================================================= *)
  (** ** 逆矩阵 *)
  Definition minv {n} (m : Square n) := mcmul (X1/det m) (madj m).
  
  (** Verify formula for inversion of specify matrix *)
  Lemma inv_1_1 : forall a, a <> X0 -> m2l (minv (mk_mat_1_1 a)) = [[X1/a]].
  Proof.
    intros. cbv. f_equal;f_equal. field. auto.
  Qed.
  
  Lemma inv_2_2 : forall a11 a12 a21 a22 : X, 
      let d := (a11 * a22 - a12 * a21)%X in
      d <> X0 ->
      m2l (minv (mk_mat_2_2 a11 a12 a21 a22)) =
        ([[a22/d; -a12/d]; [-a21/d; a11/d]])%X.
  Proof.
    intros. cbv. tac_listeq; try field; auto.
  Qed.
  
  (* 注意，以下公式可由matlab来提供，避免手写 *)
  Lemma inv_3_3 : forall a11 a12 a13 a21 a22 a23 a31 a32 a33, 
      let d := (a11*a22*a33 - a11*a23*a32 - a12*a21*a33 + 
                  a12*a23*a31 + a13*a21*a32 - a13*a22*a31)%X in
      d <> X0 ->
      m2l (minv (mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33)) =
        ([[(a22*a33 - a23*a32)/d; -(a12*a33 - a13*a32)/d; (a12*a23 - a13*a22)/d];
          [-(a21*a33 - a23*a31)/d; (a11*a33 - a13*a31)/d; -(a11*a23 - a13*a21)/d];
          [(a21*a32 - a22*a31)/d; -(a11*a32 - a12*a31)/d; (a11*a22 - a12*a21)/d]
        ])%X.
  Proof.
    intros. cbv. tac_listeq; try field; auto.
  Qed.
  
  (** 直接计算出1/2/3阶符号矩阵的逆矩阵 *)
  Section FindFormula.
    Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : X.
    Let m1 := mk_mat_1_1 a11.
    Let m2 := mk_mat_2_2 a11 a12 a21 a22.
    Let m3 := mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.
    
    (* 虽然结果正确，但是太过冗长，以后使用 RAST 来化简 *)
  (*     Compute (m2l (minv m1)).
    Compute (m2l (minv m2)).
    Compute (m2l (minv m3)). *)
    
  End FindFormula.

End Inversion.


(** Test for Inversion *)
Module Test_for_Inversion.

  (* 用Qc来测试，比较直观 *)
  Import QArith Qcanon.
  Module Import InversionQc := Inversion FieldQc.FieldDefQc.
  Open Scope Q.
  Open Scope Qc_scope.

  Coercion Q2Qc : Q >-> Qc.
  
  (* 符号 *)
  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : Qc.
  
  (* 2x2的数值矩阵、符号矩阵 *)
  Definition m20 := mk_mat_2_2 1 2 3 4.
  Definition m21 := mk_mat_2_2 a11 a12 a21 a22.
  
  (* 3x3的数值矩阵、符号矩阵 *)
  Definition m30 := mk_mat_3_3 1 2 3 4 5 6 7 8 9.
  Definition m31 := mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.
  
  (* 余子式 *)
  (*   Compute (m2l (submat m30 0 1)).
  Compute (m2l (submat m31 2 1)). *)
  
  (* 计算行列式 *)
  (*   Compute det m20.
  Compute det m30.
  Eval cbn in det m21.
  Eval cbn in det m31. *)
  
  (* 克拉默法则 *)
  Variable b1 b2 b3 : Qc.
  Definition v31 := mk_mat_3_1 b1 b2 b3.
(*   Compute (m2l m30).
  Compute (m2l (mchgcol m30 2 v31)).
  Eval cbn in det (mchgcol m30 2 v31).
  Eval cbn in cramerRule m30 v31. *)
  
  (* 伴随矩阵 *)
(*   Compute (m2l (madj m20)).
  Compute (m2l (madj m30)). *)
  
  (* 逆矩阵 *)
(*   Compute (m2l (minv m20)).
  Compute (m2l (minv m30)).
  Eval cbn in (m2l (minv m21)).
  Eval cbn in (m2l (minv m31)). *)
  
End Test_for_Inversion.


(** 同济大学，线性代数（第五版），page25, 习题一 *)
(** 数值矩阵部分，使用特定的域会便于计算，但涉及到符号时，会展开为复杂的表达式，
不便于符号矩阵的证明 *)
Module Exercise_Ch1_Number.

  (* 用Qc来测试，比较直观 *)
  Import QArith Qcanon.
  Module Import InversionQc := Inversion FieldQc.FieldDefQc.
  Open Scope Q.
  Open Scope Qc_scope.

  Coercion Q2Qc : Q >-> Qc.
  
  
  (** 同济大学，线性代数（第五版），page22, 例14 *)
  Section example14.
    Let D := mk_mat_4_4 
               2 1 (-5) 1
               1 (-3) 0 (-6)
               0 2 (-1) 2
               1 4 (-7) 6.
    Let b := mk_mat_4_1 8 9 (-5) 0.
    
    (*     Compute (m2l (cramerRule D b)). *)
  End example14.
  
  Section example15.
    Let D := mk_mat_4_4 
               1 1 1 1
               1 2 4 8
               1 3 9 27
               1 4 16 64.
    Let b := mk_mat_4_1 3 4 3 (-3).
    
    (*     Compute (m2l (cramerRule D b)). *)
  End example15.

  (** ex1 *)
  Section ex_1.
    (*     Compute (det (mk_mat_3_3 2 0 1 1 (-4) (-1) (-1) 8 3)). *)

    Variable a b c : Qc.
    (*     Eval cbn in det (mk_mat_3_3 a b c b c a c a b). *)
    (* ToDo: 不在证明模式时，如何利用Coq环境化简上述表达式？ *)
  End ex_1.
End Exercise_Ch1_Number.


(** 符号矩阵部分，在符号这一级方便证明 *)
Module Exercise_Ch1_Symbol.

  Declare Module F : FieldSig.
  Module Import InversionInst := Inversion F.
  
  Notation "2" := (1 + 1)%X.
  Notation "3" := (1 + 2)%X.
  
  (* X上的幂函数 *)
  Fixpoint Apow (a : X) (n : nat) :=
    match n with
    | 0 => X1
    | S n' => (a * (Apow a n'))%X
    end.
  Infix "^" := (Apow).
  
  Example ex6_1 : forall a b : X,
      let m := (mk_mat_3_3 (a*a) (a*b) (b*b) (2*a) (a+b) (2*b) 1 1 1)%X in
      det m = (a - b)^3.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Example ex6_2 : forall a b x y z : X,
      let m1 := (mk_mat_3_3
                   (a*x+b*y) (a*y+b*z) (a*z+b*x)
                   (a*y+b*z) (a*z+b*x) (a*x+b*y)
                   (a*z+b*x) (a*x+b*y) (a*y+b*z))%X in
      let m2 := mk_mat_3_3 x y z y z x z x y in
      det m1 = ((a^3 + b^3) * det m2)%X.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Example ex6_3 : forall a b e d : X,
      let m := (mk_mat_4_4
                  (a*a) ((a+1)^2) ((a+2)^2) ((a+3)^2)
                  (b*b) ((b+1)^2) ((b+2)^2) ((b+3)^2)
                  (e*e) ((e+1)^2) ((e+2)^2) ((e+3)^2)
                  (d*d) ((d+1)^2) ((d+2)^2) ((d+3)^2))%X in
      det m = 0.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Example ex6_4 : forall a b e d : X,
      let m := (mk_mat_4_4
                  1 1 1 1
                  a b e d
                  (a^2) (b^2) (e^2) (d^2)
                  (a^4) (b^4) (e^4) (d^4))%X in
      det m = ((a-b)*(a-e)*(a-d)*(b-e)*(b-d)*(e-d)*(a+b+e+d))%X.
  Proof.
    intros. cbv. ring.
  Qed.
  
  (** 6.(5) 是无穷的，需要更多构造和证明，待以后补充 *)

End Exercise_Ch1_Symbol.

(** 使用实数的AST，看能否得到简化的逆矩阵表达式 *)
Module Simplify_by_RAST.
  
  Import RAST.
  Module Import InversionInst := Inversion FieldT.FieldDefT.
  
  Notation "0" := T0.
  Notation "1" := T1.
  Notation "2" := (1 + 1)%X.
  Notation "3" := (1 + 2)%X.
  Infix "+" := Tadd.
  Infix "-" := Tsub.
  Infix "*" := Tmul.
  
  (* simp 函数可以化简一个项，我们需要对 list 和 list list 进行化简 *)
  
  (** list (list T) 的化简 *)
  Definition dl_nsimp (dl : list (list T)) (n : nat) :=
    map (map (fun t => nsimp t n)) dl.
  
  (** list (list T) 上的 AST -> R 的转换 *)
  Definition dl_T2R (dl : list (list T)) : list (list R) :=
    map (map T2R) dl.
  
  (* 以计算 1/2/3阶符号矩阵的逆矩阵为例，测试 RAST 的化简效果 *)
  
  (* 第一版，大概测试一下 *)
  Section TestV1.
    (* 定义多个变量 *)
    Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : X.
    
    (* 构造1/2/3阶矩阵 *)
    Let m1 := mk_mat_1_1 a11.
    Let m2 := mk_mat_2_2 a11 a12 a21 a22.
    Let m3 := mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.

    (* 计算逆矩阵 *)
    Let l1 := Eval cbv in m2l (minv m1).
    Let l2 := Eval cbv in m2l (minv m2).
    Let l3 := Eval cbv in m2l (minv m3).
    
    (* 可以看到，结果确实有冗余 *)
  (*     Print l1.   (* [[(1 * (/ (0 + (a11 * 1)))) * (1 * 1)]] *)
    Print l2.
    Print l3. *)
    
    (* 可以看到，simp有一定的效果，但还不彻底，需要更强的 simp *)
    (*     Compute dl_nsimp l1 10. (* [[(/ (0 + (a11 * 1)))%T]] *) *)
    
  (* 再看 AST -> R 之后的结果，看到有未展开的函数抽象，可能与 a11 的定义方式
      有关。下一节准备用 TLit (r : R) 来构造，再次测试 *)
    (*     Compute T2R ((/ (0 + (a11 * 1)))%T). *)
  End TestV1.
  
  (** 第2版，改用 TLit (r : R) 来定义变量 *)
  Section TestV2.
    Open Scope R.
    Variable r11 r12 r13 r21 r22 r23 r31 r32 r33 : R.
    Let a11 := TLit r11. Let a12 := TLit r12. Let a13 := TLit r13.
    Let a21 := TLit r21. Let a22 := TLit r22. Let a23 := TLit r23.
    Let a31 := TLit r31. Let a32 := TLit r32. Let a33 := TLit r33.
    
    Let m1 := mk_mat_1_1 a11.
    Let m2 := mk_mat_2_2 a11 a12 a21 a22.
    Let m3 := mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.

    (* 行列式表达式 *)
    (*     Compute T2R (nsimp (det m1) 10).  (* = r11 *)
    Compute T2R (nsimp (det m2) 10).  (* = (r11 * r22 + - r12 * r21)%R *)
    
    Compute (det m3).
    Compute T2R (det m3).
    Compute T2R (nsimp (det m3) 30).  (*
      r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + 
      - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31 *)
     *)    
    (* 逆矩阵表达式 *)
    Let l1 := Eval cbv in m2l (minv m1).
    Let l2 := Eval cbv in m2l (minv m2).
    Let l3 := Eval cbv in m2l (minv m3).
    (*     Compute l1. (* [[1 * / (0 + TLit r11 * 1) * (1 * 1)]] *)
    Compute dl_nsimp l1 10. (* [[(/ TLit r11)%T]] *)
    Compute T2R (/ TLit r11)%T. (* (/ r11)%R *)
    Compute dl_T2R (dl_nsimp l1 10). (*
      = [[(/ r11)%R]] *) *)
    
    (*     Compute l2.
    Compute dl_nsimp l2 20.
    Compute dl_T2R (dl_nsimp l2 20). (*
    = [[/ (r11 * r22 + - r12 * r21) * r22; - / (r11 * r22 + - r12 * r21) * r12];
       [- / (r11 * r22 + - r12 * r21) * r21; / (r11 * r22 + - r12 * r21) * r11]]
     *) *)
    
    (*     Compute dl_T2R (dl_nsimp l3 50). (* *)
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
    (* 基本上得到与 Matlab一样的结果 *)
    
    (* 以第一项为例，可以得到证明 *)
    
    (* 先给出3x3矩阵行列式的表达式 *)
    Let det_m3_exp := r11*r22*r33 - r11*r23*r32 - r12*r21*r33 +
                        r12*r23*r31 + r13*r21*r32 - r13*r22*r31.
    
    (* 再证明该表达式确实等于行列式 *)
    Let det_m3_exp_ok : det_m3_exp = T2R (det m3).
    Proof.
      cbv. ring.
    Qed.
    
    (* 证明逆矩阵第一项，确实等于 Matlab 给出的那个结果 *)
    Let inv_a11_ok : T2R (det m3) <> 0 -> 
                     / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r22 * r33 +
                       / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r23 * r32 
                     = (r22*r33 - r23*r32)/(r11*r22*r33 - r11*r23*r32 - r12*r21*r33 + r12*r23*r31 + r13*r21*r32 - r13*r22*r31).
    Proof.
      clear l1 l2 l3. intros. field.
      rewrite <- det_m3_exp_ok in H. auto.
    Qed.
    
  End TestV2.
  
  (** 任意纬度的测试，自动构造变量 *)
  Module TestV3_any_dim.
    
    Open Scope nat.

    (** 从 "a" 2 3 到 "a23" *)
    Definition nn2s (prefix:string) (i j:nat) : string :=
      (prefix ++ (nat2str i) ++ (nat2str j))%string.
    
    (** 构造矩阵需要的所有字符串变量 *)
    Definition mat_vars_s (r c:nat) : list (list string) :=
      map (fun i => map (nn2s "a" i) (seq 0 c)) (seq 0 r).
    
    (*     Compute mat_vars_s 3 4. *)
    
    (** 虚拟的环境，可以将 string 映射到 R *)
    Variable env_s2T : string -> T.
    
    Coercion env_s2T : string >-> T.
    
    (*     Check nth 0 (mat_vars_s 3 4).
    Check nth 0 (nth 0 (mat_vars_s 3 4) []) "".
    Compute nth 0 (nth 0 (mat_vars_s 3 4) []) "".
     *)    
    (** 矩阵的生成函数 *)
    Definition g' r c : MATData T := fun i j =>
                                       env_s2T (nth j (nth i (mat_vars_s r c) []) "").
    
    (* 当 200x200 规模时，计算一个元素，约 0.5 s *)
    (*     Time Compute g' 200 200 5 6. *)
    
    (* 手动设定阶数，行数、列数都等于它 *)
    Definition ORDERS := 6.
    Definition ROWS := ORDERS.
    Definition COLS := ORDERS.
    
    (* 事先算好字符串，节省时间。当100x100规模时，约 2.5s *) 
    Definition mat_vars_given := Eval cbv in (mat_vars_s ROWS COLS).

    (*     Print mat_vars_given. *)
    
    Definition g : MATData T := fun i j =>
                                  env_s2T (nth j (nth i mat_vars_given []) "").
    
    (* 此时，取出元素速度较快 *)
    (*     Compute g 1 9. *)
    
    Definition m := mk_mat ROWS COLS g.
    
    (*     Time Compute minv m. *)
    (*     Time Compute (m2l (minv m)). *)
  (*     Time Definition m' := Eval cbv in (minv m).
    Time Definition dl := Eval cbv in (m2l m').
    Time Definition dl1 := Eval cbv in (dl_nsimp dl 2).
    
    Check dl1.
    Check (hd [] dl1).
    Check (hd T0 (hd [] dl1)).
    Compute (hd T0 (hd [] dl1)).
    Compute (hd T0 (hd [] (dl_nsimp dl 3))).
    Let t1 := Eval cbv in (hd T0 (hd [] (dl_nsimp dl 0))).
    Print t1. *)
  (* 注意，这里继续优化反而有问题，因为 nsimp 为是 TLit 而写的，
    这里的类型可能不适合 *)
    
    (* 重新写一版，针对 TLit 的*)
    
  End TestV3_any_dim.
  
  (* 几乎与 TestV3_any_dim 一样，只不过使用 TLit *)
  Module TestV4_any_dim_TLit.
    
    Open Scope nat.

    (** 从 "a" 2 3 到 "a23" *)
    Definition nn2s (prefix:string) (i j:nat) : string :=
      (prefix ++ (nat2str i) ++ (nat2str j))%string.
    
    (** 构造矩阵需要的所有字符串变量 *)
    Definition mat_vars_s (r c:nat) : list (list string) :=
      map (fun i => map (nn2s "a" i) (seq 0 c)) (seq 0 r).
    
    (*     Compute mat_vars_s 3 4. *)
    
    (** 虚拟的环境，可以将 string 映射到 R *)
    Variable env_s2R : string -> R.
    
    Coercion env_s2R : string >-> R.
    
    (*     Check nth 0 (mat_vars_s 3 4).
    Check nth 0 (nth 0 (mat_vars_s 3 4) []) "".
    Compute nth 0 (nth 0 (mat_vars_s 3 4) []) "". *)
    
    (** 矩阵的生成函数 *)
    Definition g' r c : MATData T :=
      fun i j => (TLit (env_s2R (nth j (nth i (mat_vars_s r c) []) ""))).
    
    Coercion TLit : R >-> T.
    
    (* 当 200x200 规模时，计算一个元素，约 0.5 s *)
    (*     Time Compute g' 200 200 5 6. *)
    
    (* 手动设定阶数，行数、列数都等于它 *)
    Definition ORDERS := 6.
    Definition ROWS := ORDERS.
    Definition COLS := ORDERS.
    
    (* 事先算好字符串，节省时间。当100x100规模时，约 2.5s *) 
    Definition mat_vars_given := Eval cbv in (mat_vars_s ROWS COLS).

    (*     Print mat_vars_given. *)
    
    Definition g : MATData T :=
      fun i j => (TLit (env_s2R (nth j (nth i mat_vars_given []) ""))).
    
    (* 此时，取出元素速度较快 *)
    (*     Compute g 1 9. *)
    
    Definition m := mk_mat ROWS COLS g.
    
    (*     Time Compute minv m. *)
    (*     Time Compute (m2l (minv m)). *)
  (*     Time Definition m' := Eval cbv in (minv m).
    Time Definition dl := Eval cbv in (m2l m').
    Time Definition dl1 := Eval cbv in (dl_nsimp dl 2). *)
    
  (*     Check dl1.
    Check (hd [] dl1).
    Check (hd T0 (hd [] dl1)).
    Compute (hd T0 (hd [] dl1)).
    Compute (hd T0 (hd [] (dl_nsimp dl 3))).
    Let t1 := Eval cbv in (hd T0 (hd [] (dl_nsimp dl 0))).
    Print t1.
    Let t2 := Eval cbv in (hd T0 (hd [] (dl_nsimp dl 5))).
    Print t2. *)
  (* 还是不行，越优化效果越差。
    下次，从 4 阶开始查 优化算法。*)
    
  End TestV4_any_dim_TLit.

End Simplify_by_RAST.


