(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Reproduce the results of a paper
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
  1. 这是对论文 "Formal verification of Matrix based MATLAB models using 
    interactive theorem proving" 结果的重现，同时也验证这个矩阵库的适应能力。
*)


Require Import FieldStruct.
Require Import Function.MatrixThy.

Require Import ListListExt.
Require Import Lia.

Require Import Setoid.  (* ==> *)


(* ######################################################################### *)
(** * Instantiate matrix theory *)
Module MatrixThy := MatrixThy FieldR.
Export MatrixThy.

Open Scope R.

(* 打印矩阵元素 *)
Definition mprint {M N} (m : mat M N) :=
  let g := mdata m in
    let rows := map (fun i => g i) (seq 0 M) in
      let elems := map (fun row => map (fun j => row j) (seq 0 N)) rows in
        elems.

Definition m1 : mat 2 3 := mk_mat _ _ (fun i j => INR (i+j)).
Compute mprint m1.

(* ######################################################################### *)
(** * Multivariate Theory in HOL LIGHT *)


(* Def1，矩阵乘法 *)
Definition matrix_mul {M N P} (A : mat M N) (B : mat N P) := mmul A B.

(* Def2, 矩阵转置 *)
Definition transp {M N} (A : mat M N) := mtrans A. 

(* Def3, 取出矩阵的一行或一列 *)
Definition row {M N} (A : mat M N) (i : nat) :=
  let g := mdata A in 
(*     mk_mat M 1 (fun _ j => g i j)   (* 定义为矩阵 *). *)
    (fun j => g i j)    (* 定义为函数 *).

Definition column {M N} (A : mat M N) (j : nat) :=
  let g := mdata A in 
(*     mk_mat 1 N (fun i _ => g i j)   (* 定义为矩阵 *). *)
    (fun i => g i j)    (* 定义为函数 *).

(* Def4, 对角矩阵 *)
Definition dmat {M N} (k : R) :=
  mk_mat M N (fun i j => if i =? j then k else R0).

(* Def5, 向量，无限长的一个常数序列 *)
Definition vec (n : nat) := fun (i : nat) => INR n.

(* Def6, 行向量、列向量，由一个生成函数 v 来构造 *)
Definition rowvector {N} (v : nat -> R) : mat N 1 :=
  mk_mat N 1 (fun i j => if j =? 0 then v i else R0).

Definition columnvector {N} (v : nat -> R) : mat 1 N :=
  mk_mat 1 N (fun i j => if i =? 0 then v j else R0).

(* Def7, 向量化，将 MxN矩阵转换为一个 M*N维的向量。
  以 M=2,N=3 为例
  i   1+(i-1)/N   1+(i-1)%N
  0   1           1
  1   1           1
  2   1           2
  3   1           3
  4   2           1
  5   2           2
  6   2           3
  7   3           1
  看起来，这里的下标是从1开始的，为何不从0开始呢？
*)
Definition vectorize {M N} (A : mat M N) : nat -> R :=
  let g := mdata A in
    fun i => g (Nat.div (i-1) N) (Nat.modulo (i-1) N).

Section test.
  
  Let m1 : mat 2 3 := l2m [[1;2;3];[4;5;6]]%R.
  Let v1 := vectorize m1.
  
  (* 取出从0开始的 前10个元素 *)
  Compute map (fun i => v1 i) (seq 0 10).
  
End test.

(* Def8, 矩阵化，将一个 M*N 维的向量转换为一个 MxN 矩阵。
其实，Def7和Def8也说明了一个公式： (x^a)^b = x^(a*b) *)

Definition Matrify {M N} (x : nat -> R) : mat M N :=
  mk_mat M N (fun i j => x (i * N + j)%nat).

Section test.
  
  Let x1 := fun n => INR n.
  Let m1 : mat 2 3 := Matrify x1.
  
  (* 取出元素 *)
  Let f := mdata m1.
  Compute
    let lst := map (fun i => f i) (seq 0 2) in
      map (fun l => map (fun j => l j) (seq 0 3)) lst.
  
End test.


(* ######################################################################### *)
(** * Formalization of matrix functions in HOL LIGHT *)

(* 上下翻转 *)
Definition flipud {M N} (m : mat M N) : mat M N :=
  let g := mdata m in
    mk_mat _ _ (fun i j => g (M - i - 1)%nat j).
    

(* 旋转90度（逆时针）
 1 2 3 =>  3 6
 4 5 6     2 5
           1 4
 拆分为基本操作如下
 (1) 转置为
 1 4
 2 5
 3 6
 (2) 所有行进行一次翻转(rev)，即上下翻转 flip_u_d
*)
Definition rot90 {M N} (A : mat M N) : mat N M :=

(* 翻转多个90度，就是多次作用 *)
Definition rot90_matrix {M N} (A : mat M N) (n : nat) :=


  let g := mdata A in
    fun i => g (Nat.div (i-1) N) (Nat.modulo (i-1) N).

Section test.
  
  Let m1 : mat 2 3 := l2m [[1;2;3];[4;5;6]]%R.
  Let v1 := vectorize m1.
  
  (* 取出从0开始的 前10个元素 *)
  Compute map (fun i => v1 i) (seq 0 10).
  
End test.


Module VectorThy (E : FieldSig) <: VectorThySig.
  
  (* ======================================================================= *)
  
  
  (* ======================================================================= *)
  (** ** Vector type *)
  
  Declare Scope vec_scope.
  Delimit Scope vec_scope with V.
  Open Scope vec_scope.
  
  Definition vec n := mat n 1.
  
  (** Get generate function of the vector *)
  Definition vdata {n} (v : vec n) : nat -> A :=
    let g := mdata v in
      fun i => g i 0.
  
  
  (* ======================================================================= *)
  (** ** Vector equility *)
  Definition veq {n} (v1 v2 : vec n) := meq v1 v2.
  
  Notation "v1 == v2 " := (@veq _ v1 v2) (at level 70).
  
  Lemma veq_refl : forall {n} (v : vec n), v == v.
  Proof. intros. apply meq_refl. Qed.
   
  Lemma veq_sym : forall {n} (v1 v2 : vec n), v1 == v2 -> v2 == v1.
  Proof. intros. apply meq_sym. easy. Qed.
  
  Lemma veq_trans : forall {n} (v1 v2 v3 : vec n), 
    v1 == v2 -> v2 == v3 -> v1 == v3.
  Proof. intros. apply meq_trans with (m2:=v2); auto. Qed.
  
  Lemma veq_dec : forall {n} (v1 v2 : vec n), {v1 == v2} + {not (v1 == v2)}.
  Proof. intros. apply meq_dec. Qed.
  
  
  (* ======================================================================= *)
  (** ** Convert between tuples and vector *)
  Definition t2v_2 (t : @T2 A) : vec 2 := 
    let '(a,b) := t in l2m [[a];[b]].
    
  Definition t2v_3 (t : @T3 A) : vec 3 := 
    let '(a,b,c) := t in l2m [[a];[b];[c]].
    
  Definition t2v_4 (t : @T4 A) : vec 4 := 
    let '(a,b,c,d) := t in l2m [[a];[b];[c];[d]].
  
  
  Definition v2t_2 (v : vec 2) : @T2 A :=
    let g := vdata v in (g 0, g 1).

  Definition v2t_3 (v : vec 3) : @T3 A :=
    let g := vdata v in (g 0, g 1, g 2).
    
  Definition v2t_4 (v : vec 4) : @T4 A :=
    let g := vdata v in (g 0, g 1, g 2, g 3).
  
  Lemma v2t_t2v_id_2 : forall (t : A * A), v2t_2 (t2v_2 t) = t.
  Proof.
    intros. destruct t. simpl. unfold v2t_2. simpl. f_equal.
  Qed.
  
  Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v.
  Proof.
    intros. intros i j Hi Hj. simpl.
    repeat (try destruct i; try destruct j; auto; try lia).
  Qed.
  
  
  (* ======================================================================= *)
  (** ** Convert between list and vector *)
  Definition v2l {n} (v : vec n) : list A := MCol 0 v.
  Definition l2v (l : list A) : vec (length l) := l2m (cvt_row2col l).
  
  
  (* ======================================================================= *)
  (** ** Zero vector *)
  Definition vec0 n : vec n := mat0 n 1.

  (** Assert that a vector is an zero vector. *)
  Definition vzero {n} (v : vec n) : Prop := @meq n 1 v (vec0 n).

  (** Assert that a vector is an non-zero vector. *)
  Definition vnonzero {n} (v : vec n) : Prop := ~(vzero v).
  
  (** vec0 is equal to mat0 with column 1 *)
  Lemma vec0_eq_mat0 : forall n, vec0 n == mat0 n 1.
  Proof. intros. easy. Qed.

  (** It is decidable that if a vector is zero vector. *)
  Lemma vzero_dec : forall {n} (v : vec n), {vzero v} + {vnonzero v}.
  Proof. intros. apply meq_dec. Qed.
  
  
  (* ======================================================================= *)
  (** ** algebra operations *)
  
  (** 一个向量的映射 *)
  Definition vmap {n} (v : vec n) f : vec n := mmap f v.
  
  (** 一个向量的fold操作 *)
(*   Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)
  
  (** 两个向量的映射 *)
  Definition vmap2 {n} (v1 v2 : vec n) f : vec n := mmap2 f v1 v2.
  
  (* 两个向量的点积。这里用矩阵乘法来定义点积，而我们之前是用点积来定义乘法 *)
  Definition vdot {n : nat} (A : vec n) (B : vec n) :=
    scalar_of_mat (@mmul 1 n 1 (mtrans A) B).

  (** 向量加法 *)
  Definition vadd {n} (v1 v2 : vec n) : vec n := madd v1 v2.
  Infix "+" := vadd.

  (** 向量加法交换律 *)
  Lemma vadd_comm : forall {n} (v1 v2 : vec n), @meq n 1 (v1 + v2) (v2 + v1).
  Proof. intros. apply madd_comm. Qed.

  (** 向量加法结合律 *)
  Lemma vadd_assoc : forall {n} (v1 v2 v3 : vec n), 
    @meq n 1 ((v1 + v2) + v3) (v1 + (v2 + v3)).
  Proof. intros. apply madd_assoc. Qed.

  (** 向量左加0 *)
  Lemma vadd_zero_l : forall {n} (v : vec n), @meq n 1 ((vec0 n) + v) v.
  Proof. intros. apply (@madd_0_l n 1). Qed.

  (** 向量右加0 *)
  Lemma vadd_zero_r : forall {n} (v : vec n), @meq n 1 (v + (vec0 n)) v.
  Proof. intros. apply (@madd_0_r n 1). Qed.

  (** 负向量 *)
  Definition vopp {n} (v : vec n) : vec n := mopp v.
  Notation "- v" := (vopp v).

  (** 加上负向量等于0 *)
  Lemma vadd_vopp : forall {n} (v : vec n), @meq n 1 (v + (- v)) (vec0 n).
  Proof. intros. apply (@madd_mopp n 1). Qed.

  (** 向量减法 *)
  Definition vsub {n} (v1 v2 : vec n) : vec n := v1 + (- v2).
  Infix "-" := vsub.
  
  (** 取元素 *)
  Definition vnth {n} (v : vec n) i : A := @mnth n 1 v i 0.
  
  Notation "v # i" := (vnth v i) (at level 30).

  (** 取出1x1矩阵的第 0,0 个元素 *)
  Definition scalar_of_mat (m : mat 1 1) := mnth m 0 0.

  (** 向量数乘 *)
  Definition vcmul {n} a (v : vec n) : vec n := a c* v.
  Definition vmulc {n} (v : vec n) a : vec n := v *c a.
  
  (** veq与vcmul的相容性 *)
  Add Parametric Morphism n : (@vcmul n)
    with signature eq ==> veq ==> veq as vcmul_mor.
  Proof.
    intros a [g1] [g2] H. unfold veq, meq in *; simpl in *. intros.
    assert (g1 i j = g2 i j); auto. rewrite H2. auto.
  Qed.

  (** 右数乘和左数乘等价 *)
  Lemma vmulc_eq_vcmul : forall {n} a (v : vec n), @meq n 1 (v *c a) (a c* v).
  Proof. intros. rewrite mmulc_eq_mcmul. easy. Qed.

  (** 数乘结合律1 *)
  Lemma vcmul_assoc1 : forall {n} a b (v : vec n), 
    a c* (b c* v) == (a * b) c* v.
  Proof. intros. rewrite mcmul_assoc1. easy. Qed.

  (** 数乘结合律2 *)
  Lemma vcmul_assoc2 : forall {n} a b (v : vec n), 
    a c* (b c* v) == b c* (a c* v).
  Proof. intros. rewrite mcmul_assoc2. easy. Qed.

  (** 数乘左分配律 *)
  Lemma vcmul_vadd_distr_l : forall {n} a b (v : vec n), 
    (a + b)%A c* v == (a c* v) + (b c* v).
  Proof. intros. rewrite mcmul_madd_distr_r. easy. Qed.

  (** 数乘右分配律 *)
  Lemma vcmul_vadd_distr_r : forall {n} a (v1 v2 : vec n), 
    a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. unfold veq,vadd. rewrite mcmul_madd_distr_l. easy. Qed.

  (** 用1数乘 *)
  Lemma vcmul_1_l : forall {n} (v : vec n), @meq n 1 (A1 c* v) v.
  Proof. intros. rewrite mcmul_1_l. easy. Qed.

  (** 用0数乘 *)
  Lemma vcmul_0_l : forall {n} (v : vec n), @meq n 1 (A0 c* v) (vec0 n).
  Proof. intros. rewrite mcmul_0_l. easy. Qed.

  (** 非零向量是k倍关系，则系数k不为0 *)
  Lemma vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : vec n) k,
    vnonzero v1 -> vnonzero v2 -> (@meq n 1 v1 (k c* v2)) -> k <> A0.
  Proof.
    intros. intro. subst. rewrite vcmul_0_l in H1. easy.
  Qed.
  
  
  (* ======================================================================= *)
  (** ** 2-dim vector operations *)

  (** 2维向量的“长度”，这里不是欧式距离，而是欧式距离的平方，为了方便计算 *)
  Definition vlen2 (v : vec 2) : A :=
    let '(x,y) := v2t_2 v in
      (x * x + y * y)%A.
  
  
  (* ======================================================================= *)
  (** ** 3-dim vector operations *)

  (** 3维向量的“长度”，这里不是欧式距离，而是欧式距离的平方，为了方便计算 *)
  Definition vlen3 (v : vec 3) : A :=
    let '(x,y,z) := v2t_3 v in
      (x * x + y * y + z * z)%A.
      
  (** V3的点积 *)
  Definition vdot3 (v0 v1 : vec 3) : A :=
    let '(a0,b0,c0) := v2t_3 v0 in
    let '(a1,b1,c1) := v2t_3 v1 in
      (a0 * a1 + b0 * b1 + c0 * c1)%A.
  
End VectorThy.


(* ######################################################################### *)
(** * Vector on R *)
Module VectorR := VectorThy (FieldR).


(* ######################################################################### *)
(** * Test of VectorR *)
Module VectorR_test.

  Import VectorR.
  Open Scope R.
  Open Scope mat_scope.
  
  Definition v1 : vec 3 := l2v [1;2;3].
  Definition v2 : vec 3 := l2v [4;5;6].
  Example vdot_ex1 : vdot v1 v2 = (4+10+18)%R.
  Proof. compute. ring. Qed.
  
End VectorR_test.

