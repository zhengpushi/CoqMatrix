(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector Theory based on Matrix of Function
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. This is version 2, fixed the shape problem
*)


Require Export Matrix.


(* ==================================== *)
(** ** Definition of Vector type *)
Section Def.

  Context {A:Type}.

  (** 为便于 vector 和 matrix 同时操作，将 vector 就定义为 matrix 类型，
      需要注意的是：
      1. 访问 vector 的元素时，不要用 v i 0 这样的双下标方式，
         而是使用 vnth v i 这样的方式。
   *)
  Definition vec n := @mat A n 1.

  (** vector to function *)
  Definition v2f {n} (v : vec n) : nat -> A :=
    fun i => m2f v i 0.

  (** function to vector *)
  Definition f2v n (f : nat -> A) : vec n :=
    f2m (fun i _ => f i).
  
  (** Get element from a vector *)
  Definition vnth {n} (v : vec n) (i:nat) : A := (v2f v) i.
  
End Def.

Notation "v # i" := (vnth v i) : vec_scope.

(* ==================================== *)
(** ** Equility of vectors *)
Section veq.

  Context `{ER:EqReflect}.

  Definition veq {n} (v1 v2 : @vec A n) := meq v1 v2.
  Infix "==" := veq.
  
  Lemma veq_refl : forall {n} (v : @vec A n), v == v.
  Proof. intros. apply meq_refl. Qed.
   
  Lemma veq_sym : forall {n} (v1 v2 : @vec A n), v1 == v2 -> v2 == v1.
  Proof. intros. apply meq_sym. easy. Qed.
  
  Lemma veq_trans : forall {n} (v1 v2 v3 : @vec A n), 
    v1 == v2 -> v2 == v3 -> v1 == v3.
  Proof. intros. apply meq_trans with (m2:=v2); auto. Qed.
  
  Lemma veq_dec : forall {n} (v1 v2 : @vec A n), {v1 == v2} + {~(v1 == v2)}.
  Proof. intros. apply meq_dec. Qed.

End veq.

Global Infix "==" := veq : vec_scope.


(* ==================================== *)
(** ** Convert between tuples and vector *)
Section t2v_v2t.

  Context {A:Type}.
  Context {A0:A}.

  (** 单态化通用的函数，以简化书写 *)
  Notation l2m := (l2m (A0:=A0)).
  
  Definition t2v_2 (t : @T2 A) : @vec A 2 := 
    let '(a,b) := t in l2m [[a];[b]].
    
  Definition t2v_3 (t : @T3 A) : @vec A 3 := 
    let '(a,b,c) := t in l2m [[a];[b];[c]].
    
  Definition t2v_4 (t : @T4 A) : @vec A 4 := 
    let '(a,b,c,d) := t in l2m [[a];[b];[c];[d]].

  Definition v2t_2 (v : @vec A 2) : @T2 A :=
    (v#0, v#1).

  Definition v2t_3 (v : @vec A 3) : @T3 A :=
    (v#0, v#1, v#2).
    
  Definition v2t_4 (v : @vec A 4) : @T4 A :=
    (v#0, v#1, v#2, v#3).
  
  Lemma v2t_t2v_id_2 : forall (t : A * A), v2t_2 (t2v_2 t) = t.
  Proof.
    intros. destruct t. simpl. unfold v2t_2. simpl. f_equal.
  Qed.
  
  Lemma t2v_v2t_id_2 : forall (v : @vec A 2), t2v_2 (v2t_2 v) == v.
  Proof.
    intros. apply meq_iff; intros i j Hi Hj. simpl.
    repeat (try destruct i; try destruct j; auto; try lia).
  Qed.

End t2v_v2t.
  
(* ==================================== *)
(** ** Convert between list and vector *)
Section v2l_l2v.

  Context {A:Type}.
  Context {A0:A}.
  
  Definition v2l {n} (v : @vec A n) : list A := mcol 0 v (r:=n) (c:=1).
  Definition l2v {n} (l : list A) : @vec A n := l2m (row2col l) (A0:=A0).
  
  Lemma v2l_length : forall {n} (v : @vec A n), length (v2l v) = n.
  Proof. intros. unfold v2l. apply mcol_length. Qed.
  
  Lemma v2l_l2v_id : forall {n} (l : list A),
      length l = n -> @v2l n (@l2v n l) = l.
  Proof.
    intros. unfold v2l,l2v,l2m,mcol. simpl.
    (* 列表相等，转换为 nth 相等 *)
    rewrite list_eq_iff_nth with (A0:=A0) (n:=n); auto.
    - intros.
      (* nth_map_seq 可以化简 *)
      rewrite nth_map_seq; auto.
      (* nth_row2col 可以化简 *)
      rewrite nth_row2col with (A0:=A0); try lia.
      simpl. f_equal. auto.
    - rewrite map_length. rewrite seq_length. auto. 
  Qed.

  Lemma l2v_v2l_id : forall {n} (v : @vec A n), 
      l2v (v2l v) == v.
  Proof.
    intros. unfold v2l,l2v,l2m,f2m,mcol.
    unfold veq,vec in *. meq_simp.
    intros.
    (* 尽量不要直接归纳，而是用不变式来化简函数作用 *)
    rewrite nth_row2col with (A0:=A0).
    - rewrite nth_map_seq; auto.
      simpl. destruct j; auto. lia.
    - rewrite map_length. rewrite seq_length. auto. 
  Qed.

End v2l_l2v.


(* ==================================== *)
(** ** Zero vector *)
Section vec0.

  Context {A:Type}.
  Context {A0:A}.
  Context `{ER:EqReflect (A:=A)}.

  Notation mat0 := (mat0 (A0:=A0)).
  
  Definition vec0 {n} : @vec A n := mat0 n 1.

  (** Assert that a vector is an zero vector. *)
  Definition vzero {n} (v : @vec A n) : Prop := v == vec0.

  (** Assert that a vector is an non-zero vector. *)
  Definition vnonzero {n} (v : @vec A n) : Prop := ~(vzero v).
  
  (** vec0 is equal to mat0 with column 1 *)
  Lemma vec0_eq_mat0 : forall n, vec0 == mat0 n 1.
  Proof. intros. easy. Qed.

  (** It is decidable that if a vector is zero vector. *)
  Lemma vzero_dec : forall {n} (v : @vec A n), {vzero v} + {vnonzero v}.
  Proof. intros. apply meq_dec. Qed.

End vec0.
  
(* ==================================== *)
(** ** algebra operations *)

Section vector_algebra.

  Context `{R:Ring}.
  Declare Scope A_scope.
  Delimit Scope A_scope with A.
  Open Scope A_scope.
  Infix "+" := add0 : A_scope.
  Infix "*" := mul0 : A_scope.
  Notation "0" := zero0 : A_scope.
  Notation "1" := one0 : A_scope.
  Notation "- x" := (opp x) : A_scope.
  Notation "a - b" := (a + (-b)) : A_scope.

  (** 注册 Ring 结构，使能 ring 策略 *)
  Add Ring ring_inst : make_ring_theory.

  Notation vec0 := (vec0 (A0:=0)).
  Notation mmul r c s := (mmul (add0:=add0) (zero0:=zero0) (mul0:=mul0)
                            (r:=r) (c:=c) (s:=s)).
  Notation madd r c := (madd (op:=add0) (r:=r) (c:=c)).
  (* Notation mopp r c := (mopp (inv:=opp) (r:=r) (c:=c)). *)
  Notation mopp := (mopp (inv:=opp)).

  (** 一个向量的映射 *)
  Definition vmap {n} (v : @vec A n) f : @vec A n := mmap f v.
  
  (** 一个向量的fold操作 *)
  (*   Definition vfold : forall {B : Type} {n} (v : @vec A n)
       (f : A -> B) (b : B), B. *)
  
  (** 两个向量的映射 *)
  Definition vmap2 {n} (v1 v2 : @vec A n) f : @vec A n := mmap2 f v1 v2.
  
  (* 两个向量的点积。这里用矩阵乘法来定义点积，而我们之前是用点积来定义乘法 *)
  Definition vdot {n : nat} (m1 m2 : @vec A n) : A :=
    m2t_1x1 (mmul 1 n 1 (mtrans m1) m2).

  (** 向量的长度，模，范数（欧几里得范数）的平方。方便计算。*)
  Definition vlen_sqr {n} (v : vec n) : A := vdot (n:=n) v v.

  (* (** 2维向量的“长度”，这里不是欧式距离，而是欧式距离的平方，为了方便计算 *) *)
  (* Definition vlen2_sqr (v : @vec A 2) : A := *)
  (*   let '(x,y) := v2t_2 v in *)
  (*     (x * x + y * y)%A. *)

  (* (** 3维向量的“长度”，这里不是欧式距离，而是欧式距离的平方，为了方便计算 *) *)
  (* Definition vlen3_sqr (v : @vec A 3) : A := *)
  (*   let '(x,y,z) := v2t_3 v in *)
  (*     (x * x + y * y + z * z)%A. *)
      
  (* (** V3的点积 *) *)
  (* Definition vdot3 (v0 v1 : @vec A 3) : A := *)
  (*   let '(a0,b0,c0) := v2t_3 v0 in *)
  (*   let '(a1,b1,c1) := v2t_3 v1 in *)
  (*     (a0 * a1 + b0 * b1 + c0 * c1)%A. *)

  
  (** 向量加法 *)
  Definition vadd {n} (v1 v2 : @vec A n) : @vec A n := madd n 1 v1 v2.
  Infix "+" := vadd.

  (** 向量加法交换律 *)
  Lemma vadd_comm : forall {n} (v1 v2 : @vec A n), v1 + v2 == v2 + v1.
  Proof. intros. apply (madd_comm (c:=1)). Qed.

  (** 向量加法结合律 *)
  Lemma vadd_assoc : forall {n} (v1 v2 v3 : @vec A n), 
    (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof. intros. apply (madd_assoc (c:=1)). Qed.

  (** 向量左加0 *)
  Lemma vadd_0_l : forall {n} (v : @vec A n), vec0 + v == v.
  Proof. intros. apply (madd_0_l (c:=1)). Qed.

  (** 向量右加0 *)
  Lemma vadd_0_r : forall {n} (v : @vec A n), v + vec0 == v.
  Proof. intros. apply (madd_0_r (c:=1)). Qed.

  (** 负向量 *)
  Definition vopp {n} (v : @vec A n) : @vec A n := mopp v.
  Notation "- v" := (vopp v).

  (** 加上负向量等于0 *)
  Lemma vadd_opp : forall {n} (v : @vec A n), v + (- v) == vec0.
  Proof. intros. unfold vadd, vopp. apply (madd_opp). Qed.

  (** 向量减法 *)
  Definition vsub {n} (v1 v2 : @vec A n) : @vec A n := v1 + (- v2).
  Infix "-" := vsub.

  (** 向量数乘 *)
  Definition vcmul {n} a (v : @vec A n) : @vec A n :=
    (* a c* v. *)
    mcmul a v (mul0:=mul0).
  Infix "c*" := vcmul.
  
  Definition vmulc {n} (v : @vec A n) a : @vec A n :=
    (* v *c a. *)
    mmulc v a (mul0:=mul0).
  Infix "*c" := vmulc.

  (** 右数乘和左数乘等价 *)
  Lemma vmulc_eq_vcmul : forall {n} a (v : @vec A n), 
    (v *c a) == (a c* v).
  Proof. intros. apply (mmulc_eq_mcmul (c:=1)). Qed.

  (** 数乘结合律1 *)
  Lemma vcmul_assoc : forall {n} a b (v : @vec A n), 
    (a * b) c* v == a c* (b c* v).
  Proof. intros. apply meq_sym. apply (mcmul_assoc (c:=1)). Qed.

  (** 数乘结合律2 *)
  Lemma vcmul_perm : forall {n} a b (v : @vec A n), 
    a c* (b c* v) == b c* (a c* v).
  Proof. intros. apply (mcmul_perm (c:=1)). Qed.

  (** 数乘左分配律 *)
  Lemma vcmul_add_distr_l : forall {n} a (v1 v2 : @vec A n), 
    a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply (mcmul_add_distr_l (c:=1)). Qed.

  (** 数乘右分配律 *)
  Lemma vcmul_add_distr_r : forall {n} a b (v : @vec A n), 
    (a + b)%A c* v == (a c* v) + (b c* v).
  Proof. intros. apply (mcmul_add_distr_r (c:=1)). Qed.

  (** 用1数乘 *)
  Lemma vcmul_1_l : forall {n} (v : @vec A n), 1 c* v == v.
  Proof. intros. apply (mcmul_1_l (c:=1)). Qed.

  (** 用0数乘 *)
  Lemma vcmul_0_l : forall {n} (v : @vec A n), 0 c* v == vec0.
  Proof. intros. apply (mcmul_0_l (c:=1)). Qed.

  (** 非零向量是k倍关系，则系数k不为0 *)
  Lemma vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : @vec A n) k,
    vnonzero v1 (A0:=0) -> vnonzero v2 (A0:=0) -> v1 == k c* v2 -> k <> 0.
  Proof.
    intros. intro. subst. rewrite vcmul_0_l in H1. destruct H. easy.
  Qed.
  
End vector_algebra.

Global Infix "+" := vadd : vec_scope.
Global Notation "- v" := (vopp v) : vec_scope.
Global Infix "-" := vsub : vec_scope.
Global Infix "c*" := vcmul : vec_scope.
Global Infix "*c" := vmulc : vec_scope.


(* ==================================== *)
(** ** Test of VectorR *)
Module test_VectorR.
  
  (* Import FieldR. *)
  (* Import VectorR. *)
  Open Scope R.
  Open Scope mat_scope.

  Notation l2v := (l2v (A0:=0)).
  Notation vdot := (vdot (add0:=Rplus) (zero0:=0) (mul0:=Rmult)).
  
  Definition v1 : vec 3 := l2v [1;2;3].
  Definition v2 : vec 3 := l2v [4;5;6].

  Goal vdot v1 v2 = (4+10+18)%R. cbv. ring. Qed.
  
End test_VectorR.


(* ==================================== *)
(** ** Test of VectorQ *)
Module test_VectorQ.
  
  Open Scope Q.
  Open Scope mat_scope.

  Notation l2v := (l2v (A0:=0)).
  Notation vdot := (vdot (add0:=Qplus) (zero0:=0) (mul0:=Qmult)).

  Definition v1 : vec 3 := l2v [1.5; 2; 3].
  Definition v2 : vec 3 := l2v [4; 5; 6].

  Goal (vdot v1 v2 == (6+10+18))%Q. cbn. cbv. auto. Qed.
  Goal v2l v1 = [1.5; 2; 3]. cbv. auto. Qed.
  
End test_VectorQ.


(* ==================================== *)
(** ** Test of VectorQc *)
Module test_VectorQc.
  
  Open Scope Q. (* 可以输入 1.5 之类的小数 *)
  Open Scope Qc. (* 使用 Qc 中的运算符号 *)
  Open Scope mat_scope.

  Notation l2v := (l2v (A0:=0)).
  Notation vdot := (vdot (add0:=Qcplus) (zero0:=0) (mul0:=Qcmult)).

  (* 开启自动类型转换 *)
  Coercion Q2Qc : Q >-> Qc.

  (* 简单的表达式是可以 *)
  Definition ex1 : Qc := 1.5.

  (* 在列表中就不能用了，需要额外的处理 *)
  Fail Definition ex2 : list Qc := [1.5; 2.3].

  (* 可以手动一个个转换 *)
  Definition ex2 : list Qc := [Q2Qc 1.5; Q2Qc 2.3].

  (* 也可以用map *)
  Definition ex3 : list Qc := map Q2Qc [1.5; 2.3].

  (* 试试能否写一个list之间的处理函数，让Coercion自动调用？*)
  Definition list_Q2Qc (l : list Q) : list Qc := map Q2Qc l.

  (* 看起来不支持这种复合类型 *) 
  (* Coercion list_Q2Qc : (list Q) >-> (list Qc). *)

  (** 再尝试一下，把 list Q 和 list Qc 命名为新的类型，则又能通过了，
      但仍需要对输入做显式的类型标注，例如 [1.5; 2.3] : listQ *)
  Definition listQ : Type := list Q.
  Definition listQc : Type := list Qc.
  Definition list_Q2Qc' (l : listQ) : listQc := map Q2Qc l.
  Coercion list_Q2Qc' : listQ >-> listQc.
  Definition ex4 : listQc := ([1.5; 2.3] : listQ).
  
  Definition v1 : vec 3 := l2v (map Q2Qc [1.5; 2; 3]).
  Definition v2 : vec 3 := l2v (map Q2Qc [4; 5; 6]).

  (** Qc 的好处是，自动计算有理式范式，因此可以使用等号，而不是等价 *)
  Goal vdot v1 v2 = (6+10+18)%Qc. cbv. auto. Qed.

  Goal v2l v1 = map Q2Qc [1.5; 2; 3]. cbv. auto. Qed.
  
End test_VectorQc.

