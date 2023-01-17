(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Function (version 2) (Fixed Shape)
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. This is version 2, fixed the shape problem
*)

Require Export Hierarchy.
Require Export Sequence.
Require Export TuplesExt NatExt ListListExt.
Require Export Arith Lia Lra.
(* Require Import Setoid. (* R => R', Morphisms.respectful R R' *) *)


(** ** Definition of matrix *)
Section Def.

  (* 矩阵被定义为从自然数下标到值的映射，这里用了两个影子参数 r c 表示
     矩阵维度 *)
  Definition mat {A:Type} (r c : nat) := nat -> nat -> A.
  (*     Bind Scope mat_scope with mat. *)

  Definition mat_rows {A r c} (m : @mat A r c) := r.
  Definition mat_cols {A r c} (m : @mat A r c) := c.

  (**  带有维度参数的强类型版本 *)
  Inductive matT {A:Type} (r c : nat) := mk_matT (f: nat -> nat -> A).

  (** 取出矩阵的函数 *)
  Definition m2f {A r c} (m : @matT A r c) : nat -> nat -> A :=
    let '(mk_matT _ _ f) := m in f.

End Def.

  
(** ** Equality of matrix *)
Section meq.

  Context {A:Type}.

  (* 矩阵相等定义为：下标有效时对应元素相等 *)
  Definition meq {r c : nat} (m1 m2 : @mat A r c) : Prop :=
    forall i j, i < r -> j < c -> m1 i j = m2 i j.
 
  Infix "==" := meq.
    
  (** 容易证明，这是等价关系 *)
  Lemma meq_refl : forall {r c} (m : mat r c), m == m.
  Proof.
    unfold meq; intros; auto.
  Qed.
  
  Lemma meq_sym : forall {r c} (m1 m2 : mat r c), m1 == m2 -> m2 == m1.
  Proof.
    unfold meq; intros; auto. rewrite H; auto.
  Qed.
  
  Lemma meq_trans : forall {r c} (m1 m2 m3 : mat r c),
      m1 == m2 -> m2 == m3 -> m1 == m3.
  Proof.
    unfold meq; intros; auto. rewrite H,H0;auto.
  Qed.

  (** Register meq equivalence relation to Coq to enable rewring support. *)
  Global
    Add Parametric Relation (r c : nat) : (@mat A r c) meq
       reflexivity proved by meq_refl
       symmetry proved by meq_sym
       transitivity proved by meq_trans
       as meq_rel.

  (** 两矩阵等价，iff，对应元素相等。相当于加强了meq的另一个方向 *)  
  Lemma meq_iff : forall {r c} (m1 m2 : @mat A r c),
      m1 == m2 <-> forall i j, i < r -> j < c -> m1 i j = m2 i j.
  Proof.
    intros. split; intros.
    - rewrite H; auto.
    - auto.
  Qed.

  (** meq_dec 需要是 EqReflect 类 *)
  Context {Aeqb:A->A->bool}.
  Context `{ER:@EqReflect A Aeqb}.

  (** Meq is decidable *)
  Lemma meq_dec : forall {r c} (m1 m2 : mat r c),
      {m1 == m2} + {~(m1 == m2)}.
  Proof. apply seq2eq_dec. Qed.
  
End meq.

(** 在 Section 外面还要再写一次符号 *)
Infix "==" := meq : mat_scope.

(** 测试 meq 的重写 *)
Goal forall A r c (m1 m2 m3 : @mat A r c), m1 == m2 -> m2 == m3 -> m1 == m3.
  intros. rewrite H,H0. reflexivity. Qed.


(* ==================================== *)
(** ** Get element *)
Section mnth.

  Context {A:Type}.
  
  Definition mnth {r c} (m : mat r c) (ri ci : nat) : A := m ri ci.
  
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> 
        (forall ri ci, ri < r -> ci < c -> mnth m1 ri ci = mnth m2 ri ci).
  Proof. unfold meq; intros; split; intros; auto. Qed.
  
End mnth.


(* ==================================== *)
(** ** Get a row on a matrix *)
Section mrow.

  Context {A:Type}.

  (** 取出矩阵一行 *)
  Definition mrow {r c : nat} (ri : nat) (m : mat r c) : list A :=
    map (fun j => m ri j) (seq 0 c).

  (** 取出矩阵一行，具有期望的长度 *)
  Lemma mrow_length : forall {r c} ri (m : mat r c), length (mrow ri m) = c.
  Proof. intros. unfold mrow. rewrite map_length. apply seq_length. Qed.
  
  (** 不越界时取出有效的数据 *) 
  (** (mrow m i)[j] = m[i][j] *)
  Lemma mrow_nth : forall {r c} ri ci (m : mat r c) a,
      ri < r -> ci < c ->
      nth ci (mrow ri m) a = m ri ci.
  Proof. intros. unfold mrow. rewrite nth_map_seq; auto. Qed.

End mrow.


(* ==================================== *)
(** ** Get a column of a matrix *)
Section mcol.

  Context {A:Type}.

  (** 取出矩阵一列 *)
  Definition mcol {r c : nat} (ci : nat) (m : mat r c) : list A :=
    map (fun i => m i ci) (seq 0 r).

  (** 取出矩阵一列，具有期望的长度 *)
  Lemma mcol_length : forall {r c} ci (m : mat r c), length (mcol ci m) = r.
  Proof. intros. unfold mcol. rewrite map_length. apply seq_length. Qed.
  
  (** 不越界时取出有效的数据 *) 
  (** (mcol m j)[i] = m[i][j] *)
  Lemma mcol_nth : forall {r c} ri ci (m : mat r c) a,
      ri < r -> ci < c ->
      nth ri (mcol ci m) a = m ri ci.
  Proof. intros. unfold mcol. rewrite nth_map_seq; auto. Qed.

End mcol.


(* ==================================== *)
(** ** Convert between list of lists and matrix *)
Section l2m_m2l.

  Context {A:Type}.
  Context {A0:A}.
  
  (** Convert list of lists to matrix
      指定了行数和列数，不足补充自动填充为0，多余的数据会丢弃 *)
  Definition l2m {r c} (dl : list (list A)) : mat r c := 
    fun x y => nth y (nth x dl []) A0.
  
  (** Convert list of lists to matrix (auto calculate shape)
      矩阵行数等于输入列表的长度，
      矩阵列数等于输入列表的子列表中第一个列表的长度，
      该版本不常用 *)
  Definition l2m_autoshape (dl : list (list A))
    : mat (length dl) (length (hd [] dl)) :=
    fun x y => nth y (nth x dl []) A0.

  (** Convert matrix to list of lists *)
  Definition m2l {r c} (m : mat r c) : list (list A) :=
    map (fun ri => (map (fun ci => m ri ci) (seq 0 c))) (seq 0 r).

  (** Convert matrix to list of lists (transposed) *)
  Definition m2l_transposed {r c} (m : mat r c) : list (list A) :=
    map (fun ci => (map (fun ri => m ri ci) (seq 0 r))) (seq 0 c).

  (** 矩阵转列表 行数不变 *)
  Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
  Proof. intros. unfold m2l. rewrite map_length,seq_length;auto. Qed.

  (** 矩阵转列表 列数不变 *)
  Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
  Proof.
    intros. unfold m2l.
    apply width_map. intros. rewrite map_length,seq_length;auto.
  Qed.

  Lemma l2m_m2l_id : forall {r c} (m : mat r c),
      l2m (m2l m) == m. 
  Proof.
    unfold l2m,m2l,meq.
    intros.
    rewrite nth_map_seq; auto.
    rewrite nth_map_seq; auto.
  Qed.
          
  Lemma m2l_l2m_id : forall {r c} (dl : list (list A)),
      (length dl = r) -> (width dl c) -> m2l (@l2m r c dl) = dl.
  Proof.
    unfold m2l,l2m.
    induction r.
    - intros. apply length_zero_iff_nil in H. subst. simpl. auto.
    - intros. destruct dl.
      + simpl in *. lia.
      + simpl. destruct H0. inversion H.
        f_equal.
        * apply map_nth_seq. auto.
        * rewrite <- seq_shift. rewrite map_map.
          rewrite <- IHr with (c:=c); auto. f_equal. f_equal. auto.
  Qed.

  (** 注意，以下证明中需要 A 是可判定的 *)
  Context {AEqDec:@EqDec A}.
  
  Lemma l2m_inj : forall {r c} (d1 d2 : list (list A)),
      length d1 = r -> width d1 c -> 
      length d2 = r -> width d2 c -> 
      d1 <> d2 -> @l2m r c d1 <> l2m d2.
  Proof.
    unfold l2m. intros. intro.
    (* 将函数相等转换为全称相等 *)
    rewrite (@fun_eq_iff_forall_eq2 nat nat A) in H4.
    destruct H3.
    (* 利用 dlist 已证性质 *)
    apply (@dlist_eq_iff_nth_nth _ A0 r c d1 d2 H H1 H0 H2). auto.
  Qed.
  
  Lemma l2m_surj : forall {r c} (m : mat r c), 
      (exists d, l2m d == m).
  Proof. Admitted.
  
  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c),
      ~(m1 == m2) -> m2l m1 <> m2l m2.
  Proof. Admitted.
  
  Lemma m2l_surj : forall {r c} (d : list (list A)), 
      length d = r -> width d c -> 
      (exists m, @m2l r c m = d).
  Proof. Admitted.

  
End l2m_m2l.

Section test.

  (* (* 先构造一个矩阵 *) *)
  (* Let dl1 := [[1;2;3];[4;5;6];[7;8;9]]. *)
  (* Let m1 := @l2m _ 0 3 3 dl1. *)

  (* Compute m2l (@l2m _ 0 0 3 dl1). *)

  (* (* 矩阵转列表 *) *)
  (* Compute m2l m1. *)

  (* (* 手动取出一些元素 *) *)
  (* Compute (m1 0 0, m1 0 1, m1 0 2, m1 0 3). *)

  (* (* 取出第1行 *) *)
  (* Compute map (fun i => m1 0 i) (seq 0 4). *)
  
  (* (* 取出所有元素 *) *)
  (* Compute (map (fun i => (map (fun j => m1 i j) (seq 0 4))) (seq 0 4)). *)
  
End test.

Global Hint Resolve m2l_length : mat.
Global Hint Resolve m2l_width : mat.


(* ==================================== *)
(** ** Right shift columns *)
Section mshift.

  Context {A:Type}.
  Context {A0 A1:A}.
  Context {A1_neq_A0 : A1 <> A0}.
  
  (** Right shift columns *)
  Definition mshiftc {r c} (m : @mat A r c) (k : nat) : mat r c :=
    fun i j => m i (j + k).
  
  (** ∃ A A' k (X = A' /\ mshiftc A k <> mshiftc A' k *)
  Lemma mshiftc_neq : exists r c (m1 m2 : mat r c) (k : nat),
      m1 == m2 /\ ~(mshiftc m1 k == mshiftc m2 k).
  Proof.
    set (m1 := fun (i j:nat) => if (j <? 2) then A1 else A0).
    set (m2 := fun (i j:nat) => if (j <? 3) then A1 else A0).
    exists 2, 2, m1, m2, (1). split.
    - apply meq_iff. intros.
      (* unfold m1, m2. intros i j Hi Hj. simpl. *)
      destruct j as [|[|]]; destruct i as [|[|]]; trivial; lia.
    - intros F.
      assert (1 < 2) by lia.
      apply meq_iff in F. (* ToDo: 为何没有效果？ *)
      rewrite meq_iff in F.
      specialize (F _ _ H H).
      unfold m1, m2, mshiftc in F.
      simpl in F.
      apply A1_neq_A0; auto.
  Qed.
  
End mshift.


(* ==================================== *)
(** ** Matrix Automation *)

(** Useful tactic for solving A = B for concrete A, B *)

Ltac solve_end :=
  match goal with
  | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.

(** 由于 Coq 8.16 开始，提示“lt_S_n 弃用，文件 Arith.Lt 过时，
    请改用 Nat.succ_lt_mono_left 这个双向版本并不能完全代替单向的情形，
    这里需要严格的出现 S ?a < S ?b 时才使用该引理。
    因此，用 Arith_prebase.lt_S_n 来代替 *)
Ltac by_cell := 
  intros;
  let i := fresh "i" in 
  let j := fresh "j" in 
  let Hi := fresh "Hi" in 
  let Hj := fresh "Hj" in 
  intros i j Hi Hj; try solve_end;
  repeat (destruct i as [|i]; simpl; 
          [|apply Arith_prebase.lt_S_n in Hi]; try solve_end); clear Hi;
  repeat (destruct j as [|j]; simpl; 
          [|apply Arith_prebase.lt_S_n in Hj]; try solve_end); clear Hj.

Ltac lma := by_cell; compute; try ring; auto.


(* ==================================== *)
(** ** 指定维数的矩阵的创建函数 *)
Section SpecifyDims.

  Context {A:Type}.
  Context {A0:A}.
  
  Definition mk_mat_0_c c : @mat A 0 c.
  Proof. exact (l2m [] (A0:=A0)). Defined.

  Definition mk_mat_1_1 (a11 : A) : @mat A 1 1.
  Proof. exact (l2m [[a11]] (A0:=A0)). Defined.
  
  Definition mk_mat_1_2 (a11 a12 : A) : @mat A 1 2.
  Proof. exact (l2m [[a11;a12]] (A0:=A0)). Defined.
  
  Definition mk_mat_1_3 (a11 a12 a13 : A) : @mat A 1 3.
  Proof. exact (l2m [[a11;a12;a13]] (A0:=A0)). Defined.
  
  Definition mk_mat_1_4 (a11 a12 a13 a14 : A) : @mat A 1 4.
  Proof. exact (l2m [[a11;a12;a13;a14]] (A0:=A0)). Defined.
  
  Definition mk_mat_1_c c (l : list A) : @mat A 1 c.
  Proof. exact (l2m [l] (A0:=A0)). Defined.
  
  Definition mk_mat_r_0 r : @mat A r 0.
  Proof. exact (l2m [] (A0:=A0)). Defined.
  
  Definition mk_mat_2_1 (a11 a21 : A) : @mat A 2 1.
  Proof. exact (l2m [[a11];[a21]] (A0:=A0)). Defined.
  
  Definition mk_mat_2_2 (a11 a12 a21 a22 : A) : @mat A 2 2.
  Proof. exact (l2m [[a11;a12];[a21;a22]] (A0:=A0)). Defined.
  
  Definition mk_mat_3_1 (a11 a21 a31 : A) : @mat A 3 1.
  Proof. exact (l2m [[a11];[a21];[a31]] (A0:=A0)). Defined.
  
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A) : @mat A 3 3.
  Proof. exact (l2m [[a11;a12;a13]; [a21;a22;a23]; [a31;a32;a33]] (A0:=A0)).
  Defined.
  
  Definition mk_mat_4_1 (a11 a21 a31 a41 : A) : @mat A 4 1.
  Proof. exact (l2m [[a11];[a21];[a31];[a41]] (A0:=A0)). Defined.
  
  Definition mk_mat_4_4 (a11 a12 a13 a14 a21 a22 a23 a24 
                           a31 a32 a33 a34 a41 a42 a43 a44 : A) : @mat A 4 4.
  Proof. exact (l2m [[a11;a12;a13;a14]; [a21;a22;a23;a24]; 
                      [a31;a32;a33;a34]; [a41;a42;a43;a44]] (A0:=A0)). Defined.
  
  Definition mk_mat_r_1 r (l : list A) : @mat A r 1.
  Proof. exact (fun ri ci : nat => if (ci =? 0) then (nth ri l A0) else A0).
  Defined.
  
End SpecifyDims.

Section test.
  (* Compute mk_mat_2_1 1 2. *)
  (* Compute (m2l (mk_mat_2_1 1 2)). *)
  (* Compute (m2l (mk_mat_r_1 5 [1;2;3])). *)
End test.


(* ==================================== *)
(** ** 矩阵映射 *)
Section Map.

  Context {A:Type}.
  
  Definition mmap {r c} (f : A -> A) (m : mat r c) : mat r c :=
    fun i j => f (m i j).

  Definition mmap2 {r c} (f : A -> A -> A) (m1 m2 : mat r c) : mat r c :=
    fun i j => f (m1 i j) (m2 i j).
  
  Lemma mmap2_comm : forall {r c} (f : A -> A -> A)
                       (f_comm : forall a b : A, f a b = f b a) (m1 m2 : mat r c), 
      mmap2 f m1 m2 == mmap2 f m2 m1.
  Proof.
    intros. apply meq_iff. intros. cbv. auto.
  Qed.
  
  Lemma mmap2_assoc : forall {r c} (f : A -> A -> A)
                        (f_assoc : forall a b c, f a (f b c) = f (f a b) c)
                        (m1 m2 m3 : mat r c), 
      mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
  Proof.
    intros. apply meq_iff. intros. cbv. auto.
  Qed.
  
End Map.


(* ==================================== *)
(** ** 零矩阵和单位矩阵 *)
Section Mat1_Mat0.

  Context {A:Type}.
  Context {A0 A1 : A}.
  
  (* Zero M *)
  Definition mat0 (r c : nat) : mat r c := fun _ _ => A0.
  
  (* Identity M *)
  Definition mat1 (n : nat) : mat n n := fun i j => if (i =? j) then A1 else A0.
  
End Mat1_Mat0.


(* ==================================== *)
(** ** 矩阵加法 *)
Section madd.

  Context `{AM:AMonoid}.

  Declare Scope A_scope.
  Delimit Scope A_scope with A.
  Open Scope A_scope.
  Infix "+" := op : A_scope.
  Notation "0" := e : A_scope.

  Definition madd {r c} (m1 m2 : mat r c) : mat r c :=
    fun i j => m1 i j + m2 i j.

  Infix "+" := madd.
  
  Lemma madd_comm : forall {r c} (m1 m2 : mat r c), m1 + m2 == (m2 + m1).
  Proof. lma. apply commutative. Qed.
  
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : mat r c), 
      (m1 + m2) + m3 == m1 + (m2 + m3).
  Proof. lma. rewrite associative;auto. Qed.
  
  Lemma madd_0_l : forall {r c} (m : mat r c), @mat0 A 0 r c + m == m. 
  Proof. lma. apply identityLeft. Qed.
  
  Lemma madd_0_r : forall {r c} (m : mat r c), m + @mat0 A 0 r c == m. 
  Proof. lma. apply identityRight. Qed.
  
  (** Get element of addition with two matrics equal to additon of 
      corresponded elements. *)
  Lemma madd_nth : forall {r c} (m1 m2 : mat r c) ri ci,
      mnth (m1 + m2) ri ci = ((mnth m1 ri ci) + (mnth m2 ri ci))%A.
  Proof. intros. auto. Qed.
  
  (** 加法与 mrow 的关系 *)
  
  (* (m1 + m2)[0] = m1[0] + m2[0] *)
  Lemma mrow_aux_prop1 : forall {r c} (m1 m2 : mat r c) ri,
      ri < r ->
      mrow ri (m1 + m2) = 
        map2 op (mrow ri m1) (mrow ri m2).
  Proof.
    intros. unfold mrow.
    rewrite map2_map_map with (g:=(fun j => (m1 + m2) ri j)); auto.
  Qed.

End madd.

Global Infix "+" := madd : mat_scope.


(* ==================================== *)
(** ** Matrix subtraction *)
Section msub.

  Context `{G:AGroup}.

  Declare Scope A_scope.
  Delimit Scope A_scope with A.
  Open Scope A_scope.
  Infix "+" := op : A_scope.
  Notation "0" := e : A_scope.
  Notation "- x" := (inv x) : A_scope.
  Notation "a - b" := (a + (-b)) : A_scope.

  Definition mopp {r c} (m : mat r c) : mat r c :=
    fun i j => - (m i j).

  Definition msub {r c} (m1 m2 : mat r c) : mat r c := 
    fun i j => m1 i j - m2 i j.

  Notation "- a" := (mopp a) : mat_scope.
  Infix "-" := msub : mat_scope.
  Notation "m1 + m2" := (madd m1 m2 (op:=op)) : mat_scope.
  Open Scope mat_scope.
  
  Lemma mopp_opp : forall {r c} (m : mat r c), - (- m) == m.
  Proof. lma. apply group_inv_inv. Qed.
  
  Lemma msub_comm : forall {r c} (m1 m2 : mat r c), m1 - m2 == - (m2 - m1).
  Proof. lma. rewrite group_inv_distr. f_equal. rewrite group_inv_inv. auto.
  Qed.
  
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c),
      (m1 - m2) - m3 == m1 - (m2 + m3).
  Proof.
    lma.
    rewrite <- associative. f_equal.
    rewrite group_inv_distr. rewrite commutative. auto.
  Qed.
  
  Lemma msub_0_l : forall {r c} (m : mat r c), (@mat0 _ 0 r c) - m == - m.
  Proof. lma. apply identityLeft. Qed.
  
  Lemma msub_0_r : forall {r c} (m : mat r c), m - (@mat0 _ 0 r c) == m.
  Proof.
    lma.
    rewrite (@group_inv_id A op 0 inv agroupGroup). apply identityRight.
  Qed.
  
  Lemma madd_opp : forall r c (m : mat r c), m + (-m) == @mat0 _ 0 r c.
  Proof. lma. apply inverseRight. Qed.
  
  Lemma msub_self : forall {r c} (m : mat r c), m - m == (@mat0 _ 0 r c).
  Proof. lma. apply inverseRight. Qed.

End msub.

Global Notation "- a" := (mopp a) : mat_scope.
Global Infix "-" := msub : mat_scope.



(* ==================================== *)
(** ** Constant multiplication of matrix *)
Section mcmul.

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

  Definition mcmul {r c} (a : A) (m : mat r c) : mat r c :=
    fun i j => (a * m i j).
  
  Definition mmulc {r c} (m : mat r c) (a : A) : mat r c :=
    fun i j => (m i j * a).

  Notation "m1 + m2" := (madd m1 m2 (op:=add0)) : mat_scope.
  Infix "c*" := mcmul : mat_scope.
  Infix "*c" := mmulc : mat_scope.
  Open Scope mat_scope.

  Lemma mmulc_eq_mcmul : forall {r c} (a : A) (m : mat r c), 
      m *c a == a c* m.
  Proof. lma. Qed.
  
  Lemma mcmul_0_l : forall {r c} (m : mat r c), 0 c* m == @mat0 _ 0 r c.
  Proof. lma. Qed.
  
  Lemma mcmul_0_r : forall {r c} a, a c* @mat0 _ 0 r c == @mat0 _ 0 r c.
  Proof. lma. Qed.
  
  Lemma mcmul_1_l : forall {r c} (m : mat r c), mcmul 1 m == m.
  Proof. lma. Qed.

  Lemma mcmul_1_r : forall {n} a, a c* @mat1 _ 0 1 n ==
                               fun ri ci => if (ri =? ci) then a else 0.
  Proof.
    intros n a. apply meq_iff.
    intros. unfold mat1,mcmul.
    destruct (i =? j); ring.
  Qed.
  
  Lemma mcmul_assoc : forall {r c} (a b : A) (m : mat r c), 
      a c* (b c* m) == (a * b) c* m.
  Proof. lma. Qed.
  
  Lemma mcmul_perm : forall {r c} (a b : A) (m : mat r c), 
      a c* (b c* m) == b c* (a c* m).
  Proof. lma. Qed.
  
  Lemma mcmul_add_distr_l : forall {r c} (a : A) (m1 m2 : mat r c), 
      a c* (m1 + m2) == ((a c* m1) + (a c* m2)).
  Proof. lma. Qed.
  
  Lemma mcmul_add_distr_r : forall {r c} (a b : A) (m : mat r c), 
      (a + b)%A c* m == (a c* m) + (b c* m).
  Proof. lma. Qed.

End mcmul.

Global Infix "c*" := mcmul : mat_scope.
Global Infix "*c" := mmulc : mat_scope.


(* ==================================== *)
(** ** Matrix transposition *)
Section mtrans.

  Context `{R:Ring}.
  Declare Scope A_scope.
  Delimit Scope A_scope with A.
  Open Scope A_scope.
  (* Infix "+" := add0 : A_scope. *)
  (* Infix "*" := mul0 : A_scope. *)
  Notation "0" := zero0 : A_scope.
  Notation "1" := one0 : A_scope.
  (* Notation "- x" := (opp x) : A_scope. *)
  (* Notation "a - b" := (a + (-b)) : A_scope. *)
  
  Definition mtrans {r c} (m : @mat A r c): mat c r :=
    fun x y => m y x.

  Notation "m 'ᵀ'" := (mtrans m) : mat_scope. 

  (** Transpose twice keep unchanged. *)
  Lemma mtrans_trans : forall {r c} (m : mat r c), mtrans (mtrans m) == m.
  Proof. lma. Qed.
  
  (** Transpose identity matrix keep unchanged. *)
  Lemma mat1_trans_eq : forall {n : nat}, (@mat1 _ 0 1 n)ᵀ == (@mat1 _ 0 1 n).
  Proof.
    by_cell. unfold mtrans, mat1. rewrite Nat.eqb_sym. auto.
  Qed.

  (** Transpose zero matrix won't change the data. *)
  Lemma mat0_trans_eq : forall {r c : nat}, (@mat0 _ 0 r c)ᵀ == @mat0 _ 0 c r.
  Proof. lma. Qed.
  
End mtrans.

Global Notation "m 'ᵀ'" := (mtrans m) : mat_scope. 


(* ==================================== *)
(** ** Matrix multiplication *)
Section mmul.

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

  (** 定义矩阵乘法 *)
  Definition mmul {r c s : nat} (m1 : mat r c) (m2 : @mat A c s) : @mat A r s :=
    fun x z => seqsum (fun y => m1 x y * m2 y z) c (add:=add0) (zero:=0).

  Infix "*" := mmul : mat_scope.
  Open Scope mat_scope.
  Notation "m1 + m2" := (madd m1 m2 (op:=add0)) : mat_scope.
  Notation "a c* m" := (mcmul a m (mul0:=mul0)) : mat_scope.
  Notation "m *c a" := (mmulc m a (mul0:=mul0)): mat_scope.

  Lemma mmul_assoc : forall {r c s t : nat} 
                       (m1 : mat r c) (m2 : @mat A c s) (m3: @mat A s t), 
      (m1 * m2) * m3 == m1 * (m2 * m3).
  Proof.
    intros. apply meq_iff; intros.
    unfold mmul.
    induction c.
    - simpl. clear m2.
      induction s. reflexivity.
      simpl. rewrite IHs. ring.
    - simpl.
      rewrite <- IHc.
      rewrite seqsum_cmul_l.
      rewrite <- seqsum_plusSeq.
      apply seqsum_eq. intros. ring.
  Qed.
  
  Lemma mmul_add_distr_l : forall {r c s : nat} 
                             (m1 : mat r c) (m2 m3 : @mat A c s), 
      m1 * (m2 + m3) == m1 * m2 + m1 * m3.
  Proof.
    by_cell. unfold mmul, madd.
    rewrite <- seqsum_plusSeq.
    apply seqsum_eq; intros. ring.
  Qed.
  
  Lemma mmul_add_distr_r : forall {r c s : nat} 
                             (m1 m2 : mat r c) (m3 : @mat A c s),
      (m1 + m2) * m3 == m1 * m3 + m2 * m3.
  Proof.
    by_cell. unfold mmul, madd.
    rewrite <- seqsum_plusSeq.
    apply seqsum_eq; intros. ring.
  Qed.

  Lemma mmul_0_l : forall {r c s} (m : @mat A c s),
      (@mat0 _ 0 r c) * m == @mat0 _ 0 r s.
  Proof.
    by_cell. unfold mmul,mat0. rewrite seqsum_seq0; auto. intros. ring.
  Qed.
  
  Lemma mmul_0_r : forall {r c s} (m : mat r c),
      m * (@mat0 _ 0 c s) == @mat0 _ 0 r s.
  Proof.
    by_cell. unfold mmul,mat0. rewrite seqsum_seq0; auto. intros. ring.
  Qed.
  
  Lemma mmul_1_l : forall {r c : nat} (m : mat r c), 
      @mat1 _ 0 1 r * m == m.
  Proof.
    intros. apply meq_iff; intros.
    unfold mmul,mat1.
    eapply seqsum_unique. apply H.
    rewrite Nat.eqb_refl. ring.
    intros. apply Nat.eqb_neq in H1. rewrite H1. ring.
  Qed.
  
  Lemma mmul_1_r : forall {r c : nat} (m : mat r c), 
      m * @mat1 _ 0 1 c == m.
  Proof.
    intros. apply meq_iff; intros.
    unfold mmul,mat1.
    eapply seqsum_unique. apply H0.
    rewrite Nat.eqb_refl. ring.
    intros. apply not_eq_sym in H1. apply Nat.eqb_neq in H1. rewrite H1. ring.
  Qed.
  
  Lemma mcmul_mul_distr_l : forall {r c s} (a : A) 
                              (m1 : mat r c) (m2 : @mat A c s), 
      (a c* m1) * m2 == a c* (m1 * m2).
  Proof.
    by_cell. unfold mcmul,mmul.
    rewrite seqsum_cmul_l.
    apply seqsum_eq. intros. ring.
  Qed.
  
  Lemma mcmul_mul_distr_r : forall {r c s} (a : A) 
                              (m1 : mat r c) (m2 : @mat A c s), 
      m1 * (a c* m2) == a c* (m1 * m2).
  Proof.
    by_cell. unfold mcmul,mmul.
    rewrite seqsum_cmul_l.
    apply seqsum_eq. intros. ring.
  Qed.

End mmul.

Global Infix "*" := mmul : mat_scope.


(* ==================================== *)
(** ** Square matrix *)

Section square_matrix.

  Context {A:Type}.
  Context {add : A -> A -> A}.
  Context {zero : A}.
  Context `{M:@Monoid A add zero}.
  
  Definition Square n := @mat A n n.
  
  (** Trace *)
  Definition trace {n : nat} (m : Square n) := 
    seqsum (fun x => m x x) n (add:=add) (zero:=zero).

End square_matrix.


 (* ==================================== *)
(** ** Other Operations and Properties *)

(** *** Convert between tuples and matrix *)
Section t2m_m2t.

  Context {A:Type}.
  Context {A0:A}.

  (** 一个元素 转换为 mat_1x1 *)
  Definition t2m_1x1 (a : A) : @mat A 1 1.
  Proof.
    exact (mk_mat_1_1 a (A0:=A0)).
  Defined.
  
  (** mat_1x1 转换为 一个元素 *)
  Definition m2t_1x1 (m : @mat A 1 1) : A := m 0 0.

  (** 2x2元组 转换为 mat_2x2 *)
  Definition t2m_2x2 (t : @T_2x2 A) : @mat A 2 2.
  Proof.
    destruct t as (t1,t2).
    destruct t1 as (a11,a12).
    destruct t2 as (a21,a22).
    exact (mk_mat_2_2 a11 a12 a21 a22 (A0:=A0)).
  Defined.
  
  (** mat_2x2 转换为 2x2元组 *)
  Definition m2t_2x2 (m : @mat A 2 2) : @T_2x2 A :=
    (
      (m 0 0, m 0 1),
      (m 1 0, m 1 1)
    ).
  
  (** 3x3元组 转换为 mat_3x3 *)
  Definition t2m_3x3 (t : @T_3x3 A) : @mat A 3 3.
  Proof.
    destruct t as ((t1,t2),t3).
    destruct t1 as ((a11,a12),a13).
    destruct t2 as ((a21,a22),a23).
    destruct t3 as ((a31,a32),a33).
    exact (mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 (A0:=A0)).
  Defined.

  (** mat_3x3 转换为 3x3元组 *)
  Definition m2t_3x3 (m : @mat A 3 3) : @T_3x3 A :=
    (
      (m 0 0, m 0 1, m 0 2),
      (m 1 0, m 1 1, m 1 2),
      (m 2 0, m 2 1, m 2 2)
    ).

End t2m_m2t.


(* ==================================== *)
(** ** 测试 *)

(** 在 R 上的矩阵测试 *)
Module test_matrix_R.

  (** 单态化：为特定类型给定默认值 *)
  Open Scope R.
  Definition mat0 := mat0 (A0:=0).

  Definition m1 : mat 2 3 := fun i j => INR (i + j).
  (* Compute mrow 0 m1. *)
  (* Compute mrow 1 m1. *)

  Definition m10 := mat0 3 4.
  (* Compute m10. *)
  Definition m11 := mmap (fun x => x + R1) m10.
  (* Compute m2l (m11). *)

End test_matrix_R.

(** 在 Q 上的矩阵测试 *)
Module test_matrix_Q.


  (** 单态化：为特定类型给定默认值 *)
  Open Scope Q.
  Definition mk_mat_3_3 := mk_mat_3_3 (A0:=0).
  Definition trace {n} (m : Square n) := trace m (add:=Qplus) (zero:=0).
  Definition madd {r c} (m1 m2:mat r c) := madd m1 m2 (op:=Qplus).
  Definition mmul {r c s} (m1:mat r c) (m2:mat c s) :=
    mmul m1 m2 (add0:=Qplus) (zero0:=0) (mul0:=Qmult).
  Infix "+" := madd.
  Infix "*" := mmul.

  (** 除了 Definition，还可以用 Notation 的方式来单态化 *)
  Notation l2m := (l2m (A0:=0)).

  Example m1 := mk_mat_3_3 1 2 3 4 5 6 7 8 9.
  (* Eval cbn in trace m1. *)
  (* Compute trace m1. *)
  (* Compute (m2l (m1 + m1)). *)
  (* Compute (m2l (m1 * m1)). *)

End test_matrix_Q.


(* (* ==================================== *) *)
(* (** ** Matrix Simplification *) *)

(* Ltac unify_matrix_dims tac :=  *)
(*   try reflexivity;  *)
(*   repeat (apply f_equal_gen; try reflexivity;  *)
(*           try (is_nat_equality; tac)). *)

(* Ltac restore_dims_rec A := *)
(*   match A with *)
(*   (* special cases *) *)
(*   | ?X * I _          => let A' := restore_dims_rec A in  *)
(*                         match type of A' with  *)
(*                         | @mat A ?m' ?n' =>  *)
(*                             constr:(@mmul m' n' n' A' (mat1 n')) *)
(*                         end *)
(*   | I _ * ?B          => let B' := restore_dims_rec B in  *)
(*                         match type of B' with  *)
(*                         | @mat A ?n' ?o' =>  *)
(*                             constr:(@mmul n' n' o' (mat1 n')  B') *)
(*                         end *)
(*   | ?X * @mat0 ?n ?n  => let A' := restore_dims_rec A in  *)
(*                         match type of A' with  *)
(*                         | @mat A ?m' ?n' =>  *)
(*                             constr:(@mmul m' n' n' A' (@mat0 n' n')) *)
(*                         end *)
(*   | @mat0 ?n ?n * ?B  => let B' := restore_dims_rec B in  *)
(*                         match type of B' with  *)
(*                         | @mat A ?n' ?o' =>  *)
(*                             constr:(@mmul n' n' o' (@mat0 n' n') B') *)
(*                         end *)
(*   | ?X * @mat0 ?n ?o  => let A' := restore_dims_rec A in  *)
(*                         match type of A' with  *)
(*                         | @mat A ?m' ?n' =>  *)
(*                             constr:(@mmul m' n' o A' (@mat0 n' o)) *)
(*                         end *)
(*   | @mat0 ?m ?n * ?B  => let B' := restore_dims_rec B in  *)
(*                         match type of B' with  *)
(*                         | @mat A ?n' ?o' =>  *)
(*                             constr:(@mmul n' n' o' (@mat0 m n') B') *)
(*                         end *)
(*   | ?X + @mat0 ?m ?n => let A' := restore_dims_rec A in  *)
(*                        match type of A' with  *)
(*                        | @mat A ?m' ?n' =>  *)
(*                            constr:(@madd m' n' A' (@mat0 m' n')) *)
(*                        end *)
(*   | @mat0 ?m ?n + ?B => let B' := restore_dims_rec B in  *)
(*                        match type of B' with  *)
(*                        | @mat A ?m' ?n' =>  *)
(*                            constr:(@madd m' n' (@mat0 m' n') B') *)
(*                        end *)
(*   (* general cases *) *)
(*   | ?X = ?B  => let A' := restore_dims_rec A in  *)
(*                let B' := restore_dims_rec B in  *)
(*                match type of A' with  *)
(*                | @mat A ?m' ?n' => constr:(@meq m' n' A' B') *)
(*                end *)
(*   | ?X * ?B   => let A' := restore_dims_rec A in  *)
(*                 let B' := restore_dims_rec B in  *)
(*                 match type of A' with  *)
(*                 | @mat A ?m' ?n' => *)
(*                     match type of B' with  *)
(*                     | @mat A ?n'' ?o' => constr:(@mmul m' n' o' A' B') *)
(*                     end *)
(*                 end  *)
(*   | ?X + ?B => let A' := restore_dims_rec A in  *)
(*               let B' := restore_dims_rec B in  *)
(*               match type of A' with  *)
(*               | @mat A ?m' ?n' => *)
(*                   match type of B' with  *)
(*                   | @mat A ?m'' ?n'' => constr:(@madd m' n' A' B') *)
(*                   end *)
(*               end *)
(*   | ?c * ?X => let A' := restore_dims_rec A in  *)
(*               match type of A' with *)
(*               | @mat A ?m' ?n' => constr:(@mcmul m' n' c A') *)
(*               end *)
(*   (* Handle functions applied to matrices *) *)
(*   | ?f ?X    => let f' := restore_dims_rec f in  *)
(*                let A' := restore_dims_rec A in  *)
(*                constr:(f' A') *)
(*   (* default *) *)
(*   | ?X       => A *)
(*   end. *)

(* Ltac restore_dims tac :=  *)
(*   match goal with *)
(*   | |- ?X      => let A' := restore_dims_rec A in  *)
(*                 replace A with A' by unify_matrix_dims tac *)
(*   end. *)

(* (* 终于合成了两个可带或可不带参数的策略 *) *)
(* Tactic Notation "restore_dims" tactic(tac) := restore_dims tac. *)

(* Tactic Notation "restore_dims" :=  *)
(*   restore_dims (try ring; unify_pows_two; simpl; lia). *)

(* (* 数据库名称可能的解释， U_db : User database *) *)
(* Global Hint Unfold madd mmul mcmul mat1 : U_db.  *)

(* Hint Rewrite @mmul_1_l @mmul_1_r @mcmul_1_l @mat1_trans_eq : M_db_light. *)
(* Hint Rewrite @mmul_0_l @mmul_0_r @madd_0_l @madd_0_r *)
(*   @mcmul_0_l @mcmul_0_r @mat0_trans_eq : M_db_light. *)

(* (* I don't like always doing restore_dims first, but otherwise sometimes leaves  *)
(*      unsolvable WF_Matrix goals. *) *)
(* Ltac Msimpl_light := restore_dims; autorewrite with M_db_light. *)

(* Ltac Msimpl := restore_dims; autorewrite with M_db_light. *)

