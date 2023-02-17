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


Require Export MatrixThySig.

Require Import NatExt ListListExt.
Require Import Arith Lia Lra.
Require Import Setoid. (* R => R', Morphisms.respectful R R' *)
Require Import Sequence.


(* ######################################################################### *)
(** * Matrix theory *)
Module MatrixThy (F : FieldSig) <: MatrixThySig F.
  
  (** Carrier Type *)
  Module Export FieldThyInst := FieldThy F.
  
  (** Sequence, for matrix multiplication *)
  Module Export SequenceInst := Sequence F.
  
  Open Scope nat.
  Open Scope X_scope.
  Open Scope mat_scope.
  
  (* ==================================== *)
  (** ** Definition of matrix *)
  
  Section Def.
    
    (** Type of matrix data, mapping from two index of number to value of X 
      type. *)
    Definition MATData X := nat -> nat -> X.
    
    (** We define a _matrix_ as a simple function from two nats
        (corresponding to a row and a column) to a value. 
        Note that, mat' is real type, M is a dummy type of mat', because M 
        contain two parameters but without use it. That means, m and n are 
        two fake parameters, but it could be used to represent shape of the 
        matrix. *)
    
    (* 使用 Record 和 Inductive，这两种方式有何区别？
    另外，Coq报错，称 M 不满足 Sig 签名，提示要改名，暂不知原因。
    经过实践，Record 比 Inductive 更好一点，因为访问字段有了专门的名字。*)
    Record mat' X (r c : nat) := mk_mat {
                                     mdata : MATData X
                                   }.
    Inductive mat'' X (r c : nat) := mk_mat'' (g : MATData X).
    
    Definition mat X r c := (mat' X r c).
    
  (** 使用 M 而不是 mat', 是因为Coq报错，称不满足 Sig 签名，提示要这么做。
      暂时不知道什么原因。*) 

    (*     Bind Scope mat_scope with mat. *)
    
  End Def.
  
  Arguments mk_mat {X}.
  Arguments mdata {X r c}.
  Notation M r c := (mat X r c).
  
  
  (* ==================================== *)
  (** ** Equality of matrix *)
  Section meq.
    (** Note that the dimensions of the matrix aren'X being used here. In
        practice, a matrix is simply a function on any two nats. However,
        we will used these dimensions to define equality. *)

    (** If every corresponding elements of two matrices are equal, then they 
      are considered equal. *)
    Definition meq {r c : nat} (m1 m2 : M r c) : Prop := 
      let g1 := mdata m1 in 
      let g2 := mdata m2 in
      forall i j, i < r -> j < c -> g1 i j = g2 i j.
    
    Lemma meq_refl : forall {r c} (m : M r c), meq m m.
    Proof.
      intros r c [g]. intros i j Hi Hj. auto.
    Qed.
    
    Lemma meq_sym : forall {r c} (m1 m2 : M r c), meq m1 m2 -> meq m2 m1.
    Proof.
      intros r c [g1] [g2] H. unfold meq in *. intros; simpl in *.
      rewrite H; auto.
    Qed.
    
    Lemma meq_trans : forall {r c} (m1 m2 m3 : M r c), 
        meq m1 m2 -> meq m2 m3 -> meq m1 m3.
    Proof.
      intros r c [g1] [g2] [g3] H. unfold meq in *. intros; simpl in *.
      rewrite H; auto.
    Qed.
    
    (** Register meq equivalence relation to Coq to enable rewring support. *)
    Global Add Parametric Relation (r c : nat) : (M r c) meq
           reflexivity proved by meq_refl
           symmetry proved by meq_sym
           transitivity proved by meq_trans
           as meq_rel.
    
    (** Meq is decidable (on equivalence relation) *)
    Lemma meq_dec_equiv : forall {r c} (m1 m2 : M r c), {meq m1 m2} + {~(meq m1 m2)}.
    Proof.
      intros r c [g1] [g2]. simpl. apply seq2eq_dec.
    Qed.
    
    (** This is a temperary solution, perfect solution see MathComp. *)
    Section AXIOM_FOR_REWRITE_TEMPORARY_SOLUTION.
      
      Axiom meq_iff : forall {r c} (m1 m2 : M r c), m1 = m2 <-> meq m1 m2.
      
      Lemma meq_imply_eq : forall {r c} (m1 m2 : M r c), meq m1 m2 -> m1 = m2.
      Proof.
        intros. apply meq_iff. auto.
      Qed.
      
      Lemma eq_imply_meq : forall {r c} (m1 m2 : M r c), m1 = m2 -> meq m1 m2.
      Proof.
        intros; subst. reflexivity.
      Qed.
      
      Lemma mneq_imply_neq : forall {r c} (m1 m2 : M r c), ~(meq m1 m2) -> m1 <> m2.
      Proof.
        intros. intro. apply meq_iff in H0. auto.
      Qed.
      
      Lemma neq_imply_mneq : forall {r c} (m1 m2 : M r c), m1 <> m2 -> ~(meq m1 m2).
      Proof.
        intros; subst. intro. apply meq_imply_eq in H0. auto.
      Qed.
      
    End AXIOM_FOR_REWRITE_TEMPORARY_SOLUTION.
    
    (** Meq is decidable *)
    Lemma meq_dec : forall {r c} (m1 m2 : M r c), {m1 = m2} + {m1 <> m2}.
    Proof.
      intros. destruct (meq_dec_equiv m1 m2) as [H | H].
      apply meq_iff in H. auto.
      right. intro. apply meq_iff in H0. auto.
    Qed.
    
  End meq.
  
  (*   Notation "m1 == m2" := (meq m1 m2) (at level 70) : mat_scope. *)
  
  
  (* ==================================== *)
  (** ** Get element *)
  Section mnth.
    
    Definition mnth {r c} (m : M r c) (ri ci : nat) : X := (mdata m) ri ci.
    
    Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : M r c),
        m1 = m2 <-> 
          (forall ri ci, ri < r -> ci < c -> mnth m1 ri ci = mnth m2 ri ci).
    Proof.
      intros. split; intros. subst; auto.
      apply meq_iff. auto.
    Qed.
    
  End mnth.

  
  (* ==================================== *)
  (** ** Get row *)
  Section mrow.
    
    (* Aux function, cnt initial is 0 *)
    (* 取出第 ri 行的数据。
      1. 列元素个数为 c 个
      2. 列偏移量为 cnt，如果为0则正好，不为0，则超出部分的数据不保证正确
     *)
    Fixpoint mrow_aux {r c : nat} (ri : nat) (cnt : nat) (m : M r c) : list X :=
      match c with
      | O => nil
      | S c' =>
          let g := mdata m in
          let m' := mk_mat r c' g in
          g ri cnt :: (@mrow_aux r c' ri (S cnt) m')
      end.
    
    Lemma mrow_aux_length : forall {r c} ri c_init (m : M r c), 
        length (mrow_aux ri c_init m) = c.
    Proof.
      intros. destruct m. gd c_init.
      induction c; auto. intros. simpl. auto.
    Qed.
    
    Definition mrow {r c : nat} (ri : nat) (m : M r c) := @mrow_aux r c ri 0 m.
    
    (** (mrow_aux m i c_init)[j] = m[i][j + c_init] *)
    
    Lemma mrow_aux_nth : forall {r c} ri ci c_init (m : M r c) a,
        ri < r -> ci < c ->
        nth ci (mrow_aux ri c_init m) a = (mdata m) ri (ci + c_init)%nat.
    Proof.
      intros. destruct m. gd ci. gd ri. gd c_init. gd r.
      induction c; intros. lia.
      destruct ci; auto. simpl.
      rewrite IHc; auto. intuition.
    Qed.

    Lemma mrow_length : forall {r c} ri (m : M r c), length (mrow ri m) = c.
    Proof.
      intros. unfold mrow. apply mrow_aux_length.
    Qed.
    
    (** (mrow m i)[j] = m[i][j] *)
    Lemma mrow_nth : forall {r c} ri ci (m : M r c) a,
        ri < r -> ci < c ->
        nth ci (mrow ri m) a = (mdata m) ri ci.
    Proof.
      intros. unfold mrow.
      rewrite mrow_aux_nth; auto.
    Qed.
    
  End mrow.


  (* ==================================== *)
  (** Convert between list and M *)
  Section cvt_lst_and_mat.
    
    (** list list to M *)
    
    (* 指定矩阵形状 *)
    Definition l2m {r c} (dl : list (list X)) : M r c := 
      mk_mat _ _ (fun x y => nth y (nth x dl []) X0).
    
    (* 自动计算矩阵形状 *)
    Definition l2m' (dl : @list (list X)) : M (length dl) (length (hd [] dl)) :=
      mk_mat _ _ (fun x y => nth y (nth x dl []) X0).

    (** M to list list *)
    Fixpoint m2l_aux {r c : nat} (cnt : nat) (m : M r c) : list (list X) := 
      match r with
      | O => nil
      | S r' =>
          let g := mdata m in
          let m' := mk_mat _ _ g in
          mrow cnt m :: (@m2l_aux r' c (S cnt) m')
      end.
    
    Lemma m2l_aux_length : forall {r c} cnt (m : M r c), length (m2l_aux cnt m) = r.
    Proof.
      induction r; auto. intros. simpl. destruct r; auto.
    Qed.
    
    Lemma m2l_aux_width : forall {r c} cnt {m : M r c}, width (m2l_aux cnt m) c.
    Proof.
      induction r; intros; simpl; auto. split.
      - apply mrow_length.
      - auto.
    Qed.
    
    Definition m2l {r c} (m : M r c) := m2l_aux 0 m.

    Lemma m2l_length : forall {r c} (m : M r c), length (m2l m) = r.
    Proof.
      unfold m2l. intros; apply m2l_aux_length.
    Qed.
    
    Lemma m2l_width : forall {r c} (m : M r c), width (m2l m) c.
    Proof.
      intros. apply m2l_aux_width.
    Qed.
    
    (* 不越界时取出有效的数据 *)
    Lemma nth_mrow_aux : forall {r c} (m : M r c) ri ci c_init,
        let g := mdata m in
        (ri < r) -> (ci + c_init < c) ->
        nth ci (mrow_aux ri c_init m) X0 = g ri (ci + c_init)%nat.
    Proof.
      (* 第一次证明，最后的不等式无法证明 *)
      intros r c. gd r. induction c.
      - intros. lia.
      - intros. simpl. destruct ci; auto. simpl. rewrite IHc; auto.
    Admitted.
    
    Lemma nth_mrow : forall {r c} (m : M r c) ri ci,
        let g := mdata m in
        (ri < r) -> (ci < c) ->
        nth ci (mrow ri m) X0 = g ri ci.
    Proof.
      intros. unfold mrow.
      rewrite nth_mrow_aux; auto. intuition.
    Qed.
    
    Lemma nth_nth_m2l_aux : forall {r c} (m : M r c) (ri ci r_init : nat),
        let g := mdata m in
        (ri < r) -> (ci < c) -> (ri + r_init < r) ->
        nth ci (nth ri (m2l_aux r_init m) []) X0 = g (ri + r_init)%nat ci.
    Proof.
      induction r; intros. lia.
      destruct ri; simpl. apply nth_mrow; auto.
      rewrite IHr; auto. lia.
    Admitted.
    
    Lemma l2m_m2l_id : forall {r c} (m : M r c),
        l2m (m2l m) =  m. 
    Proof.
      intros. apply meq_iff. unfold m2l,l2m. unfold meq; intros.
      destruct m. simpl. rewrite nth_nth_m2l_aux; auto. lia.
    Qed.
    
    Lemma m2l_aux_nth_nth : forall {r c} (dl : list (list X))
                                   (H1 : length dl = r) (H2 : width dl c),
        @m2l_aux r c 0 (mk_mat _ _ (fun x y : nat => nth y (nth x dl []) X0)) 
        = dl.
    Proof.
      intros. gd dl. gd c.
      induction r; intros.
      - apply length_zero_iff_nil in H1. subst. simpl. auto.
      - simpl. destruct dl.
        + simpl in H1. lia.
        + f_equal.
    Admitted.
    
    Lemma m2l_l2m_id : forall {r c} (dl : list (list X)),
        (length dl = r) -> (width dl c) -> m2l (@l2m r c dl) = dl.
    Proof.
      unfold m2l,l2m.
      destruct r.
      - intros. apply length_zero_iff_nil in H. subst. simpl. auto.
      - intros. rewrite m2l_aux_nth_nth; auto.
    Qed.
    
    Lemma l2m_inj : forall {r c} (d1 d2 : list (list X)),
        length d1 = r -> width d1 c -> length d2 = r -> width d2 c -> 
        d1 <> d2 -> @l2m r c d1 <> l2m d2.
    Proof.
    Admitted.
    
    Lemma l2m_surj : forall {r c} (m : M r c), (exists d, l2m d = m).
    Proof.
    Admitted.
    
    Lemma m2l_inj : forall {r c} (m1 m2 : M r c), m1 <> m2 -> m2l m1 <> m2l m2.
    Proof.
    Admitted.
    
    Lemma m2l_surj : forall {r c} (d : list (list X)), 
        length d = r -> width d c -> (exists m, @m2l r c m = d).
    Proof.
    Admitted.
    
  End cvt_lst_and_mat.
  
  Global Hint Resolve m2l_length : mat.
  Global Hint Resolve m2l_width : mat.
  

  (* ==================================== *)
  (** ** Get column *)
  Section mcol.
    
    (* Aux function, cnt initial is 0 *)
    Fixpoint MCol_aux (r c : nat) (ci : nat) (cnt : nat) (m : M r c) : list X :=
      match r with
      | O => nil
      | S r' =>
          let g := (mdata m) in
          let m' := mk_mat _ _ g in
          g cnt ci :: (MCol_aux r' c ci (S cnt) m')
      end.
    Definition MCol {r c : nat} (ci : nat) (m : M r c) := MCol_aux r c ci 0 m.
    
  End mcol.
  
  
  (* ==================================== *)
  (** ** Right shift columns *)
  Section mshift.
    
    (** Right shift columns *)
    Definition mshiftc {r c} (m : M r c) (k : nat) : M r c :=
      let g := mdata m in
      mk_mat _ _ (fun i j => g i (j + k)%nat).
    
    (** ∃ X X' k (X = X' /\ mshiftc X k <> mshiftc X' k *)
    Lemma mshiftc_neq : exists r c (m1 m2 : M r c) (k : nat),
        m1 = m2 /\ mshiftc m1 k <> mshiftc m2 k. 
    Proof.
      set (m1 := mk_mat 2 2 (fun i j => if (j <? 2)%nat then X1 else X0)).
      set (m2 := mk_mat 2 2 (fun i j => if (j <? 3)%nat then X1 else X0)).
      exists _, _, m1, m2, (1%nat). split.
      - apply meq_iff. unfold m1, m2. intros i j Hi Hj. simpl.
        destruct j as [|[|]]; destruct i as [|[|]]; trivial; lia.
      - intros F.
        assert (1 < 2)%nat by lia.
        apply meq_iff in F.
        specialize (F _ _ H H).
        unfold m1, m2, mshiftc in F.
        simpl in F.
        apply X1_neq_X0; auto.
    Qed.
    
  End mshift.
  
  
  (* ==================================== *)
  (** ** Matrix Automation *)
  
  (** Useful tactic for solving X = B for concrete X, B *)

  Ltac solve_end :=
    match goal with
    | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
    end.

  Ltac by_cell := 
    intros; try apply meq_imply_eq;
    let i := fresh "i" in 
    let j := fresh "j" in 
    let Hi := fresh "Hi" in 
    let Hj := fresh "Hj" in 
    intros i j Hi Hj; try solve_end;
    repeat (destruct i as [|i]; simpl; 
            [|apply lt_S_n in Hi]; try solve_end); clear Hi;
    repeat (destruct j as [|j]; simpl; 
            [|apply lt_S_n in Hj]; try solve_end); clear Hj.

  Ltac lma := by_cell; compute; ring.
  
  
  (* ==================================== *)
  (** ** 指定维数的矩阵的创建函数 *)
  Section SpecifyDims.
    
    Definition mk_mat_0_c c : M 0 c.
    Proof.
      refine (l2m []).
    Defined.
    
    Definition mk_mat_1_1 (a11 : X) : M 1 1.
    Proof.
      refine (l2m [[a11]]).
    Defined.
    
    Definition mk_mat_1_2 (a11 a12 : X) : M 1 2.
    Proof.
      refine (l2m [[a11;a12]]).
    Defined.
    
    Definition mk_mat_1_3 (a11 a12 a13 : X) : M 1 3.
    Proof.
      refine (l2m [[a11;a12;a13]]).
    Defined.
    
    Definition mk_mat_1_4 (a11 a12 a13 a14 : X) : M 1 4.
    Proof.
      refine (l2m [[a11;a12;a13;a14]]).
    Defined.
    
    Definition mk_mat_1_c c (l : list X) : M 1 c.
    Proof.
      refine (l2m [l]).
    Defined.
    
    Definition mk_mat_r_0 r : M r 0.
    Proof.
      refine (l2m []).
    Defined.
    
    Definition mk_mat_2_1 (a11 a21 : X) : M 2 1.
    Proof.
      refine (l2m [[a11];[a21]]).
    Defined.
    
    Definition mk_mat_2_2 (a11 a12 a21 a22 : X) : M 2 2.
    Proof.
      refine (l2m [[a11;a12];[a21;a22]]).
    Defined.
    
    Definition mk_mat_3_1 (a11 a21 a31 : X) : M 3 1.
    Proof.
      refine (l2m [[a11];[a21];[a31]]).
    Defined.
    
    Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : X) : M 3 3.
    Proof.
      refine (l2m [[a11;a12;a13]; [a21;a22;a23]; [a31;a32;a33]]).
    Defined.
    
    Definition mk_mat_4_1 (a11 a21 a31 a41 : X) : M 4 1.
    Proof.
      refine (l2m [[a11];[a21];[a31];[a41]]).
    Defined.
    
    Definition mk_mat_4_4 (a11 a12 a13 a14 a21 a22 a23 a24 
                             a31 a32 a33 a34 a41 a42 a43 a44 : X) : M 4 4.
    Proof.
      refine (l2m [[a11;a12;a13;a14]; [a21;a22;a23;a24]; 
                   [a31;a32;a33;a34]; [a41;a42;a43;a44]]).
    Defined.
    
    Definition mk_mat_r_1 r (l : list X) : M r 1.
    Proof.
      set (g:= (fun ri ci : nat => 
                  if (ci =? 0)%nat then (nth ri l X0) else X0)).
      refine (mk_mat _ _ g).
    Defined.
    
  End SpecifyDims.
  
  
  (* ==================================== *)
  (** ** 矩阵映射 *)
  Section Map.
    
    Definition mmap {r c} (f : X -> X) (m : M r c) : M r c :=
      let g := mdata m in
      mk_mat _ _ (fun i j => f (g i j)).
    
    Definition mmap2 {r c} (f : X -> X -> X) (m1 m2 : M r c) : M r c :=
      let g1 := mdata m1 in
      let g2 := mdata m2 in
      mk_mat _ _ (fun i j => f (g1 i j) (g2 i j)).
    
    Lemma mmap2_comm : forall {r c} (f : X -> X -> X)
                         (f_comm : forall a b : X, f a b = f b a)
                         (m1 m2 : M r c), 
        mmap2 f m1 m2 = mmap2 f m2 m1.
    Proof.
      intros r c f H1. intros m1 m2.
      apply meq_iff. intros i j Hi Hj.
      unfold mmap2. simpl. auto.
    Qed.
    
    Lemma mmap2_assoc : forall {r c} (f : X -> X -> X)
                          (f_assoc : forall a b c, f a (f b c) = f (f a b) c)
                          (m1 m2 m3 : M r c), 
        mmap2 f (mmap2 f m1 m2) m3 = mmap2 f m1 (mmap2 f m2 m3).
    Proof.
      intros r c f H1. intros m1 m2 m3.
      apply meq_iff. intros i j Hi Hj.
      unfold mmap2. simpl. auto.
    Qed.
    
  End Map.
  
  
  (* ==================================== *)
  (** ** 零矩阵和单位矩阵 *)
  Section Mat1_Mat0.

    (* Zero M *)
    Definition mat0 (r c : nat) : M r c := mk_mat _ _ (fun _ _ => X0).
    
    (* Identity M *)
    Definition mat1 (n : nat) : M n n :=
      mk_mat _ _ (fun i j => if (i =? j)%nat then X1 else X0).
    
  End Mat1_Mat0.
  
  
  (* ==================================== *)
  (** ** 矩阵加法 *)
  Section madd.
    
    Definition madd {r c} (m1 m2 : M r c) : M r c :=
      let g1 := mdata m1 in
      let g2 := mdata m2 in
      mk_mat _ _ (fun i j => g1 i j + g2 i j).
    
  End madd.
  
  Global Infix "+" := madd : mat_scope.

  
  (* ==================================== *)
  (** ** 矩阵加法的性质 *)
  Section madd_props.

    Lemma madd_comm : forall {r c} (m1 m2 : M r c), m1 + m2 = (m2 + m1).
    Proof.
      lma.
    Qed.
    
    Lemma madd_assoc : forall {r c} (m1 m2 m3 : M r c), 
        (m1 + m2) + m3 = m1 + (m2 + m3).
    Proof.
      lma.
    Qed.
    
    Lemma madd_0_l : forall {r c} (m : M r c), mat0 r c + m = m. 
    Proof.
      lma.
    Qed.
    
    Lemma madd_0_r : forall {r c} (m : M r c), m + mat0 r c = m. 
    Proof.
      lma.
    Qed.
    
    (** Get element of addition with two matrics equal to additon of 
      corresponded elements. *)
    Lemma madd_nth : forall {r c} (m1 m2 : M r c) ri ci,
        mnth (m1 + m2) ri ci = ((mnth m1 ri ci) + (mnth m2 ri ci))%X.
    Proof.
      intros. auto.
    Qed.
    
    (** 加法与 mrow 的关系 *)
    
    (* (m1 + m2)[0] = m1[0] + m2[0] *)
    Lemma mrow_aux_prop1 : forall {r c} (m1 m2 : M r c),
        (0 < r) ->
        mrow_aux 0 0 (m1 + m2) = 
          map2 Xadd (mrow_aux 0 0 m1) (mrow_aux 0 0 m2).
    Proof.
      intros r c. gd r. induction c.
      - intros. simpl. auto.
      - intros. simpl. f_equal.
        eapply nth_ext.
        + rewrite mrow_aux_length. 
          rewrite map2_length with (n := c); auto.
          apply mrow_aux_length.
          apply mrow_aux_length.
        + intros. 
          rewrite mrow_aux_length in H0.
          rewrite mrow_aux_nth; auto.
          rewrite map2_nth.
          repeat rewrite mrow_aux_nth; auto.
          rewrite mrow_aux_length; auto.
          rewrite mrow_aux_length; auto.
          Unshelve. exact X0. exact X0.
    Qed.
    
  End madd_props.
  
  
  (* ==================================== *)
  (** ** Matrix subtraction *)
  Section msub.
    
    Definition mopp {r c} (m : M r c) : M r c :=
      let g := mdata m in
      mk_mat _ _ (fun i j => - (g i j)).
    
    Definition msub {r c} (m1 m2 : M r c) : M r c := 
      let g1 := mdata m1 in
      let g2 := mdata m2 in
      mk_mat _ _ (fun i j => g1 i j - g2 i j).
    
  End msub.
  
  Global Notation "- a" := (mopp a) : mat_scope.
  Global Infix "-" := msub : mat_scope.
  
  
  (* ==================================== *)
  (** ** Properties of matrix subtraction *)
  Section msub_props.
    
    Lemma mopp_opp : forall {r c} (m : M r c), - (- m) = m.
    Proof.
      lma.
    Qed.
    
    Lemma msub_comm : forall {r c} (m1 m2 : M r c), m1 - m2 = - (m2 - m1).
    Proof.
      lma.
    Qed.
    
    Lemma msub_assoc : forall {r c} (m1 m2 m3 : M r c), (m1 - m2) - m3 = m1 - (m2 + m3).
    Proof.
      lma.
    Qed.
    
    Lemma msub_0_l : forall {r c} (m : M r c), (mat0 r c) - m = - m.
    Proof.
      lma.
    Qed.
    
    Lemma msub_0_r : forall {r c} (m : M r c), m - (mat0 r c) = m.
    Proof.
      lma.
    Qed.
    
    Lemma madd_opp : forall r c (m : M r c), m + (-m) = mat0 r c.
    Proof.
      lma.
    Qed.
    
    Lemma msub_self : forall {r c} (m : M r c), m - m = (mat0 r c).
    Proof.
      lma.
    Qed.

  End msub_props.
  
  
  (* ==================================== *)
  (** ** Constant multiplication of matrix *)
  Section mcmul.
    
    Definition mcmul {r c} (a : X) (m : M r c) : M r c :=
      let g := mdata m in
      mk_mat _ _ (fun i j => (a * g i j)).
    
    Definition mmulc {r c} (m : M r c) (a : X) : M r c :=
      let g := mdata m in
      mk_mat _ _ (fun i j => (g i j * a)).

  End mcmul.
  
  Global Infix "c*" := mcmul : mat_scope.
  Global Infix "*c" := mmulc : mat_scope.
  
  
  (* ==================================== *)
  (** ** Properties for constant multiplication of matrix *)
  Section mcmul_props.
    
    Lemma mmulc_eq_mcmul : forall {r c} (a : X) (m : M r c), 
        m *c a = a c* m.
    Proof.
      lma.
    Qed.
    
    Lemma mcmul_0_l : forall {r c} (m : M r c), X0 c* m = mat0 r c.
    Proof.
      lma.
    Qed.
    
    Lemma mcmul_0_r : forall {r c} a, a c* mat0 r c = mat0 r c.
    Proof.
      lma.
    Qed.
    
    Lemma mcmul_1_l : forall {r c} (m : M r c), mcmul X1 m = m.
    Proof.
      lma.
    Qed.
    
    Lemma mcmul_1_r : forall {n} a,
        a c* mat1 n =
          mk_mat _ _ (fun ri ci => if (ri =? ci)%nat then a else X0).
    Proof.
      intros n a. apply meq_iff.
      intros i j _ _.
      unfold mat1. unfold mcmul. simpl.
      destruct (i =? j)%nat; cbv; ring.
    Qed.
    
    Lemma mcmul_assoc : forall {r c} (a b : X) (m : M r c), 
        a c* (b c* m) = (a * b) c* m.
    Proof.
      lma.
    Qed.
    
    Lemma mcmul_perm : forall {r c} (a b : X) (m : M r c), 
        a c* (b c* m) = b c* (a c* m).
    Proof.
      lma.
    Qed.
    
    Lemma mcmul_add_distr_l : forall {r c} (a : X) (m1 m2 : M r c), 
        a c* (m1 + m2)%M = ((a c* m1) + (a c* m2))%M.
    Proof.
      lma.
    Qed.
    
    Lemma mcmul_add_distr_r : forall {r c} (a b : X) (m : M r c), 
        (a + b)%X c* m = ((a c* m) + (b c* m))%M.
    Proof.
      lma.
    Qed.
    
  End mcmul_props.
  
  
  (* ==================================== *)
  (** ** Matrix transposition *)
  Section mtrans.
    
    Definition mtrans {r c} (m : M r c): M c r :=
      let g := mdata m in
      mk_mat _ _ (fun x y => g y x).
    
  End mtrans.
  
  Global Notation "X 'ᵀ'" := (mtrans X) : mat_scope. 
  
  
  (* ==================================== *)
  (** ** Properties of matrix transposition *)
  Section mtrans_props.
    
    (** Transpose twice keep unchanged. *)
    Lemma mtrans_trans : forall {r c} (m : M r c), mtrans (mtrans m) = m.
    Proof.
      lma.
    Qed.
    
    (** Transpose identity matrix keep unchanged. *)
    Lemma mat1_trans_eq : forall {n : nat}, (mat1 n)ᵀ = (mat1 n).
    Proof.
      intros. by_cell.
      unfold mtrans, mat1. simpl.
      rewrite Nat.eqb_sym.
      reflexivity.
    Qed.

    (** Transpose zero matrix keep unchanged. *)
    Lemma mat0_trans_eq : forall {r c : nat}, (@mat0 r c)ᵀ = @mat0 c r.
    Proof.
      reflexivity.
    Qed.
    
  End mtrans_props.
  
  
  (* ==================================== *)
  (** ** Matrix multiplication *)
  Section mmul.
    
    Definition mmul {r c t : nat} (m1 : M r c) (m2 : M c t) : M r t :=
      let g1 := mdata m1 in
      let g2 := mdata m2 in
      mk_mat _ _ (fun x z => seqsum (fun y => g1 x y * g2 y z) c).
    
  End mmul.
  
  Global Infix "*" := mmul : mat_scope.
  
  
  (* ==================================== *)
  (** ** Properties of matrix multiplication *)
  Section mmul_props.

    Lemma mmul_assoc : forall {r c s t : nat} (m1 : M r c) (m2 : M c s) (m3: M s t), 
        (m1 * m2) * m3 = m1 * (m2 * m3).
    Proof.
      intros r c s t [g1] [g2] [g3]; apply meq_iff.
      intros i j Hi Hj. simpl.
      induction c.
      - simpl.
        induction s; auto. simpl. rewrite IHs.
        cbv. ring.
      - simpl.
        rewrite <- IHc.
        rewrite seqsum_cmul_l.
        rewrite <- seqsum_plusSeq.
        apply seqsum_eq; intros. ring.
    Qed.
    
    Lemma mmul_add_distr_l : forall {r c s : nat} (m1 : M r c) (m2 m3 : M c s), 
        m1 * (m2 + m3) = m1 * m2 + m1 * m3.
    Proof.
      intros r c s [g1] [g2] [g3]. apply meq_iff; intros i j _ _. simpl.
      rewrite <- seqsum_plusSeq.
      apply seqsum_eq; intros. ring.
    Qed.
    
    Lemma mmul_add_distr_r : forall {r c s : nat} (m1 m2 : M r c) (m3 : M c s),
        (m1 + m2) * m3 = m1 * m3 + m2 * m3.
    Proof. 
      intros r c s [g1] [g2] [g3]. apply meq_iff; intros i j _ _. simpl.
      rewrite <- seqsum_plusSeq.
      apply seqsum_eq; intros. ring.
    Qed.

    Lemma mmul_0_l : forall {r c s} (m : M c s), (mat0 r c) * m = mat0 r s.
    Proof.
      intros r c s [g].
      apply meq_iff; intros i j Hi Hj. simpl.
      rewrite seqsum_seq0; auto. intros. cbv; ring.
    Qed.
    
    Lemma mmul_0_r : forall {r c s} (m : M r c), m * (mat0 c s) = mat0 r s.
    Proof.
      intros r c s [g]; apply meq_iff; intros i j Hi Hj. simpl.
      rewrite seqsum_seq0; auto. intros. cbv; ring.
    Qed.
    
    Lemma mmul_1_l : forall {r c : nat} (m : M r c), mat1 r * m = m.
    Proof.
      intros m n [g]; apply meq_iff; intros i j Hi Hj. simpl.
      eapply seqsum_unique. apply Hi.
      unfold mat1. rewrite Nat.eqb_refl. cbv; ring.
      intros x Hx.
      apply Nat.eqb_neq in Hx. rewrite Hx. cbv; ring.
    Qed.
    
    Lemma mmul_1_r : forall {r c : nat} (m : M r c), m * mat1 c = m.
    Proof.
      intros m n [g]; apply meq_iff; intros i j Hi Hj. simpl.
      eapply seqsum_unique. apply Hj.
      unfold mat1. rewrite Nat.eqb_refl. cbv; ring.
      intros x Hx.
      apply Nat.eqb_neq in Hx. rewrite Nat.eqb_sym. rewrite Hx. cbv; ring.
    Qed.
    
    Lemma mcmul_mul_distr_l : forall {r c s} (a : X) (m1 : M r c) (m2 : M c s), 
        (a c* m1) * m2 = a c* (m1 * m2).
    Proof.
      intros r c s a [g1] [g2]; apply meq_iff; intros i j _ _ . simpl.
      rewrite seqsum_cmul_l.
      apply seqsum_eq. intros. ring.
    Qed.
    
    Lemma mcmul_mul_distr_r : forall {r c s} (a : X) (m1 : M r c) (m2 : M c s), 
        m1 * (a c* m2) = a c* (m1 * m2).
    Proof.
      intros r c s a [g1] [g2]; apply meq_iff; intros i j _ _ . simpl.
      rewrite seqsum_cmul_l.
      apply seqsum_eq. intros. ring.
    Qed.
    
  End mmul_props.
  
  
  (* ==================================== *)
  (** ** Other OPs and PROPs *)
  
  (** Convert between tuples and matrix *)
  
  (** 3x3元组 转换为 mat_3x3 *)
  Definition t2m_3x3 (t : @T_3x3 X) : M 3 3.
  Proof.
    destruct t as ((t1,t2),t3).
    destruct t1 as ((a11,a12),a13).
    destruct t2 as ((a21,a22),a23).
    destruct t3 as ((a31,a32),a33).
    exact (mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33).
  Defined.
  
  (** mat_3x3 转换为 3x3元组 ((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) *)
  Definition m2t_3x3 (m : M 3 3) : @T_3x3 X :=
    let g := mdata m in (
                       (g 0 0, g 0 1, g 0 2),
                       (g 1 0, g 1 1, g 1 2),
                       (g 2 0, g 2 1, g 2 2)
                     )%nat.
  
  (** 取出1x1矩阵的第 0,0 个元素 *)
  Definition scalar_of_mat (m : M 1 1) := mnth m 0 0.
  

  (*   
  (* ==================================== *)
  (** ** Matrix Simplification *)

  Ltac unify_matrix_dims tac := 
    try reflexivity; 
    repeat (apply f_equal_gen; try reflexivity; 
            try (is_nat_equality; tac)).

  Ltac restore_dims_rec X :=
     match X with
  (* special cases *)
    | ?X * I _          => let X' := restore_dims_rec X in 
                          match type of X' with 
                          | M ?m' ?n' => 
                            constr:(@mmul m' n' n' X' (mat1 n'))
                          end
    | I _ * ?B          => let B' := restore_dims_rec B in 
                          match type of B' with 
                          | M ?n' ?o' => 
                            constr:(@mmul n' n' o' (mat1 n')  B')
                          end
    | ?X * @mat0 ?n ?n  => let X' := restore_dims_rec X in 
                          match type of X' with 
                          | M ?m' ?n' => 
                            constr:(@mmul m' n' n' X' (@mat0 n' n'))
                          end
    | @mat0 ?n ?n * ?B  => let B' := restore_dims_rec B in 
                          match type of B' with 
                          | M ?n' ?o' => 
                            constr:(@mmul n' n' o' (@mat0 n' n') B')
                          end
    | ?X * @mat0 ?n ?o  => let X' := restore_dims_rec X in 
                          match type of X' with 
                          | M ?m' ?n' => 
                            constr:(@mmul m' n' o X' (@mat0 n' o))
                          end
    | @mat0 ?m ?n * ?B  => let B' := restore_dims_rec B in 
                          match type of B' with 
                          | M ?n' ?o' => 
                            constr:(@mmul n' n' o' (@mat0 m n') B')
                          end
    | ?X + @mat0 ?m ?n => let X' := restore_dims_rec X in 
                          match type of X' with 
                          | M ?m' ?n' => 
                            constr:(@madd m' n' X' (@mat0 m' n'))
                          end
    | @mat0 ?m ?n + ?B => let B' := restore_dims_rec B in 
                          match type of B' with 
                          | M ?m' ?n' => 
                            constr:(@madd m' n' (@mat0 m' n') B')
                          end
  (* general cases *)
    | ?X = ?B  => let X' := restore_dims_rec X in 
                  let B' := restore_dims_rec B in 
                  match type of X' with 
                  | M ?m' ?n' => constr:(@meq m' n' X' B')
                    end
    | ?X * ?B   => let X' := restore_dims_rec X in 
                  let B' := restore_dims_rec B in 
                  match type of X' with 
                  | M ?m' ?n' =>
                    match type of B' with 
                    | M ?n'' ?o' => constr:(@mmul m' n' o' X' B')
                    end
                  end 
    | ?X + ?B => let X' := restore_dims_rec X in 
                 let B' := restore_dims_rec B in 
                 match type of X' with 
                 | M ?m' ?n' =>
                   match type of B' with 
                   | M ?m'' ?n'' => constr:(@madd m' n' X' B')
                   end
                 end
    | ?c * ?X => let X' := restore_dims_rec X in 
                 match type of X' with
                 | M ?m' ?n' => constr:(@mcmul m' n' c X')
                 end
    (* Handle functions applied to matrices *)
    | ?f ?X    => let f' := restore_dims_rec f in 
                 let X' := restore_dims_rec X in 
                 constr:(f' X')
    (* default *)
    | ?X       => X
     end.

  Ltac restore_dims tac := 
    match goal with
    | |- ?X      => let X' := restore_dims_rec X in 
                  replace X with X' by unify_matrix_dims tac
    end.

  (* 终于合成了两个可带或可不带参数的策略 *)
  Tactic Notation "restore_dims" tactic(tac) := restore_dims tac.

  Tactic Notation "restore_dims" := 
    restore_dims (try ring; unify_pows_two; simpl; lia).

  (* 数据库名称可能的解释， U_db : User database *)
  Global Hint Unfold madd mmul mcmul mat1 : U_db. 

  Hint Rewrite @mmul_1_l @mmul_1_r @mcmul_1_l @mat1_trans_eq : M_db_light.
  Hint Rewrite @mmul_0_l @mmul_0_r @madd_0_l @madd_0_r
    @mcmul_0_l @mcmul_0_r @mat0_trans_eq : M_db_light.

  (* I don't like always doing restore_dims first, but otherwise sometimes leaves 
     unsolvable WF_Matrix goals. *)
  Ltac Msimpl_light := restore_dims; autorewrite with M_db_light.

  Ltac Msimpl := restore_dims; autorewrite with M_db_light. *)
  
  
  (* ==================================== *)
  (** ** Square matrix *)
  
  Notation Square n := (M n n).

  (** Trace *)
  Definition trace {n : nat} (m : Square n) := 
    let g := mdata m in
    seqsum (fun x => g x x) n.
  
End MatrixThy.

(* Require Import FieldTypeR. *)
Module MatrixR := MatrixThy FieldR.FieldDefR.

Import FieldR.
Import MatrixR.
Open Scope R.

Definition f1 := fun i j => INR (i + j).
Definition m1 : M 2 3 := mk_mat _ _ f1.
(* Compute mrow 0 m1. *)
(* Compute mrow 1 m1. *)

Definition m10 := mat0 3 4.
(* Compute m10. *)
Definition m11 := mmap (fun x => x + R1) m10.
(* Compute m2l (m11). *)


(** Test new functions *)
Module Test.
  Import QArith Qcanon.
  Module Import MatrixQc := MatrixThy FieldQc.FieldDefQc.
  Open Scope Q.
  Open Scope Qc_scope.

  Coercion Q2Qc : Q >-> Qc.


  Definition m3 := (mk_mat_3_3 1 2 3 4 5 6 7 8 9)%Qc.
  (*   Compute trace m3. *)
  (*   Eval cbn in trace m3. *)

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : Qc.
  Definition m4 := mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.
  (*   Eval cbn in trace m4. *)
  (*   Eval cbn in (submat m4 0). *)
  (*   Eval cbn in (m2l (submat m4 3)). *)
  (*   Eval cbn in (trace (submat m4 0)). *)
  
  (*   Check m4. *)
  (*   Compute seq 0 3. *)
  (*   Compute map (fun i => (mdata m4) 0%nat i) (seq 0 3). *)
  (*   Compute map (fun i => ((mdata m4) 0%nat i, submat m4 i)) (seq 0 3). *)
  

End Test.


