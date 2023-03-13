(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Function (Safe version) (Fixed Shape)
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. This is safe version of NatFun, which corrected the shape problem

  2. About determinant and inversion matrix:
  (1). There are three methods to compute the determinant,
     ref: https://zhuanlan.zhihu.com/p/435900775
     a. expand by row or column, then compute it with the algebraic remainder (代数
        余子式) 。Each expansion corresponds to a drop of one order.
        Note: expanding by rows/columns is a special case of Laplace's expansion 
        theorem.
     b. using primitive transformations (初等变换).
     c. with the help of inverse ordinal (逆序数) and permutation, i.e., by the 
        definition.
  (2). Test the performance of inversion algorithm here which is an OCaml program 
     extracted from Coq.

     Test result:
          n=8, 1.1s;  n=9, 12s;  n=10, 120s

     Main issue:
     a. observed that, the CPU usage is too high, but memory usage is low.
     b. maybe caused by the index of nat type, and I think that int type should 
        better. So, maybe we need to write an implementation in OCaml directly.
     c. another reason is that the recursion of det function is too much.

     So, we should write several version in OCaml, to check which one resulting the 
     bad performane.
     a. version1, still use NatFun, but with index of int type.
     b. version2, use array
     c. version3, use matrix (bigarray)

     New test result:
     a. version1,
        n=8, 0.25s;  n=9, 2.4s;  n=10, 32s
        I think it is still slow, maybe causing by functional style
     b. version2,
        n=8, 1s;  n=9,7s; n=10, not tested yet
        This version is slower than original one, although we have used
        array structure, why? maybe too much foo loop? I'm not sure.
 *)


Require Export MatrixTheory.
Require Sequence SafeNatFun.Matrix.
Require PermutationExt.


(* ######################################################################### *)
(** * Basic matrix theory implemented with SafeNatFun *)

Module BasicMatrixTheorySF (E : ElementType) <: BasicMatrixTheory E.

  (** Basic library *)
  Export BasicConfig TupleExt SetoidListListExt HierarchySetoid.

  Export Sequence SafeNatFun.Matrix.
  
  (* ==================================== *)
  (** ** Matrix element type *)
  Export E.

  Global Infix "==" := Aeq : A_scope.
  Global Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.

  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope mat_scope.

  (* ==================================== *)
  (** ** Matrix type and basic operations *)
  
  (** We define a _matrix_ as record which contains only one field has type of 
      nat -> nat -> A.
      Meanwhile, thare are two parameters respresenting rows and columns of 
      the matrix as parts of type of mat. *)
  Definition mat (r c : nat) := @mat A r c.

  (** Square matrix *)
  Definition smat (n : nat) := mat n n.

  (* (** matrix equality *) *)
  Definition meq {r c : nat} (m1 m2 : mat r c) : Prop := @meq A Aeq r c m1 m2.
  Global Infix "==" := meq : mat_scope.

  Lemma meq_equiv : forall {r c}, Equivalence (meq (r:=r) (c:=c)).
  Proof. 
    intros. apply meq_equiv.
  Qed.

  Global Existing Instance meq_equiv.

  (** Get n-th element of a matrix *)  
  Definition mnth {r c} (m : mat r c) (ri ci : nat) := mnth m ri ci.
  Global Notation "m ! r ! c" := (mnth m r c) : mat_scope.

  (** meq and mnth should satisfy this constraint *)
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> (forall ri ci, ri < r -> ci < c -> (m1 ! ri ! ci == m2 ! ri ! ci)%A).
  Proof.
    intros. apply meq_iff_mnth.
  Qed.
  
  (* ==================================== *)
  (** ** Convert between list list and matrix *)

  (** *** list list to mat *)
  
  Definition l2m {r c} (dl : list (list A)) : mat r c := @l2m A A0 r c dl.

  (** l2m is a proper morphism *)
  Lemma l2m_aeq_mor : forall r c, Proper (eqlistA (eqlistA Aeq) ==> meq) (@l2m r c).
  Proof.
  Admitted.

  Global Existing Instance l2m_aeq_mor.
  
  Lemma l2m_inj : forall {r c} (d1 d2 : list (list A)),
      length d1 = r -> width d1 c -> 
      length d2 = r -> width d2 c -> 
      ~(d1 == d2)%dlist -> ~(@l2m r c d1 == l2m d2).
  Proof.
    intros. apply l2m_inj; auto.
  Qed.
  
  Lemma l2m_surj : forall {r c} (m : mat r c), 
      (exists d, l2m d == m).
  Proof.
    intros. apply l2m_surj.
  Qed.

  
  (** *** mat to list list *)
  Definition m2l {r c} (m : mat r c) : list (list A) := @m2l A r c m.

  (** m2l is a proper morphism *)
  Lemma m2l_aeq_mor : forall r c, Proper (meq ==> eqlistA (eqlistA Aeq)) (@m2l r c).
  Proof.
  Admitted.

  Global Existing Instance m2l_aeq_mor.

  Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
  Proof.
    intros. apply m2l_length.
  Qed.

  Global Hint Resolve m2l_length : mat.
  
  Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
  Proof.
    intros. apply m2l_width.
  Qed.

  Global Hint Resolve m2l_width : mat.
  
  Lemma m2l_l2m_id : forall {r c} (dl : list (list A)) (H1 : length dl = r)
                            (H2 : width dl c), (@m2l r c (l2m dl) == dl)%dlist.
  Proof.
    intros. apply m2l_l2m_id; auto.
  Qed.
  
  Lemma l2m_m2l_id : forall {r c} (m : mat r c), l2m (m2l m) == m. 
  Proof.
    intros. apply l2m_m2l_id; auto.
  Qed.
  
  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c),
      ~(m1 == m2) -> ~(m2l m1 == m2l m2)%dlist.
  Proof.
    intros. apply (m2l_inj (A0:=A0)). easy.
  Qed.
  
  Lemma m2l_surj : forall {r c} (d : list (list A)), 
      length d = r -> width d c -> 
      (exists m, @m2l r c m == d)%dlist.
  Proof.
    intros. apply (m2l_surj (A0:=A0)); auto.
  Qed.
  
  (* ==================================== *)
  (** ** Specific matrix *)

  Definition mk_mat_1_1 (a00 : A) : mat 1 1 := mk_mat_1_1 (A0:=A0) a00.

  Definition mk_mat_3_1 (a00 a10 a20 : A) : mat 3 1 := mk_mat_3_1 (A0:=A0) a00 a10 a20.

  Definition mk_mat_4_1 (a00 a10 a20 a30 : A) : mat 4 1 :=
    mk_mat_4_1 (A0:=A0) a00 a10 a20 a30.

  Definition mk_mat_2_2 (a00 a01 a10 a11 : A) : mat 2 2
    := mk_mat_2_2 (A0:=A0) a00 a01 a10 a11.
  
  Definition mk_mat_3_3 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : A) : mat 3 3 
    := mk_mat_3_3 (A0:=A0) a00 a01 a02 a10 a11 a12 a20 a21 a22.

  Definition mk_mat_4_4 (a00 a01 a02 a03 a10 a11 a12 a13
                           a20 a21 a22 a23 a30 a31 a32 a33 : A) : mat 4 4 
    := mk_mat_4_4 (A0:=A0) a00 a01 a02 a03 a10 a11 a12 a13
         a20 a21 a22 a23 a30 a31 a32 a33.

  (* ==================================== *)
  (** ** Convert between tuples and matrix *)
  
  (** tuple_3x3 -> mat_3x3 *)
  Definition t2m_3x3 (t : @T_3x3 A) : mat 3 3 := t2m_3x3 (A0:=A0) t.
  
  (** mat_3x3 -> tuple_3x3 *)
  Definition m2t_3x3 (m : mat 3 3) : @T_3x3 A := m2t_3x3 m.
  
  (** m[0,0] : mat_1x1 -> A *)
  Definition scalar_of_mat (m : mat 1 1) := m ! 0 ! 0.

  (* ==================================== *)
  (** ** Matrix transposition *)
  
  Definition mtrans {r c} (m : mat r c): mat c r :=
    @mtrans A r c m.
  
  Global Notation "m \T" := (mtrans m) : mat_scope.
  
  Lemma mtrans_trans : forall {r c} (m : mat r c), mtrans (mtrans m) == m.
  Proof.
    intros. apply mtrans_trans.
  Qed.
  
  (* ==================================== *)
  (** ** Mapping of matrix *)

  (** Mapping of a matrix *)
  Definition mmap {r c} (f : A -> A) (m : mat r c) : mat r c := @mmap A r c f m.
  
  Definition mmap2 {r c} (f: A -> A -> A) (m1 m2: mat r c) : mat r c :=
    @mmap2 A r c f m1 m2.
  
  Lemma mmap2_comm : forall {r c} (f : A -> A -> A)
                            (f_comm : forall a b : A, (f a b == f b a)%A)
                            (m1 m2 : mat r c), 
      mmap2 f m1 m2 == mmap2 f m2 m1.
  Proof.
    (* lma. (* this tactic is enough too. *) *)
    intros. apply mmap2_comm. auto.
  Qed.
  
  Lemma mmap2_assoc : forall {r c} (f : A -> A -> A)
                             (f_assoc : forall a b c, (f (f a b) c == f a (f b c))%A)
                             (m1 m2 m3 : mat r c), 
      mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
  Proof.
    intros. apply mmap2_assoc. auto.
  Qed.

  (** Auto unfold these definitions *)
  Global Hint Unfold meq mmap mmap2 : mat.

  (** linear matrix arithmetic tactic for equation: split goal to every element *)
  Global Ltac lma :=
    autounfold with mat;
    Matrix.lma.

End BasicMatrixTheorySF.


(* ######################################################################### *)
(** * Decidable matrix theory implemented with SafeNatFun *)

Module DecidableMatrixTheorySF (E : DecidableElementType) <: DecidableMatrixTheory E.

  (* Export E. *)
  Include BasicMatrixTheorySF E.

  (** linear matrix arithmetic tactic for equation: split goal to every element *)

  (** meq is decidable *)
  Lemma meq_dec : forall {r c}, Decidable (meq (r:=r)(c:=c)).
  Proof.
    intros. apply @meq_dec. apply Dec_Aeq.
  Qed.

End DecidableMatrixTheorySF.


(* ######################################################################### *)
(** * Ring matrix theory implemented with SafeNatFun *)

Module RingMatrixTheorySF (E : RingElementType) <: RingMatrixTheory E.

  (* Export E. *)
  Include BasicMatrixTheorySF E.

  Add Ring ring_thy_inst : Ring_thy.

  (** Zero matrix *)
  Definition mat0 r c : mat r c := @mat0 A A0 r c.

  (** Unit matrix *)
  Definition mat1 n : mat n n := @mat1 A A0 A1 n.

  (** *** Addition of matrix *)

  Definition madd {r c} (m1 m2 : mat r c) : mat r c := madd (Aadd:=Aadd) m1 m2.
  Infix "+" := madd : mat_scope.
  
  (** m1 + m2 = m2 + m1 *)
  Lemma madd_comm : forall {r c} (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Proof.
    intros. apply madd_comm.
  Qed.
  
  (** (m1 + m2) + m3 = m1 + (m2 + m3) *)
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) + m3 == m1 + (m2 + m3).
  Proof.
    intros. apply madd_assoc.
  Qed.
  
  (** 0 + m = m *)
  Lemma madd_0_l : forall {r c} (m : mat r c), (mat0 r c) + m == m.
  Proof.
    intros. apply madd_0_l.
  Qed.
  
  (** m + 0 = m *)
  Lemma madd_0_r : forall {r c} (m : mat r c), m + (mat0 r c) == m.
  Proof.
    intros. apply madd_0_r.
  Qed.
  

  (** *** Opposite of matrix *)
  
  Definition mopp {r c} (m : mat r c) : mat r c := @mopp A Aopp r c m.
  Global Notation "- m" := (mopp m) : mat_scope.

  (** - - m = m *)
  Lemma mopp_opp : forall {r c} (m : mat r c), - - m == m.
  Proof.
    intros. apply mopp_opp.
  Qed.

  (** m + (-m) = 0 *)
  Lemma madd_opp : forall {r c} (m : mat r c), m + (-m) == mat0 r c.
  Proof.
    intros. apply madd_opp.
  Qed.
  
  
  (** *** Subtraction of matrix *)

  Definition msub {r c} (m1 m2 : mat r c) : mat r c := @msub A Aadd Aopp r c m1 m2.
  Infix "-" := msub : mat_scope.

  (** m1 - m2 = - (m2 - m1) *)
  Lemma msub_comm : forall {r c} (m1 m2 : mat r c), m1 - m2 == - (m2 - m1).
  Proof.
    intros. apply msub_comm.
  Qed.
  (** (m1 - m2) - m3 = m1 - (m2 + m3) *)
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 - m2) - m3 == m1 - (m2 + m3).
  Proof.
    intros. apply msub_assoc.
  Qed.

  (** 0 - m = - m *)
  Lemma msub_0_l : forall {r c} (m : mat r c), (mat0 r c) - m == - m.
  Proof.
    intros. apply msub_0_l.
  Qed.
  
  (** m - 0 = m *)
  Lemma msub_0_r : forall {r c} (m : mat r c), m - (mat0 r c) == m.
  Proof.
    intros. apply msub_0_r.
  Qed.
  
  (** m - m = 0 *)
  Lemma msub_self : forall {r c} (m : mat r c), m - m == (mat0 r c).
  Proof.
    intros. apply msub_self.
  Qed.

  
  (** *** Scalar multiplication of matrix *)
  
  (** Left scalar multiplication of matrix *)
  Definition mcmul {r c} (a : A) (m : mat r c) : mat r c :=
    @mcmul A Amul r c a m.
  Notation "a c* m" := (mcmul a m) : mat_scope.

  (** Right scalar multiplication of matrix *)
  Definition mmulc {r c} (m : mat r c) (a : A) : mat r c :=
    @mmulc A Amul r c m a.
  Notation "m *c a" := (mmulc m a) : mat_scope.
  
  (** m *c a = a c* m *)
  Lemma mmulc_eq_mcmul : forall {r c} (a : A) (m : mat r c), m *c a == a c* m.
  Proof.
    intros. apply mmulc_eq_mcmul.
  Qed.
  
  (** a * (b * m) = (a * b) * m *)
  Lemma mcmul_assoc : forall {r c} (a b : A) (m : mat r c), a c* (b c* m) == (a * b)%A c* m.
  Proof.
    intros. apply mcmul_assoc.
  Qed.
  
  (** a * (b * m) = b * (a * m) *)
  Lemma mcmul_perm : forall {r c} (a b : A) (m : mat r c), a c* (b c* m) == b c* (a c* m).
  Proof.
    intros. apply mcmul_perm.
  Qed.
  
  (** a * (m1 + m2) = (a * m1) + (a * m2) *)
  Lemma mcmul_add_distr_l : forall {r c} (a : A) (m1 m2 : mat r c),
      a c* (m1 + m2) == (a c* m1) + (a c* m2).
  Proof.
    intros. apply mcmul_add_distr_l.
  Qed.
  
  (** (a + b) * m = (a * m) + (b * m) *)
  Lemma mcmul_add_distr_r : forall {r c} (a b : A) (m : mat r c),
      (a + b)%A c* m == (a c* m) + (b c* m).
  Proof.
    intros. apply mcmul_add_distr_r.
  Qed.
  
  (** 0 * m = 0 *)
  Lemma mcmul_0_l : forall {r c} (m : mat r c), A0 c* m == mat0 r c.
  Proof.
    intros. apply mcmul_0_l.
  Qed.
  
  (** 1 * m = m *)
  Lemma mcmul_1_l : forall {r c} (m : mat r c), A1 c* m == m.
  Proof.
    intros. apply mcmul_1_l.
  Qed.


  (** *** Multiplication of matrix *)
  
  Definition mmul {r c s} (m1 : mat r c) (m2 : mat c s) : mat r s :=
    @mmul A Aadd A0 Amul r c s m1 m2.

  Global Infix "*" := mmul : mat_scope.
  
  (** m1 * (m2 + m3) = (m1 * m2) + (m1 * m3) *)
  Lemma mmul_add_distr_l : forall {r c s} (m1 : mat r c) (m2 m3 : mat c s),
      m1 * (@madd c s m2 m3) == @madd r s (m1 * m2) (m1 * m3).
  Proof.
    intros. apply mmul_add_distr_l.
  Qed.
  
  (** (m1 + m2) * m3 = (m1 * m3) + (m2 * m3) *)
  Lemma mmul_add_distr_r : forall {r c s} (m1 m2 : mat r c) (m3 : mat c s),
      (@madd r c m1 m2) * m3 == @madd r s (m1 * m3) (m2 * m3).
  Proof.
    intros. apply mmul_add_distr_r.
  Qed.
  
  (** (m1 * m2) * m3 = m1 * (m2 * m3) *)
  Lemma mmul_assoc : forall {r c s t} (m1 : mat r c) (m2 : mat c s) (m3 : mat s t),
      (m1 * m2) * m3 == m1 * (m2 * m3).
  Proof.
    intros. apply mmul_assoc.
  Qed.
  
  (** mat0 * m = mat0 *)
  Lemma mmul_0_l : forall {r c s} (m : mat c s), (mat0 r c) * m == mat0 r s.
  Proof.
    intros. apply mmul_0_l.
  Qed.
  
  (** m * mat0 = mat0 *)
  Lemma mmul_0_r : forall {r c s} (m : mat r c), m * (mat0 c s) == mat0 r s.
  Proof.
    intros. apply mmul_0_r.
  Qed.
  
  (** mat1 * m = m *)
  Lemma mmul_1_l : forall {r c} (m : mat r c), (mat1 r) * m == m.
  Proof.
    intros. apply mmul_1_l.
  Qed.
  
  (** m * mat1 = m *)
  Lemma mmul_1_r : forall {r c} (m : mat r c), m * (mat1 c) == m.
  Proof.
    intros. apply mmul_1_r.
  Qed.
  
  (** Auto unfold these definitions *)
  Global Hint Unfold madd mopp msub mcmul mmul : mat.

  (** ** Extended matrix theory *)

  (** Trace of a square matrix *)
  Definition trace {n : nat} (m : smat n) :=
    seqsum (A0:=A0) (Aadd:=Aadd) (fun i => m!i!i) n.
  
  (** Determinant of 3x3 matrix *)
  Definition det3 (m : mat 3 3) : A :=
    (let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) := m2t_3x3 m in
     let b1 := (a11 * a22 * a33) in
     let b2 := (a12 * a23 * a31) in
     let b3 := (a13 * a21 * a32) in
     let c1 := (a11 * a23 * a32) in
     let c2 := (a12 * a21 * a33) in
     let c3 := (a13 * a22 * a31) in
     let b := (b1 + b2 + b3) in
     let c := (c1 + c2 + c3) in
     (b - c))%A.

End RingMatrixTheorySF.


(* ######################################################################### *)
(** * Decidable Field matrix theory implemented with SafeNatFun *)

Module DecidableFieldMatrixTheorySF (E : DecidableFieldElementType)
<: DecidableFieldMatrixTheory E.

  (* Export E. *)
  Include RingMatrixTheorySF E.

  Add Field field_inst : make_field_theory.

  Import PermutationExt.

  (** meq is decidable *)
  Lemma meq_dec : forall (r c : nat), Decidable (meq (r:=r) (c:=c)).
  Proof.
    intros. apply meq_dec.
  Qed.
  
  (** ** matrix theory *)
  Section Inversion.

    (* ======================================================================= *)
    (** ** Determinant. *)

    (** Get the sub square matrix which remove r-th row and c-th column
        from a square matrix. *)
    Definition submat {n} (m : smat (S n)) (r c : nat) : smat n :=
      mk_mat
        (fun i j =>
           let i' := (if ltb i r then i else S i) in
           let j' := (if ltb j c then j else S j) in
           m!i'!j').

    (** Determinant of a square matrix (original definition) *)
    (* Variable a b c : A. *)
    (* Compute perm 0 (seq 0 3). *)
    (* Let dl := perm 0 (seq 0 3). *)
    (* Let l := [1;2;3]. *)
    (* Compute nth 1 l 0. *)
    (* Compute map (fun i => (i, nth i l 0)) (seq 0 3). *)
    (* Compute map (fun l => map (fun i => (i, nth i l 0)) (seq 0 3)) dl. *)
    (* Let dl1 := map (fun l => map (fun i => (i, nth i l 0)) (seq 0 3)) dl. *)
    (* Variable a00 a01 a02 a10 a11 a12 a20 a21 a22 : A. *)
    (* Definition m : smat 3 := mk_mat_3_3 a00 a01 a02 a10 a11 a12 a20 a21 a22. *)
    (* Compute map (fun l => map (fun (ij:nat * nat) => let (i,j) := ij in m!i!j) l) dl1. *)

    (* (** all items in a determinant *) *)
    (* Let dl2 := map (fun l => map (fun (ij:nat * nat) => let (i,j) := ij in m!i!j) l) dl1. *)
    (* Compute dl2. *)

    (* Definition n := 3. *)
    (* Compute perm 0 (seq 0 n). (* *)
    (*  = [[0; 1; 2]; [0; 2; 1]; [1; 0; 2]; [1; 2; 0]; [2; 0; 1]; [2; 1; 0]] *)
    (*  : list (list nat) *) *)

    (* Definition item_of_det {n : nat} (m : smat n) (l : list nat) : A := *)
    (*   fold_left Amul (map (fun i => m!i!(nth i l 0)) l) A1. *)

    (* (** Definition of determinant *) *)
    (* Definition det_def {n : nat} (m : smat n) : A := *)
    (*   fold_left Aadd (map (fun l => item_of_det m l) (perm 0 (seq 0 n))) A0. *)

    (* Compute det_orig m. *)
    
    (* Compute fold_left Amul [a00;a01;a02]. *)
    (* Compute fold_left Aadd. *)

    (* Check perm. ? *)
    (* Fixpoint det_orig {n} : smat n -> A := *)
    (*   match n with *)
    (*   | 0 => fun _ => A1 *)
    (*   | S n' => *)
    (*       fun m => *)
      
    (** Determinant of a square matrix.
        The idea: by expanding the first row *)
    Fixpoint det {n} : smat n -> A :=
      match n with
      | 0 => fun _ => A1
      | S n' =>
          fun m =>
            fold_left Aadd
              (map (fun i =>
                      let a := if Nat.even i then (m!0!i)%nat else (-(m!0!i)%nat)%A in
                      let d := det (submat m 0 i) in
                      (a * d)%A) (seq 0 n)) A0
      end.

    (** Prove a proposition such as:
      "~(det m == 0) -> ~(xxx = 0)"
      or
      "~(xxx = 0) -> ~(det m == 0)"
     *)
    Ltac det_neq0_imply_neq0 :=
      match goal with
      | H : ~(det ?m == A0)%A |- ~(_ == A0)%A =>
          let H1 := fresh "H1" in
          intro H1; destruct H; cbv; ring_simplify; ring_simplify in H1; auto
      | H : ~(_ == A0)%A |- ~(det ?m == A0)%A =>
          let H1 := fresh "H1" in
          intro H1; cbv in H1; destruct H; ring_simplify; ring_simplify in H1; auto
      end.

    (** Determinant of a matrix of dimension-1 *)
    Definition det_1_1 (m : smat 1) := m!0!0.

    (** det_1_1 m = det m *)
    Lemma det_1_1_eq_det : forall m, (det_1_1 m == det m)%A.
    Proof.
      intros. cbv. ring.
    Qed.
    
    (** det m <> 0 <-> det_exp <> 0 *)
    Lemma det_1_1_neq0_iff : forall (m : smat 1),
        ~ (det m == A0)%A <->  ~ (m!0!0 == A0)%A.
    Proof.
      intros. split; intros; det_neq0_imply_neq0.
    Qed.

    (** Determinant of a matrix of dimension-2 *)
    Definition det_2_2 (m : smat 2) := (m!0!0 * m!1!1 - m!0!1 * m!1!0)%A.

    (** det_2_2 m = det m *)
    Lemma det_2_2_eq_det : forall m, (det_2_2 m == det m)%A.
    Proof.
      intros. cbv. ring.
    Qed.

    (** det m <> 0 <-> det_exp <> 0 *)
    Lemma det_2_2_neq0_iff : forall (m : smat 2),
        ~ (det m == A0)%A <->  ~ (m!0!0 * m!1!1 - m!0!1 * m!1!0 == A0)%A.
    Proof.
      intros. split; intros; det_neq0_imply_neq0.
    Qed.

    (** Determinant of a matrix of dimension-3 *)
    Definition det_3_3 (m : smat 3) :=
      (m!0!0 * m!1!1 * m!2!2 - m!0!0 * m!1!2 * m!2!1 - 
         m!0!1 * m!1!0 * m!2!2 + m!0!1 * m!1!2 * m!2!0 + 
         m!0!2 * m!1!0 * m!2!1 - m!0!2 * m!1!1 * m!2!0)%A.

    (** det_3_3 m = det m *)
    Lemma det_3_3_eq_det : forall m, (det_3_3 m == det m)%A.
    Proof.
      intros. cbv. ring.
    Qed.
    
    (** det m <> 0 <-> det_exp <> 0 *)
    Lemma det_3_3_neq0_iff : forall (m : smat 3),
        ~ (det m == A0)%A <->
          ~(m!0!0 * m!1!1 * m!2!2 - m!0!0 * m!1!2 * m!2!1 - 
              m!0!1 * m!1!0 * m!2!2 + m!0!1 * m!1!2 * m!2!0 + 
              m!0!2 * m!1!0 * m!2!1 - m!0!2 * m!1!1 * m!2!0 == A0)%A.
    Proof.
      intros. split; intros; det_neq0_imply_neq0.
    Qed.

    (* ======================================================================= *)
    (** ** Cramer rule *)
    
    (** Exchange one column of a square matrix *)
    Definition mchgcol {n} (m : smat n) (k : nat) (v : mat n 1) : smat n :=
      mk_mat (fun i j => if (Nat.eqb j k) then (v!i!0)%nat else m!i!j).
    
    (** Cramer rule, which can slving the equation with form of A*x=b.
      Note, the result is valid on when D is not zero *)
    Definition cramerRule {n} (A : smat n) (b : mat n 1) : mat n 1 :=
      let D := det A in
      mk_mat (fun i j => let Di := det (mchgcol A i b) in Di / D).
    
    (* ======================================================================= *)
    (** ** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
    (** That is: adj(A)[i,j] = algebraic remainder of A[j,i]. *)
    
    Definition madj {n} : smat n -> smat n := 
      match n with
      | O => fun m => m 
      | S n' =>
          fun m =>
            mk_mat (fun i j =>
                      let s := if Nat.even (i + j) then A1 else (-A1)%A in
                      let d := det (submat m j i) in 
                      (s * d)%A)
      end.
    
    (* ======================================================================= *)
    (** ** Inversion matrix of a matrix *)
    Definition minv {n} (m : smat n) := (A1/det m) c* (madj m).

    Lemma minv_correct_r : forall n (m : smat n), m * (minv m) == mat1 n.
    Proof.
      induction n; intros.
      - lma.
      (* - unfold minv in *. *)
        Abort.

    
    
    (* ======================================================================= *)
    (** ** Inversion matrix of dimension-1 *)
    Definition inv_1_1 (m : smat 1) : smat 1 := l2m [[A1/(m!0!0)]].

    (** det m <> 0 -> inv_1_1 m = inv m *)
    Lemma inv_1_1_eq_inv : forall m, ~(det m == A0)%A -> inv_1_1 m == minv m.
    Proof.
      lma. det_neq0_imply_neq0.
    Qed.

    (** inv_1_1 m * m = mat1 *)
    Lemma inv_1_1_correct_l : forall (m : smat 1),
        ~(det m == A0)%A -> (inv_1_1 m) * m == mat1 1.
    Proof.
      lma. det_neq0_imply_neq0.
    Qed.

    (** m * inv_1_1 m = mat1 *)
    Lemma inv_1_1_correct_r : forall (m : smat 1),
        ~(det m == A0)%A -> m * (inv_1_1 m) == mat1 1.
    Proof.
      lma. det_neq0_imply_neq0.
    Qed.

    (* ======================================================================= *)
    (** ** Inversion matrix of dimension-2 *)
    Definition inv_2_2 (m : smat 2) : smat 2 :=
      let a00 := m!0!0 in
      let a01 := m!0!1 in
      let a10 := m!1!0 in
      let a11 := m!1!1 in
      let d := det_2_2 m in
      (l2m [[a11/d; -a01/d]; [-a10/d; a00/d]])%A.

    (** det m <> 0 -> inv_2_2 m = inv m *)
    Lemma inv_2_2_eq_inv : forall m, ~(det m == A0)%A -> inv_2_2 m == minv m.
    Proof.
      lma; det_neq0_imply_neq0.
    Qed.
    
    (** inv_2_2 m * m = mat1 *)
    Lemma inv_2_2_correct_l : forall (m : smat 2),
        ~(det m == A0)%A -> (inv_2_2 m) * m == mat1 2.
    Proof.
      lma; det_neq0_imply_neq0.
    Qed.
    
    (** m * inv_2_2 m = mat1 *)
    Lemma inv_2_2_correct_r : forall (m : smat 2),
        ~(det m == A0)%A -> m * (inv_2_2 m) == mat1 2.
    Proof.
      lma; det_neq0_imply_neq0.
    Qed.
    
    (* ======================================================================= *)
    (** ** Inversion matrix of dimension-3 *)
    (* Note, this formula could be provided from matlab, thus avoiding manual work *)
    Definition inv_3_3 (m : smat 3) : smat 3 :=
      let a00 := m!0!0 in
      let a01 := m!0!1 in
      let a02 := m!0!2 in
      let a10 := m!1!0 in
      let a11 := m!1!1 in
      let a12 := m!1!2 in
      let a20 := m!2!0 in
      let a21 := m!2!1 in
      let a22 := m!2!2 in
      let d := det_3_3 m in
      (l2m
         [[(a11*a22 - a12*a21)/d; -(a01*a22 - a02*a21)/d; (a01*a12 - a02*a11)/d];
          [-(a10*a22 - a12*a20)/d; (a00*a22 - a02*a20)/d; -(a00*a12 - a02*a10)/d];
          [(a10*a21 - a11*a20)/d; -(a00*a21 - a01*a20)/d; (a00*a11 - a01*a10)/d]])%A.
    
    (** det m <> 0 -> inv_3_3 m = inv m *)
    Lemma inv_3_3_eq_inv : forall m, ~(det m == A0)%A -> inv_3_3 m == minv m.
    Proof.
      lma; det_neq0_imply_neq0.
    Qed.
    
    (** inv_3_3 m * m = mat1 *)
    Lemma inv_3_3_correct_l : forall (m : smat 3),
        ~(det m == A0)%A -> (inv_3_3 m) * m == mat1 3.
    Proof.
      lma; det_neq0_imply_neq0.
    Qed.
    
    (** m * inv_3_3 m = mat1 *)
    Lemma inv_3_3_correct_r : forall (m : smat 3),
        ~(det m == A0)%A -> m * (inv_3_3 m) == mat1 3.
    Proof.
      lma; det_neq0_imply_neq0.
    Qed.
    
    (* ======================================================================= *)
    (** ** Direct compute inversion of a symbol matrix of 1/2/3rd order. *)
    Section FindFormula.
      Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.
      Let m1 := mk_mat_1_1 a11.
      Let m2 := mk_mat_2_2 a11 a12 a21 a22.
      Let m3 := mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.

      (* Compute (m2l (minv m1)). *)
      (* Compute (m2l (minv m2)). *)
      (* Compute (m2l (minv m3)). *)
      (* Although this is correct, but the expression is too long. *)
      (* We want to simplify it with RAST *)
      
    End FindFormula.

  End Inversion.
  
End DecidableFieldMatrixTheorySF.


(** Test *)
Module Test.
  Module Export MatrixQ := DecidableFieldMatrixTheorySF DecidableFieldElementTypeQ.
  Open Scope Q.
  Open Scope mat_scope.

  Example m3 := mk_mat_3_3 1 2 3 4 5 6 7 8 9.
  (* Compute m2l (m3 + m3). *)
  (* Compute m2l (m3 * m3). *)

  (* Compute m2l (minv m3). *)
  Example m4 := mk_mat_3_3 1 2 3 4 5 7 6 8 9.
  (* Compute m2l (minv m4). *)
  (* Compute (m2l (m4 * (minv m4))). *)

  Module Export MatrixR := DecidableFieldMatrixTheorySF DecidableFieldElementTypeR.
  Open Scope R.
  Open Scope mat_scope.

  Variable a b c d : R.
  (* Eval cbv in m2l (inv_2_2 (mk_mat_2_2 a b c d)). *)
  (* Eval cbv in m2l (minv (mk_mat_2_2 a b c d)). *)

End Test.


