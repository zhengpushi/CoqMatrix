(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Finite Function (FinFun, FF)
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
 *)


Require Export MatrixTheory.
Require Export FinFun.Matrix.


(* ######################################################################### *)
(** * Decidable Field matrix theory implemented with FinFun *)

(** Tips: EqDecidableFieldElementType is needed, to force Aeq is eq, so that 
    the matrix theory in Math-Comp could be used. *)
Module DecidableFieldMatrixTheoryFF (B : BaseType) (E : EqDecidableFieldElementType B)
<: DecidableFieldMatrixTheory E.

  Export E.

  (** Control the scope *)
  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope mat_scope.

  (* ==================================== *)
  (** ** Matrix element type *)

  Global Infix "==" := Aeq : A_scope.
  Global Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.

  (* ==================================== *)
  (** ** Matrix type and basic operations *)

  Definition mat (r c : nat) := @mat A r c.

  (* (** matrix equality *) *)
  Definition meq {r c : nat} (m1 m2 : mat r c) : Prop := m1 = m2.
  Global Infix "==" := meq : mat_scope.

  Lemma meq_equiv : forall {r c}, Equivalence (meq (r:=r) (c:=c)).
  Proof. 
    intros. apply eq_equivalence.
  Qed.

  Global Existing Instance meq_equiv.

  (** Get n-th element of a matrix *)
  Definition mnth {r c} (m : mat r c) (ri ci : nat) := @mnth A A0 r c m ri ci.

  (** meq and mnth should satisfy this constraint *)
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> (forall ri ci, ri < r -> ci < c -> (mnth m1 ri ci == mnth m2 ri ci)%A).
  Proof.
    intros. apply meq_iff_mnth.
  Qed.

  (* ==================================== *)
  (** ** Convert between list list and matrix *)

  Definition l2m {r c} (dl : list (list A)) : mat r c := @l2m A A0 r c dl.

  Definition m2l {r c} (m : mat r c) : list (list A) := @m2l A r c m.
  
  Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
  Proof.
    intros. apply m2l_length.
  Qed.

  Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
  Proof.
    intros. apply m2l_width.
  Qed.
  
  Lemma m2l_l2m_id : forall {r c} (dl : list (list A)) (H1 : length dl = r)
                       (H2 : width dl c), (@m2l r c (l2m dl) == dl)%dlist.
  Proof.
    intros.
    pose proof (m2l_l2m_id (r:=r) (c:=c)).
    specialize (H dl H1 H2). unfold m2l,l2m. rewrite H. easy.
  Qed.
  
  Lemma l2m_m2l_id : forall {r c} (m : mat r c), l2m (m2l m) == m. 
  Proof.
    intros. apply l2m_m2l_id; auto.
  Qed.
  
  Lemma l2m_inj : forall {r c} (d1 d2 : list (list A)),
      length d1 = r -> width d1 c -> 
      length d2 = r -> width d2 c -> 
      ~(d1 == d2)%dlist -> ~(@l2m r c d1 == l2m d2).
  Proof.
    intros. apply l2m_inj; auto. intro. subst. destruct H3. easy.
  Qed.
  
  Lemma l2m_surj : forall {r c} (m : mat r c), 
      (exists d, l2m d == m).
  Proof.
    intros. apply l2m_surj.
  Qed.

  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c),
      ~(m1 == m2) -> ~(m2l m1 == m2l m2)%dlist.
  Proof.
    intros. intro. apply eqlistA_eq_same_relation2 in H0.
    apply m2l_inj in H. easy.
  Qed.
  
  Lemma m2l_surj : forall {r c} (d : list (list A)), 
      length d = r -> width d c -> 
      (exists m, @m2l r c m == d)%dlist.
  Proof.
    intros.
    destruct (m2l_surj d (r:=r) (c:=c)); auto.
    exists x. apply eqlistA_eq_same_relation2. auto.
  Qed.
  
  (* ==================================== *)
  (** ** Specific matrix *)

  Definition mk_mat_1_1 (a11 : A) : mat 1 1 := mk_mat_1_1 (A0:=A0) a11.

  Definition mk_mat_3_1 (a1 a2 a3 : A) : mat 3 1 := mk_mat_3_1 (A0:=A0) a1 a2 a3.
  
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A) : mat 3 3 
    := mk_mat_3_3 (A0:=A0) a11 a12 a13 a21 a22 a23 a31 a32 a33.

  (* ==================================== *)
  (** ** Convert between tuples and matrix *)
  
  (** tuple_3x3 -> mat_3x3 *)
  Definition t2m_3x3 (t : @T_3x3 A) : mat 3 3 := t2m_3x3 (A0:=A0) t.
  
  (** mat_3x3 -> tuple_3x3 *)
  Definition m2t_3x3 (m : mat 3 3) : @T_3x3 A := m2t_3x3 (A0:=A0) m.
  
  (** m[0,0] : mat_1x1 -> A *)
  Definition scalar_of_mat (m : mat 1 1) := mnth m 0 0.

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
    intros. apply mmap2_comm. auto.
  Qed.
  
  Lemma mmap2_assoc : forall {r c} (f : A -> A -> A)
                        (f_assoc : forall a b c, (f (f a b) c == f a (f b c))%A)
                        (m1 m2 m3 : mat r c), 
      mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
  Proof.
    intros. apply mmap2_assoc. auto.
  Qed.

  
  (** Zero matrix *)
  Definition mat0 r c : mat r c := @mat0 A A0 r c.

  (** Unit matrix *)
  Definition mat1 n : mat n n := @mat1 A A0 A1 n.

  (** *** Addition of matrix *)

  (** Tips, we must write the full signature, especially the explicit parameter {r c} 
      and the return type {mat r c}, to maintain a type inference relation.
      Because only {m1 m2 : mat r c} havn't any information of {r} and {c}.
      Otherwise, the "+" notation will useless.
   *)
  Definition madd {r c} (m1 m2 : mat r c) : mat r c := @madd A Aadd r c m1 m2.
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
    mmul m1 m2. 

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

  
  (** meq is decidable *)
  Lemma meq_dec : forall (r c : nat), Decidable (meq (r:=r) (c:=c)).
  Proof.
    intros. constructor.
    intros. destruct (meq_dec a b (r:=r)(c:=c)); auto.
  Qed.
    
End DecidableFieldMatrixTheoryFF.


(** Test *)
Module Test.
  Export QArith Qcanon.
  Module Export MatrixQc :=
    DecidableFieldMatrixTheoryFF BaseTypeQc DecidableFieldElementTypeQc.
  Open Scope Q.
  Open Scope Qc.
  Open Scope mat_scope.

  Coercion Q2Qc : Q >-> Qc.
  Definition m3 := mk_mat_3_3 1 2 3 4 5 6 7 8 9.
  (* Eval cbn in mnth m3 0 0. *)

  (* crash! *)
  (* Compute mnth m3 0 0. *)
  (* Compute m2l (m3 + m3). *)

End Test.

