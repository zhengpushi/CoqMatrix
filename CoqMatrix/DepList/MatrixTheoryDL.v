(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose:    Matrix implemented with Inductive List
  author:     ZhengPu Shi
  date:       2021.12
  
  remark:
  1. use Coq.Vectors.Vector 
*)


Require Export MatrixTheory.
Require Import DepList.Matrix.


(* ######################################################################### *)
(** * Basic matrix theory implemented with Dependent List *)
Module BasicMatrixTheoryDL (E : ElementType) <: BasicMatrixTheory E.

  (** Basic library *)
  Export BasicConfig TupleExt SetoidListListExt HierarchySetoid.

  (** Vector and List usually conflicted with same name and same notations *)
  Export List ListNotations.
  Export Vector VectorNotations.

  (* ==================================== *)
  (** ** Matrix element type *)
  Export E.

  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.

  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope list_scope.
  Open Scope dlist_scope.
  Open Scope vector_scope.
  Open Scope mat_scope.

  (* ==================================== *)
  (** ** Matrix type and basic operations *)

  Definition mat r c := @mat A r c.

  (** matrix equality *)
  Definition meq {r c : nat} := @meq A Aeq r c.
  Infix "==" := meq : mat_scope.

  Lemma meq_equiv r c : Equivalence (@meq r c).
  Proof.
    apply meq_equiv.
  Qed.
  Global Existing Instance meq_equiv.
  
  (** Get n-th element of a matrix *)  
  Definition mnth {r c} (m : mat r c) (ri ci : nat) :=
    mnthNat m ri ci (A0:=A0).
  Notation "m @ i # j" := (mnth m i j).

  (** meq and mnth should satisfy this constraint *)
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
    m1 == m2 <-> (forall ri ci, ri < r -> ci < c -> (m1@ri#ci == m2@ri#ci)%A).
  Proof.
    intros. apply meq_iff_mnthNat.
  Qed.

  (** linear matrix arithmetic tactic for equation: split goal to every element *)
  Ltac lma :=
    cbv; repeat constructor;
    try ring; try easy.
  
  (* ==================================== *)
  (** ** Convert between list list and matrix *)

  (** *** list list to mat *)
  
  Definition l2m {r c} (dl : list (list A)) : mat r c := l2m A0 dl r c.

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
  
  Definition m2l {r c} (m : mat r c) : list (list A) := m2l m.

  (** m2l is a proper morphism *)
  Lemma m2l_aeq_mor : forall r c, Proper (meq ==> eqlistA (eqlistA Aeq)) (@m2l r c).
  Proof.
    Admitted.

  Global Existing Instance m2l_aeq_mor.
    
  Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
  Proof.
    intros. induction m; simpl in *; auto.
  Qed.
  Global Hint Resolve m2l_length : mat.
  
  Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
  Proof.
    intros. unfold m2l. induction m; simpl; auto; constructor; auto.
    apply v2l_length.
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
    intros. apply m2l_inj. auto.
  Qed.
  
  Lemma m2l_surj : forall {r c} (d : list (list A)), 
    length d = r -> width d c -> 
    (exists m, @m2l r c m == d)%dlist.
  Proof.
    intros. apply (m2l_surj (A0:=A0)); auto.
  Qed.
  
  
  (* ==================================== *)
  (** ** Specific matrix *)
  
  Definition mk_mat_1_1 (a11 : A) : mat 1 1 := [[a11]].
  Definition mk_mat_3_1 (a1 a2 a3 : A) : mat 3 1 
    := [[a1];[a2];[a3]].
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A) : mat 3 3 
    := [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  Definition mk_mat_2_2 (a11 a12 a21 a22 : A) : mat 2 2
    := [[a11;a12];[a21;a22]].


  (* ==================================== *)
  (** ** Convert between tuples and matrix *)
  
  (** tuple_3x3 -> mat_3x3 *)
  Definition t2m_3x3 (t : @T_3x3 A) : mat 3 3.
  Proof.
    destruct t as ((t1,t2),t3).
    destruct t1 as ((a11,a12),a13).
    destruct t2 as ((a21,a22),a23).
    destruct t3 as ((a31,a32),a33).
    exact (mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33).
  Defined.
  
  (** mat_3x3 -> tuple_3x3 *)
  Definition m2t_3x3 (m : mat 3 3) : @T_3x3 A.
    set (l1 := hd m).
    set (l2 := hd (tl m)).
    set (l3 := hd (tl (tl m))).
    set (t1 := (hd l1, hd (tl l1), hd (tl (tl l1)))).
    set (t2 := (hd l2, hd (tl l2), hd (tl (tl l2)))).
    set (t3 := (hd l3, hd (tl l3), hd (tl (tl l3)))).
    exact (t1, t2, t3).
  Defined.
  
  (** mat_1x2 -> A *)
  Definition scalar_of_mat (m : mat 1 1) := mnth m 0 0.

  
  (* ==================================== *)
  (** ** Matrix transposition *)

  Definition mtrans {r c} (m : mat r c): mat c r :=
    @mtrans A r c m.
  
  Notation "m \T" := (mtrans m) : mat_scope.
  
  Lemma mtrans_trans : forall {r c} (m : mat r c), mtrans (mtrans m) == m.
  Proof.
    apply @mtrans_trans. apply Equiv_Aeq.
  Qed.
  

  (* ==================================== *)
  (** ** Mapping of matrix *)

  (** Mapping of a matrix *)
  Definition mmap {r c} (f : A -> A) (m : mat r c) : mat r c := mmap m f.

  (** Mapping of two matrices *)
  Definition mmap2 {r c} (f : A -> A -> A) (m1  m2 : mat r c) : mat r c :=
    mmap2 f m1 m2.
 
  Lemma mmap2_comm : forall {r c} (f : A -> A -> A)
    (f_comm : forall a b : A, (f a b == f b a)%A) (m1 m2 : mat r c), 
    mmap2 f m1 m2 == mmap2 f m2 m1.
  Proof.
    intros. apply @mmap2_comm. apply Equiv_Aeq. constructor; auto.
  Qed.
  
  Lemma mmap2_assoc : forall {r c} (f : A -> A -> A)
    (f_assoc : forall a b c, (f (f a b) c == f a (f b c))%A) (m1 m2 m3 : mat r c), 
    mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
  Proof.
    intros. apply @mmap2_assoc. apply Equiv_Aeq. constructor; auto.
  Qed.

End BasicMatrixTheoryDL.


(* ######################################################################### *)
(** * Decidable matrix theory implemented with Dependent List *)

Module DecidableMatrixTheoryDL (E : DecidableElementType) <: DecidableMatrixTheory E.

  (* Export E. *)
  Include BasicMatrixTheoryDL E.

  (** the equality of two matrices is decidable *)
  Lemma meq_dec : forall {r c}, Decidable (meq (r:=r) (c:=c)).
  Proof.
    intros. apply meq_dec. apply Dec_Aeq.
  Qed.

End DecidableMatrixTheoryDL.


(* ######################################################################### *)
(** * Ring matrix theory implemented with Dependent List *)

Module RingMatrixTheoryDL (E : RingElementType) <: RingMatrixTheory E.

  (* Export E. *)
  Include BasicMatrixTheoryDL E.

  Add Ring ring_thy_inst : Ring_thy.

  (** Zero matrix *)
  Definition mat0 r c : mat r c := mat0 r c (A0:=A0).

  (** Unit matrix *)
  Definition mat1 n : mat n n := mat1 n (A0:=A0)(A1:=A1).

  (** *** Addition of matrix *)
  Definition madd {r c} := @madd A Aadd r c.
  Global Infix "+" := madd : mat_scope.

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
  Definition mopp {r c} (m : mat r c) : mat r c :=
    @mopp A Aopp r c m.
  Global Notation "- m" := (mopp m) : mat_scope.

  (** - - m = m *)
  Lemma mopp_opp : forall {r c} (m : mat r c), - - m == m.
  Proof.
    intros. apply mopp_mopp.
  Qed.

  (** m + (-m) = 0 *)
  Lemma madd_opp : forall {r c} (m : mat r c), m + (-m) == mat0 r c.
  Proof.
    intros. apply madd_mopp.
  Qed.
  

  (** *** Subtraction of matrix *)
  Definition msub {r c} (m1 m2 : mat r c) : mat r c :=
    @msub A Aadd Aopp r c m1 m2.
  Global Infix "-" := msub : mat_scope.

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
  
  (** Right scalar multiplication of matrix *)
  Definition mmulc {r c} (m : mat r c) (a : A) : mat r c :=
    @mmulc A Amul r c m a.
  
  Global Notation "a c* m" := (mcmul a m) : mat_scope.
  Global Notation "m *c a" := (mmulc m a) : mat_scope.

  (** m * a = a * m *)
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
    intros. apply mcmul_distr_l.
  Qed.
  
  (** (a + b) * m = (a * m) + (b * m) *)
  Lemma mcmul_add_distr_r : forall {r c} (a b : A) (m : mat r c),
      (a + b)%A c* m == (a c* m) + (b c* m).
  Proof.
    intros. apply mcmul_distr_r.
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
  Lemma mmul_add_distr_l : forall {r c A} (m1 : mat r c) (m2 m3 : mat c A),
    m1 * (m2 + m3) == m1 * m2 + m1 * m3.
  Proof.
    intros. apply mmul_madd_distr_l.
  Qed.
  
  (** (m1 + m2) * m3 = (m1 * m3) + (m2 * m3) *)
  Lemma mmul_add_distr_r : forall {r c s} (m1 m2 : mat r c) (m3 : mat c s),
    (m1 + m2) * m3 == (m1 * m3) + (m2 * m3).
  Proof.
    intros. apply mmul_madd_distr_r.
  Qed.

  (** (m1 * m2) * m3 = m1 * (m2 * m3) *)
  Lemma mmul_assoc : forall {r c s A} (m1 : mat r c) (m2 : mat c s) (m3 : mat s A),
    (m1 * m2) * m3 == m1 * (m2 * m3).
  Proof.
    intros. apply mmul_assoc.
  Qed.

  (** mat0 * m = mat0 *)
  Lemma mmul_0_l : forall {r c A} (m : mat c A), (mat0 r c) * m == mat0 r A.
  Proof.
    intros. apply mmul_0_l.
  Qed.

  (** m * mat0 = mat0 *)
  Lemma mmul_0_r : forall {r c A} (m : mat r c), m * (mat0 c A) == mat0 r A.
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
  
End RingMatrixTheoryDL.



(* ######################################################################### *)
(** * Decidable Field matrix theory implemented with Dependent List *)

Module DecidableFieldMatrixTheoryDL (E : DecidableFieldElementType)
<: DecidableFieldMatrixTheory E.

  (* Export E. *)
  Include RingMatrixTheoryDL E.
  Module Export DecMT := DecidableMatrixTheoryDL E.

  (** meq is decidable *)
  Lemma meq_dec : forall (r c : nat), Decidable (meq (r:=r) (c:=c)).
  Proof.
    intros. apply meq_dec.
  Qed.
    
  (** ** matrix theory *)

  (** k * m = 0 -> (m = 0) \/ (k = 0) *)
  Lemma mcmul_eq0_imply_m0_or_k0 : forall {r c} (m : mat r c) k,
      let m0 := mat0 r c in
      (k c* m == m0) -> (m == m0) \/ (k == A0)%A.
  Proof.
    intros.
    (* apply mcmul_eq0_imply_m0_or_k0. auto. Qed. *)
  Admitted.


  (** (m <> 0 \/ k * m = 0) -> k = 0 *)
  Lemma mcmul_mnonzero_eq0_imply_k0 : forall {r c} (m : mat r c) k,
      let m0 := mat0 r c in
      ~(m == m0) -> k c* m == m0 -> (k == A0)%A.
  Proof.
    intros.
    (* apply mcmul_mnonzero_eq0_imply_k0 with (m:=m); auto. Qed. *)
  Admitted.

  (** k * m = m -> k = 1 \/ m = 0 *)
  Lemma mcmul_same_imply_coef1_or_mzero : forall {r c} k (m : mat r c),
      k c* m == m -> (k == A1)%A \/ (m == mat0 r c).
  Proof.
    intros.
    (* apply mcmul_same_imply_coef1_or_mzero. auto. Qed. *)
  Admitted.

  (** (m1 <> 0 /\ m2 <> 0 /\ k * m1 = m2) -> k <> 0 *)
  Lemma mcmul_eq_mat_implfy_not_k0 : forall {r c} (m1 m2 : mat r c) k,
      let m0 := mat0 r c in
      ~(m1 == m0) -> ~(m2 == m0) -> k c* m1 == m2 -> ~(k == A0)%A.
  Proof.
    intros.
    (* apply mcmul_eq_mat_implfy_not_k0 with m1 m2; auto. Qed. *)
  Admitted.

End DecidableFieldMatrixTheoryDL.


(** * Extra Properties *)
Module ExtraMatrixTheoryDL (E : DecidableFieldElementType).
  
  (* Export E. *)
  Include (DecidableFieldMatrixTheoryDL E).

  (** ** Other OPs and PROPs *)
  
  (** get / set an element of a matrix *)
  Definition mget := @mget A.
  Definition mset := @mset A.

End ExtraMatrixTheoryDL.
