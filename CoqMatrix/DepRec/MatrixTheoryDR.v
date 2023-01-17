(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory with Dependent Record
  author    : ZhengPu Shi
  date      : 2021.12
*)


Require Export MatrixTheory.
Require Import DepRec.Matrix.


(* ######################################################################### *)
(** * Basic matrix theory implemented with Dependent Record *)

Module BasicMatrixTheoryDR (E : ElementType) <: BasicMatrixTheory E.

  (* ==================================== *)
  (** ** Matrix element type *)
  Export E.

  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.

  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope list_scope.
  Open Scope dlist_scope.
  Open Scope mat_scope.

  (* ==================================== *)
  (** ** Matrix type and basic operations *)

  Definition mat r c := @mat A r c.

  (** matrix equality *)
  Definition meq {r c : nat} := @meq A Aeq r c.
  Infix "==" := meq : mat_scope.

  Lemma meq_equiv r c : Equivalence (@meq r c).
  Proof.
    apply Equiv_meq.
  Qed.

  Global Existing Instance meq_equiv.
  
  (** Get n-th element of a matrix *)  
  Definition mnth {r c} (m : mat r c) (ri ci : nat) :=
    @mnth A A0 r c m ri ci.
  Notation "m @ i # j" := (mnth m i j).
  
  (** meq and mnth should satisfy this constraint *)
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
    m1 == m2 <-> (forall ri ci, ri < r -> ci < c -> (m1@ri#ci == m2@ri#ci)%A).
  Proof.
    intros. apply meq_iff_mnth. apply Equiv_Aeq.
  Qed.

  (* ==================================== *)
  (** ** Convert between list list and matrix *)

  (** *** list list to mat *)
  
  (* Tips: we can design the needed sequence of parameters, and it maybe different 
     with the original implementation *)
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
    apply l2m_inj.
  Qed.
  
  Lemma l2m_surj : forall {r c} (m : mat r c), (exists d, l2m d == m).
  Proof.
    apply l2m_surj.
  Qed.


  (** *** mat to list list *)
  
  Definition m2l {r c} (m : mat r c) : list (list A) := mdata m.

  (** m2l is a proper morphism *)
  Lemma m2l_aeq_mor : forall r c, Proper (meq ==> eqlistA (eqlistA Aeq)) (@m2l r c).
  Proof.
    Admitted.

  Global Existing Instance m2l_aeq_mor.

  Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
  Proof.
    intros. destruct m. simpl. auto.
  Qed.
  Global Hint Resolve m2l_length : mat.
  
  Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
  Proof.
    intros. destruct m. simpl. auto.
  Qed.
  Global Hint Resolve m2l_width : mat.

  Lemma m2l_l2m_id : forall {r c} (dl : list (list A)) (H1 : length dl = r)
    (H2 : width dl c), (@m2l r c (l2m dl) == dl)%dlist.
  Proof.
    intros. unfold m2l,l2m. unfold Matrix.l2m. simpl.
    apply l2m_aux_eq; auto.
  Qed.
  
  Lemma l2m_m2l_id : forall {r c} (m : mat r c), l2m (m2l m) == m. 
  Proof.
    intros. unfold m2l,l2m. unfold Matrix.l2m. destruct m; simpl.
    hnf. simpl. apply l2m_aux_eq; auto.
  Qed.
    
  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c),
    ~(m1 == m2) -> ~(m2l m1 == m2l m2)%dlist.
  Proof.
    intros. destruct m1,m2. unfold meq,Matrix.meq in *; simpl in *. auto.
  Qed.
  
  Lemma m2l_surj : forall {r c} (d : list (list A)), 
    length d = r -> width d c -> 
    (exists m, (@m2l r c m == d)%dlist).
  Proof.
    intros. exists (mk_mat d H H0). simpl. easy.
  Qed.
  
  (* ==================================== *)
  (** ** Specific matrix *)

  Definition mk_mat_1_1 (a11 : A) : mat 1 1 :=
    mk_mat_1_1 a11.
  Definition mk_mat_3_1 (a1 a2 a3 : A) : mat 3 1 :=
    mk_mat_3_1 a1 a2 a3.
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A) : mat 3 3 :=
    mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.
  Definition mk_mat_2_2 (a11 a12 a21 a22 : A) : mat 2 2 :=
    mk_mat_2_2 a11 a12 a21 a22.

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

  (** old style, deprecated *)
  Definition m2t_3x3' (m : mat 3 3) : @T_3x3 A :=
    ((mnth m 0 0, mnth m 0 1, mnth m 0 2), 
     (mnth m 1 0, mnth m 1 1, mnth m 1 2),
     (mnth m 2 0, mnth m 2 1, mnth m 2 2)).
     
  Definition m2t_3x3 (m : mat 3 3) : @T_3x3 A.
    destruct m as [dl].
    remember (hd [] dl) as l1.
    remember (hd [] (tl dl)) as l2.
    remember (hd [] (tl (tl dl))) as l3.
    remember (hd A0 l1, hd A0 (tl l1), hd A0 (tl (tl l1))) as t1.
    remember (hd A0 l2, hd A0 (tl l2), hd A0 (tl (tl l2))) as t2.
    remember (hd A0 l3, hd A0 (tl l3), hd A0 (tl (tl l3))) as t3.
    exact (t1, t2, t3).
  Defined.

  (* ToDo: we havn't define the equality on T_3x3, do it later .. *)
  (* Lemma m2t_t2m_id_3x3 : forall (x : @T_3x3 A), m2t_3x3 (t2m_3x3 x) = x. *)
(*     Proof.
    destruct x as ((t1,t2),t3).
    destruct t1 as ((a11,a12),a13).
    destruct t2 as ((a21,a22),a23).
    destruct t3 as ((a31,a32),a33).
    simpl. auto.
  Qed. *)
  
  Lemma t2m_m2t_id_3x3 (m : mat 3 3) : t2m_3x3 (m2t_3x3 m) == m.
  Proof.
    destruct m as [dl HH HW]; simpl. unfold mk_mat_3_3,meq,Matrix.meq; simpl.
    do 4 (destruct dl; simpl in *; try easy).
    inv HW. inv H2. inv H4.
    do 4 (destruct l,l0,l1; simpl in *; try easy).
  Qed.
  
  (** m[0,0] : mat_1x1 -> A *)
  Definition scalar_of_mat (m : mat 1 1) := mnth m 0 0.
  
  (* ==================================== *)
  (** ** Matrix transposition *)

  Definition mtrans {r c} (m : mat r c): mat c r := @mtrans A r c m.
  
  Global Notation "m \T" := (mtrans m) : mat_scope.
  
  Lemma mtrans_trans : forall {r c} (m : mat r c), m \T\T == m.
  Proof.
    apply @mtrans_trans. apply Equiv_Aeq.
  Qed.
  
  (* ==================================== *)
  (** ** Mapping of matrix *)

  (** Mapping of a matrix *)
  Definition mmap {r c} (f : A -> A) (m : mat r c) : mat r c := matmap f m.
  
  (** Mapping of two matrices *)
  Definition mmap2 {r c} (f : A -> A -> A) (m1  m2 : mat r c) : mat r c :=
    matmap2 f m1 m2.
  
  Lemma mmap2_comm : forall {r c} (f : A -> A -> A)
    (f_comm : forall a b : A, (f a b == f b a)%A) (m1 m2 : mat r c), 
    mmap2 f m1 m2 == mmap2 f m2 m1.
  Proof.
    intros. apply @matmap2_comm. constructor. auto.
  Qed.
  
  Lemma mmap2_assoc : forall {r c} (f : A -> A -> A)
    (f_assoc : forall a b c, (f (f a b) c == f a (f b c))%A) (m1 m2 m3 : mat r c),
    mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
  Proof.
    intros. apply @matmap2_assoc. constructor; auto. apply Equiv_Aeq.
  Qed.

End BasicMatrixTheoryDR.


(* ######################################################################### *)
(** * Decidable matrix theory implemented with Dependent Record *)

Module DecidableMatrixTheoryDR (E : DecidableElementType) <: DecidableMatrixTheory E.

  Export E.
  Include BasicMatrixTheoryDR E.

  (** meq is decidable *)
  Lemma meq_dec : forall {r c}, Decidable (meq (r:=r) (c:=c)).
  Proof.
    intros. apply meq_dec. apply Dec_Aeq.
  Qed.

End DecidableMatrixTheoryDR.


(* ######################################################################### *)
(** * Ring matrix theory implemented with Dependent Record *)

Module RingMatrixTheoryDR (E : RingElementType) <: RingMatrixTheory E.

  Export E.
  Include BasicMatrixTheoryDR E.

  (** ** Declare ring instance to use ring tactic *)

  (** How to declare that the "Add" is respect to "Aeq" ?
      (1). Add Parametric Morphism as xxx.
      (2). Instance xxx.
      (3). Existing Instance xxx.
   *)
  (** (1). Add Parametric Morphism as xxx. *)
  (* Global Add Parametric Morphism : Aadd with signature *)
  (*        Aeq ==> Aeq ==> Aeq as Aadd_aeq_mor. *)
  (* Proof. apply Aadd_aeq_mor. Qed. *)

  (** (2). Instance xxx. *)
  (* Global Instance Aadd_aeq_mor : *)
  (*   Proper (Aeq  ==> Aeq ==> Aeq) (Aadd). *)
  (* Proof.  apply Aadd_aeq_mor. Qed. *)

  (** (3). Existing Instance xxx. *)
  (* Note that, these declarations have been finished in module E. *)
  (* Global Existing Instance Aadd_aeq_mor. *)

  Add Ring ring_thy_inst : Ring_thy.

  
  (** ** Algebraic matrix theory *)

  (** Zero matrix *)
  Definition mat0 r c : mat r c := mat0 A0.
  
  (* (** A matrix is a nonzero matrix *) *)
  (* Definition matnonzero {r c} (m : mat r c) : Prop := ~(m == mat0 r c). *)
  
  (** Unit matrix *)
  Definition mat1 n : mat n n := mat1 A0 A1.

  (** *** Addition of matrix *)

  Definition madd {r c} := @madd A Aadd r c.
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
    intros. apply madd_zero_l.
  Qed.

  (** m + 0 = m *)
  Lemma madd_0_r : forall {r c} (m : mat r c), m + (mat0 r c) == m.
  Proof.
    intros. apply madd_zero_r.
  Qed.

  (** madd and (dmap2 Aadd) are homomorphic over m2l *)
  Lemma m2l_madd_homo : forall r c,
      Homomorphic (Beq:=eqlistA (eqlistA Aeq)) madd (dmap2 Aadd) (@m2l r c).
  Proof.
    intros. constructor. intros.
    destruct a1,a2. simpl.
    unfold matmap2dl. simpl. easy.
  Qed.

  
  (** *** Opposite of matrix *)

  Definition mopp {r c} (m : mat r c) : mat r c := @mopp A Aopp r c m.
  Notation "- m" := (mopp m) : mat_scope.

  (** - - m = m *)
  Lemma mopp_opp : forall {r c} (m : mat r c), - - m == m.
  Proof.
    intros. apply mopp_opp.
  Qed.

  (** - m1 = m2 <-> m1 = - m2 *)
  Lemma mopp_exchange : forall {r c} (m1 m2 : mat r c), -m1 == m2 <-> m1 == -m2.
  Proof.
    intros. apply mopp_exchange.
  Qed.

  (** - 0 = 0 *)
  Lemma mopp_mat0 : forall {r c}, - (mat0 r c) == mat0 r c.
  Proof.
    intros. apply mopp_mat0.
  Qed.

  (** m + (-m) = 0 *)
  Lemma madd_opp : forall {r c} (m : mat r c), m + (-m) == mat0 r c.
  Proof.
    intros. apply madd_opp.
  Qed.

  
  (** *** Subtraction of matrix *)

  Definition msub {r c} := @msub A Aadd Aopp r c.
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
    intros. apply msub_zero_l.
  Qed.

  (** m - 0 = m *)
  Lemma msub_0_r : forall {r c} (m : mat r c), m - (mat0 r c) == m.
  Proof.
    intros. apply msub_zero_r.
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
  Infix " 'c*' " := mcmul : mat_scope.
  
  (** Right scalar multiplication of matrix *)
  Definition mmulc {r c} (m : mat r c) (a : A) : mat r c :=
    @mmulc A Amul r c m a.
  Infix " '*c' " := mmulc : mat_scope.

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
    intros. apply mcmul_1.
  Qed.
  
  (** (-a) * m = - (a * m) *)
  Lemma mcmul_neg : forall {r c} a (m : mat r c), (-a)%A c* m == - (a c* m).
  Proof.
    intros. apply mcmul_neg.
  Qed.
  
  (** (-a) * (- m) = (a * m) *)
  Lemma mcmul_neg_mopp : forall {r c} a (m : mat r c), (-a)%A c* (-m) == a c* m.
  Proof.
    intros. apply mcmul_neg_mopp.
  Qed.

  
  (** *** Multiplication of matrix *)
  
  Definition mmul {r c s} (m1 : mat r c) (m2 : mat c s) : mat r s :=
    @mmul A A0 Aadd Amul r c s m1 m2.
  Infix "*" := mmul : mat_scope.

  (** m1 * (m2 + m3) = (m1 * m2) + (m1 * m3) *)
  Lemma mmul_add_distr_l : forall {r c A} (m1 : mat r c) (m2 m3 : mat c A),
    m1 * (m2 + m3) == m1 * m2 + m1 * m3.
  Proof.
    intros. apply mmul_add_distr_l.
  Qed.
  
  (** (m1 + m2) * m3 = (m1 * m3) + (m2 * m3) *)
  Lemma mmul_add_distr_r : forall {r c s} (m1 m2 : mat r c) (m3 : mat c s),
    (m1 + m2) * m3 == (m1 * m3) + (m2 * m3).
  Proof.
    intros. apply mmul_add_distr_r.
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

End RingMatrixTheoryDR.


(* ######################################################################### *)
(** * Decidable Field matrix theory implemented with Dependent Record *)

Module DecidableFieldMatrixTheoryDR (E : DecidableFieldElementType)
<: DecidableFieldMatrixTheory E.

  Export E.
  Include RingMatrixTheoryDR E.
  Module Export DecMT := DecidableMatrixTheoryDR E.

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
    intros. apply mcmul_eq0_imply_m0_or_k0. auto.
  Qed.

  (** (m <> 0 \/ k * m = 0) -> k = 0 *)
  Lemma mcmul_mnonzero_eq0_imply_k0 : forall {r c} (m : mat r c) k,
      let m0 := mat0 r c in
      ~(m == m0) -> k c* m == m0 -> (k == A0)%A.
  Proof.
    intros. apply mcmul_mnonzero_eq0_imply_k0 with (m:=m); auto.
  Qed.

  (** k * m = m -> k = 1 \/ m = 0 *)
  Lemma mcmul_same_imply_coef1_or_mzero : forall {r c} k (m : mat r c),
      k c* m == m -> (k == A1)%A \/ (m == mat0 r c).
  Proof.
    intros. apply mcmul_same_imply_coef1_or_mzero. auto.
  Qed.

  (** (m1 <> 0 /\ m2 <> 0 /\ k * m1 = m2) -> k <> 0 *)
  Lemma mcmul_eq_mat_implfy_not_k0 : forall {r c} (m1 m2 : mat r c) k,
      let m0 := mat0 r c in
      ~(m1 == m0) -> ~(m2 == m0) -> k c* m1 == m2 -> ~(k == A0)%A.
  Proof.
    intros. apply mcmul_eq_mat_implfy_not_k0 with m1 m2; auto.
  Qed.

End DecidableFieldMatrixTheoryDR.


(** * Extra Properties *)
Module ExtraMatrixTheoryDR (E : DecidableFieldElementType).

  Export E.
  Include (DecidableFieldMatrixTheoryDR E).
  
  (** Vector type *)
  Definition vecr n := mat 1 n.
  Definition vecc n := mat n 1.
  
  (** determinant of a 3D square matrix *)
  Definition det_of_mat_3_3 (m : mat 3 3) : A :=
    let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) :=
      m2t_3x3 m in
    let b1 := (a11 * a22 * a33)%A in
    let b2 := (a12 * a23 * a31)%A in
    let b3 := (a13 * a21 * a32)%A in
    let c1 := (a11 * a23 * a32)%A in
    let c2 := (a12 * a21 * a33)%A in
    let c3 := (a13 * a22 * a31)%A in
    let b := (b1 + b2 + b3)%A in
    let c := (c1 + c2 + c3)%A in
      (b - c)%A.

  (** Skew symmetrix matrix *)
  (* Definition skew_sym_mat_of_v3 (v : vecc 3) : mat 3 3. *)
  (* Proof. *)
  (*   destruct (v3_to_t3 v) as [[x y] z]. *)
  (*   refine (mk_mat_3_3 *)
  (*     A0    (-z)    y *)
  (*     z     A0     (-x) *)
  (*     (-y)  x       A0)%A. *)
  (* Defined. *)
  
  (* Cross/Vector product of 3D vector *)
  (* Definition v3cross (v1 v2 : V3) : vec 3 := (skew_sym_mat_of_v3 v1) * v2. *)

  (* A matrix is a SO3 (Special Orthogonal group, rotation group) *)
  Definition so3 (m : mat 3 3) : Prop :=
    let so3_mul_unit : Prop := (m \T) * m = mat1 3 in
    let so3_det : Prop := (det_of_mat_3_3 m) = A1 in
      so3_mul_unit /\ so3_det.

End ExtraMatrixTheoryDR.


Module coordinate_transform_test.

  Module Import MT := ExtraMatrixTheoryDR DecidableFieldElementTypeR.
  Import Reals.
  Open Scope R.
  Open Scope mat_scope.

  (* ref:
  https://en.wikipedia.org/wiki/Matrix_(mathematics)#Basic_operations
  *)

  Definition m1 := @l2m 2 3 [[1;3;1];[1;0;0]].
  Definition m2 := @l2m 2 3  [[0;0;5];[7;5;0]].
  Definition m3 := @l2m 2 3  [[1;3;6];[8;5;0]].
  Example madd_m1_m2_eq_m3 : m1 + m2 == m3.
  Proof.
    cbv. repeat constructor; ring.
  Qed.
  
  Definition m4 := @l2m 2 3 [[1;8;-3];[4;-2;5]].
  Definition m5 := @l2m 2 3 [[2;16;-6];[8;-4;10]].
  Example mscale_2_m4_eq_m5 : 2 c* m4 == m5.
  Proof.
    cbv. repeat constructor; ring.
  Qed.
  
  Definition m6 := @l2m 2 3 [[1;2;3];[0;-6;7]].
  Definition m7 := @l2m 3 2 [[1;0];[2;-6];[3;7]].
  Example mtrans_m6_eq_m7 : m6 \T == m7.
  Proof.
    cbv. repeat constructor; ring.
  Qed.
  
  
  Variable θ ψ φ : R.
  Definition Rx (α : R) : mat 3 3 := mk_mat_3_3
    1         0           0
    0         (cos α)     (sin α)
    0         (-sin α)%R    (cos α).

  Definition Ry (β : R) : mat 3 3 := mk_mat_3_3
    (cos β)   0           (-sin β)%R
    0         1           0
    (sin β)   0           (cos β).

  Definition Rz (γ : R) : mat 3 3 := mk_mat_3_3 
    (cos γ)   (sin γ)   0
    (-sin γ)%R  (cos γ)   0
    0         0         1.

  Definition R_b_e_direct : mat 3 3 := (mk_mat_3_3
    (cos θ * cos ψ)
    (cos ψ * sin θ * sin φ - sin ψ * cos φ)
    (cos ψ * sin θ * cos φ + sin φ * sin ψ)
    
    (cos θ * sin ψ)
    (sin ψ * sin θ * sin φ + cos ψ * cos φ)
    (sin ψ * sin θ * cos φ - cos ψ * sin φ)
    
    (-sin θ)
    (sin φ * cos θ)
    (cos φ * cos θ))%R.
   
  Opaque cos sin.
  
  Lemma Rx_Ry_Rz_eq_Rbe : (Rz ψ)\T * (Ry θ)\T * (Rx φ)\T == R_b_e_direct.
  Proof.
    cbv. repeat constructor; ring.
  Qed.
  
End coordinate_transform_test.

