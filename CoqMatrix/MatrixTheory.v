(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Signature of Matrix Theory
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. This is an inteface of different matrix implementation.
  2. The matrix theory is orgainized at several levels
     (1) BasicMatrixTheory
         matrix theory on element with equivalence relaton.
     (2) DecidableMatrixTheory
         matrix theory on element with decidable relation
     (3) RingMatrixTheory
         matrix theory on element with ring structure.
     (4) FieldMatrixTheory
         matrix theory on element with field structure.
     (5) DecidableFieldTheory
         matrix theory on element with decidable field structure.

 *)

Require Export BasicConfig TupleExt SetoidListListExt HierarchySetoid.
Require Export ElementType.


(* ######################################################################### *)
(** * Basic matrix theory *)
Module Type BasicMatrixTheory (E : ElementType).

  (* ==================================== *)
  (** ** Matrix element type *)
  Export E.

  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.

  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope mat_scope.
  
  (* ==================================== *)
  (** ** Matrix type and basic operations *)
  Parameter mat : nat -> nat -> Type.

  (** matrix equality *)
  Parameter meq : forall {r c}, mat r c -> mat r c -> Prop.
  Infix "==" := meq : mat_scope.

  (** meq is equivalence relation *)
  Axiom meq_equiv : forall r c, Equivalence (meq (r:=r) (c:=c)).

  (** Get n-th element *)
  Parameter mnth : forall {r c}, mat r c -> nat -> nat -> A.

  (** meq and mnth should satisfy this constraint *)
  Axiom meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> (forall ri ci, ri < r -> ci < c -> (mnth m1 ri ci == mnth m2 ri ci)%A).

  (* ==================================== *)
  (** ** Convert between list list and matrix *)
  Parameter l2m : forall {r c} (dl : list (list A)), mat r c.
  Parameter m2l : forall {r c}, mat r c -> list (list A).
  Axiom m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
  Axiom m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
  
  Axiom m2l_l2m_id : forall {r c} (dl : list (list A)),
      length dl = r -> width dl c -> (m2l (@l2m r c dl) == dl)%dlist.
  Axiom l2m_m2l_id : forall {r c} (m : mat r c), 
      l2m (m2l m) == m.
  
  Axiom l2m_inj : forall {r c} (d1 d2 : list (list A)),
      length d1 = r -> width d1 c -> 
      length d2 = r -> width d2 c -> 
      ~(d1 == d2)%dlist -> ~(@l2m r c d1 == l2m d2).
  Axiom l2m_surj : forall {r c} (m : mat r c), 
      (exists d, l2m d == m). 
  Axiom m2l_inj : forall {r c} (m1 m2 : mat r c),
      ~ m1 == m2 -> ~(m2l m1 == m2l m2)%dlist.
  Axiom m2l_surj : forall {r c} (d : list (list A)), 
      length d = r -> width d c -> 
      (exists m, @m2l r c m == d)%dlist.
  
  (* ==================================== *)
  (** ** Convert between function and matrix *)
  (* Parameter f2m : forall {r c} (f : nat -> nat -> A), mat r c. *)
  (* Parameter m2f : forall {r c}, mat r c -> (nat -> nat -> A). *)

  (* ==================================== *)
  (** ** Specific matrix *)
  Parameter mk_mat_1_1 : forall (a11 : A), mat 1 1.
  Parameter mk_mat_3_1 : forall (a1 a2 a3 : A), mat 3 1.
  Parameter mk_mat_3_3 : forall (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A), 
      mat 3 3.
  
  (* ==================================== *)
  (** ** Convert between tuples and matrix *)
  Parameter t2m_3x3 : @T_3x3 A -> mat 3 3.
  Parameter m2t_3x3 : mat 3 3 -> @T_3x3 A.
  Parameter scalar_of_mat : forall (m : mat 1 1), A.
  
  (* ==================================== *)
  (** ** Matrix transposition *)
  Parameter mtrans : forall {r c} (m : mat r c), mat c r.
  Notation "m \T" := (mtrans m) : mat_scope.
  Axiom mtrans_trans : forall {r c} (m : mat r c), m \T\T == m.

  
  (* ==================================== *)
  (** ** Mapping of matrix *)
  Parameter mmap : forall {r c} (f : A -> A) (m : mat r c), mat r c.
  Parameter mmap2 : forall {r c} (f: A -> A -> A) (m1 m2 : mat r c), mat r c.
  Axiom mmap2_comm : forall {r c} (f : A -> A -> A)
                       (f_comm : forall a b, (f a b == f b a)%A)
                       (m1 m2 : mat r c), 
      mmap2 f m1 m2 == mmap2 f m2 m1.
  Axiom mmap2_assoc : forall {r c} (f : A -> A -> A)
                        (f_assoc : forall a b c, (f (f a b) c == f a (f b c))%A)
                        (m1 m2 m3 : mat r c), 
      mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).

End BasicMatrixTheory.


(* ######################################################################### *)
(** * Decidable matrix theory *)

Module Type DecidableMatrixTheory (E : DecidableElementType) <: BasicMatrixTheory E.

  Export E.
  Include (BasicMatrixTheory E).

  (* (** the equality of matrix element should be decidable *) *)
  (* Context `{Dec_Aeq:Decidable A Aeq}. *)

  (** equality of two matrices is decidable *)
  Axiom meq_dec : forall {r c}, Decidable (meq (r:=r) (c:=c)).

End DecidableMatrixTheory.


(* ######################################################################### *)
(** * Ring matrix theory *)

(** zero matrix, unit matrix,
    matrix addition, opposition, substraction, scalar multiplication,
    multiplication *)
Module Type RingMatrixTheory (E : RingElementType) <: BasicMatrixTheory E.

  Export E.
  Include (BasicMatrixTheory E).

  (* ==================================== *)
  (** ** Matrix algebra *)

  (** zero matrix *)
  Parameter mat0 : forall r c, mat r c.

  (** unit matrix *)
  Parameter mat1 : forall n, mat n n.

  (** *** Matrix addition *)
  Parameter madd : forall {r c}, mat r c -> mat r c -> mat r c.
  Infix "+" := madd : mat_scope.
  Axiom madd_comm : forall {r c} (m1 m2 : mat r c), m1 + m2 == m2 + m1.
  Axiom madd_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) + m3 == m1 + (m2 + m3).
  Axiom madd_0_l : forall {r c} (m : mat r c), (mat0 r c) + m == m.

  (** *** Matrix opposition *)
  Parameter mopp : forall {r c}, mat r c -> mat r c.
  Notation "- m" := (mopp m) : mat_scope.
  Axiom mopp_opp : forall {r c} (m : mat r c), - - m == m.
  Axiom madd_opp : forall {r c} (m : mat r c), m + (-m) == (mat0 r c).

  (** *** Matrix subtraction *)
  Parameter msub : forall {r c}, mat r c -> mat r c -> mat r c.
  Infix "-" := msub : mat_scope.
  Axiom msub_comm : forall {r c} (m1 m2 : mat r c), m1 - m2 == - (m2 - m1).
  Axiom msub_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 - m2) - m3 == m1 - (m2 + m3).
  Axiom msub_0_l : forall {r c} (m : mat r c), (mat0 r c) - m == - m.
  Axiom msub_0_r : forall {r c} (m : mat r c), m - (mat0 r c) == m.
  Axiom msub_self : forall {r c} (m : mat r c), m - m == (mat0 r c).

  (** *** Matrix scalar multiplication *)
  Parameter mcmul : forall {r c} (a : A) (m : mat r c), mat r c.
  Parameter mmulc : forall {r c} (m : mat r c) (a : A), mat r c.
  Infix " 'c*' " := mcmul : mat_scope.
  Infix " '*c' " := mmulc : mat_scope.
  Axiom mmulc_eq_mcmul : forall {r c} (a : A) (m : mat r c), m *c a == a c* m.
  Axiom mcmul_assoc : forall {r c} (a b : A) (m : mat r c),
      a c* (b c* m) == (a * b)%A c* m.
  Axiom mcmul_perm : forall {r c} (a b : A) (m : mat r c),
      a c* (b c* m) == b c* (a c* m).
  Axiom mcmul_add_distr_l : forall {r c} (a : A) (m1 m2 : mat r c),
      a c* (m1 + m2) == (a c* m1) + (a c* m2).
  Axiom mcmul_add_distr_r : forall {r c} (a b : A) (m : mat r c),
      (a + b)%A c* m == (a c* m) + (b c* m).
  Axiom mcmul_1_l : forall {r c} (m : mat r c), A1 c* m == m.
  Axiom mcmul_0_l : forall {r c} (m : mat r c), A0 c* m == mat0 r c.

  (** *** Matrix multiplication *)
  Parameter mmul : forall {r c s}, mat r c -> mat c s -> mat r s.
  Infix "*" := mmul : mat_scope.
  Axiom mmul_add_distr_l : forall {r c s} (m1 : mat r c) (m2 m3 : mat c s),
      m1 * (m2 + m3) == (m1 * m2) + (m1 * m3).
  Axiom mmul_add_distr_r : forall {r c s} (m1 m2 : mat r c) (m3 : mat c s),
      (m1 + m2) * m3 == (m1 * m3) + (m2 * m3).
  Axiom mmul_assoc : forall {r c s t} (m1 : mat r c) (m2 : mat c s) (m3 : mat s t),
      (m1 * m2) * m3 == m1 * (m2 * m3).
  Axiom mmul_0_l : forall {r c s} (m : mat c s), (mat0 r c) * m == mat0 r s.
  Axiom mmul_0_r : forall {r c s} (m : mat r c), m * (mat0 c s) == mat0 r s.
  Axiom mmul_1_l : forall {r c} (m : mat r c), (mat1 r) * m == m.
  Axiom mmul_1_r : forall {r c} (m : mat r c), m * (mat1 c) == m. 

End RingMatrixTheory.



(* ######################################################################### *)
(** * Decidable field matrix theory *)

Module Type DecidableFieldMatrixTheory (E : DecidableFieldElementType)
<: RingMatrixTheory E
<: DecidableMatrixTheory E.

  Export E.
  Include (RingMatrixTheory E).

  (** meq is decidable *)
  Axiom meq_dec : forall (r c : nat), Decidable (meq (r:=r) (c:=c)).

  (* (** k * m = 0 -> (m = 0) \/ (k = 0) *) *)
  (* Axiom mcmul_eq0_imply_m0_or_k0 : forall {r c} (m : mat r c) k, *)
  (*     let m0 := mat0 r c in *)
  (*     (k c* m == m0) -> (m == m0) \/ (k == A0)%A. *)

  (* (** (m <> 0 \/ k * m = 0) -> k = 0 *) *)
  (* Axiom mcmul_mnonzero_eq0_imply_k0 : forall {r c} (m : mat r c) k, *)
  (*     let m0 := mat0 r c in *)
  (*     ~(m == m0) -> k c* m == m0 -> (k == A0)%A. *)

  (* (** k * m = m -> k = 1 \/ m = 0 *) *)
  (* Axiom mcmul_same_imply_coef1_or_mzero : forall {r c} k (m : mat r c), *)
  (*     k c* m == m -> (k == A1)%A \/ (m == mat0 r c). *)

  (* (** (m1 <> 0 /\ m2 <> 0 /\ k * m1 = m2) -> k <> 0 *) *)
  (* Axiom mcmul_eq_mat_implfy_not_k0 : forall {r c} (m1 m2 : mat r c) k, *)
  (*     let m0 := mat0 r c in *)
  (*     ~(m1 == m0) -> ~(m2 == m0) -> k c* m1 == m2 -> ~(k == A0)%A. *)
  
End DecidableFieldMatrixTheory.

