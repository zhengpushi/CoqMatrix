(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Signature of Vector Theory
  author    : ZhengPu Shi
  date      : 2022.06
  
  reference :
  1. Vector Calculus - Michael Corral
  2. https://github.com/coq/coq/blob/master/test-suite/success/Nsatz.v
     Note: there are geometrys in coq, including point, parallel, collinear, etc.
  3. (in Chinese) Higher Mathematics Study Manual - Xu Xiao Zhan, p173
     《高等数学学习手册》徐小湛，p173
 *)

Require Export BasicConfig TupleExt SetoidListListExt HierarchySetoid.
Require Export ElementType.


(* ######################################################################### *)
(** * Basic vector theory *)
Module Type BasicVectorTheory (E : ElementType).

  (* ==================================== *)
  (** ** Vector element type *)
  Export E.

  Infix "==" := (eqlistA Aeq) : list_scope.

  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope vec_scope.
  
  (* ==================================== *)
  (** ** Vector type and basic operations *)
  Parameter vec : nat -> Type.
  
  (** matrix equality *)
  Parameter veq : forall {n}, vec n -> vec n -> Prop.
  Infix "==" := veq : vec_scope.

  (** meq is equivalence relation *)
  Axiom veq_equiv : forall n, Equivalence (veq (n:=n)).

  (** Get n-th element *)
  Parameter vnth : forall {n} (v : vec n) (i : nat), A.

  (** veq and mnth should satisfy this constraint *)
  Axiom veq_iff_vnth : forall {n : nat} (v1 v2 : vec n),
      (v1 == v2) <-> (forall i, i < n -> (vnth v1 i == vnth v2 i)%A).

  (* ==================================== *)
  (** ** Convert between list and vector *)
  Parameter l2v : forall {n} (l : list A), vec n.
  Parameter v2l : forall {n}, vec n -> list A.
  
  Axiom v2l_length : forall {n} (v : vec n), length (v2l v) = n.
  
  Axiom v2l_l2v_id : forall {n} (l : list A), length l = n -> (@v2l n (@l2v n l) == l)%list.
  Axiom l2v_v2l_id : forall {n} (v : vec n), l2v (v2l v) == v.

  (* ==================================== *)
  (** ** Convert between tuples and vector *)
  Parameter t2v_2 : @T2 A -> vec 2.
  Parameter t2v_3 : @T3 A -> vec 3.
  Parameter t2v_4 : @T4 A -> vec 4.
  
  Parameter v2t_2 : vec 2 -> @T2 A.
  Parameter v2t_3 : vec 3 -> @T3 A.
  Parameter v2t_4 : vec 4 -> @T4 A.
  
  (* Axiom t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v. *)
  (* Axiom v2t_t2v_id_2 : forall (t : A * A), v2t_2 (t2v_2 t) = t. *)

  (* ==================================== *)
  (** ** Mapping for vector *)
  
  (** Mapping a vector *)
  Parameter vmap : forall {n} (v : vec n) (f : A -> A), vec n.
  
  (** Fold a vector *)
  (*   Parameter vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)
  
  (** Mapping two vectors *)
  Parameter vmap2 : forall {n} (v1 v2 : vec n) (f : A -> A -> A), vec n.

End BasicVectorTheory.



(* ######################################################################### *)
(** * Ring vector theory *)

(** zero vector, vector addition, opposition, substraction, scalar multiplication,
    dot product *)
Module Type RingVectorTheory (E : RingElementType) <: BasicVectorTheory E.

  Export E.
  Include (BasicVectorTheory E).

  (** zero vector *)
  Parameter vec0 : forall n, vec n.

  (** *** Vector addition *)
  Parameter vadd : forall {n} (v1 v2 : vec n), vec n.
  Infix "+" := vadd : vec_scope.
  Axiom vadd_comm : forall {n} (v1 v2 : vec n), (v1 + v2) == (v2 + v1).
  Axiom vadd_assoc : forall {n} (v1 v2 v3 : vec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Axiom vadd_0_l : forall {n} (v : vec n), (vec0 n) + v == v.
  Axiom vadd_0_r : forall {n} (v : vec n), v + (vec0 n) == v.
  
  (** *** Vector opposition *)
  Parameter vopp : forall {n} (v : vec n), vec n.
  Notation "- v" := (vopp v) : vec_scope.
  Axiom vadd_opp : forall {n} (v : vec n), v + (- v) == vec0 n.

  (** *** Vector subtraction *)
  Parameter vsub : forall {n} (v1 v2 : vec n), vec n.
  Infix "-" := vsub : vec_scope.

  (** *** Vector scalar multiplication *)
  Parameter vcmul : forall {n} (a : A) (v : vec n), vec n.
  Parameter vmulc : forall {n} (v : vec n) (a : A), vec n.
  Infix "c*" := vcmul : vec_scope.
  Infix "*c" := vmulc : vec_scope.
  Axiom vmulc_eq_vcmul : forall {n} a (v : vec n), v *c a == a c* v.
  Axiom vcmul_assoc : forall {n} a b (v : vec n), a c* (b c* v) == (a * b)%A c* v.
  Axiom vcmul_perm : forall {n} a b (v : vec n), a c* (b c* v) == b c* (a c* v).
  Axiom vcmul_add_distr_l : forall {n} a b (v : vec n),
      (a + b)%A c* v == (a c* v) + (b c* v).
  Axiom vcmul_add_distr_r : forall {n} a (v1 v2 : vec n),
      a c* (v1 + v2) = (a c* v1) + (a c* v2).
  Axiom vcmul_0_l : forall {n} (v : vec n), A0 c* v == vec0 n.
  Axiom vcmul_1_l : forall {n} (v : vec n), A1 c* v == v.

  (** *** Vector dot product *)
  Parameter vdot : forall {n} (v1 v2 : vec n), A.

End RingVectorTheory.


(* ######################################################################### *)
(** * Decidable field vector theory *)

Module Type DecidableFieldVectorTheory (E : DecidableFieldElementType)
<: RingVectorTheory E.

  Export E.
  Include (RingVectorTheory E).

  (** veq is decidable *)
  Axiom veq_dec : forall (n : nat), Decidable (veq (n:=n)).

End DecidableFieldVectorTheory.


(** ** Others, later ... *)

(*
(** Assert that a vector is an zero vector. *)
Parameter vzero : forall {n} (v : vec n), Prop.

(** Assert that a vector is an non-zero vector. *)
Parameter vnonzero : forall {n} (v : vec n), Prop.

(** It is decidable that if a vector is zero vector. *)
Axiom vzero_dec : forall {n} (v : vec n), {vzero v} + {vnonzero v}.

(** vec0 is equal to mat0 with column 1 *)
(*   Lemma vec0_eq_mat0 : forall n, vec0 n = mat0 n 1.
  Proof. lma. Qed. *)

(** If two nonzero vectors has scalar multiplcation relation, 
    then the scalar coefficient must non-zero *)
Axiom vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : vec n) k,
    vnonzero v1 -> vnonzero v2 -> (v1 = k c* v2) -> k <> A0.
 *)
