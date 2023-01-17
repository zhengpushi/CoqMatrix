(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Fin Function
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. reference:  
  https://math-comp.github.io/htmldoc_1_14_0/mathcomp.algebra.matrix.html#matrix
  2. change it to Functor version, which can support multiple Base Type.
  3. especially we want to use RingType as Base Type, because lots of operations 
    related to Base Type could be omitted. 
 *)



(** The library all_algebra contain 'matrix' formalization *)
From mathcomp Require Import all_ssreflect all_algebra.

Require Export MatrixTheory.
(* Require Export ListListExt.
Require Export FieldTypeR.
Require Import MatrixSig. *)

(* Require Export Fin.
Require Export Arith.
Require Export Lia.
Require Export List.
Export ListNotations. *)

Generalizable Variable A B C Aeq Beq Ceq Aadd Aopp Amul Ainv.

Open Scope A_scope.
Open Scope mat_scope.

Section FinFunMatrix.

  (* Note that, in the construction of _ringtype, we need the proof of "1 <> 0",
     I don't sure how to organize it, becuase in my hierarchy and in Coq's hierarchy,
     "1 <> " is a property in a field structure. So, I use limited field to instead
     ring structure *)

  (* Context `{R : Ring A Aadd A0 Aopp Amul A1 eq}. *)
  (* Add Ring ring_inst : make_ring_theory. *)

  Context `{F : Field}.
  Context `{Dec_eq : Decidable A Aeq}.

  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := Amul : A_scope.
  Add Field field_inst : make_field_theory.


  (** package A to ringType structure, to enable A be used as carrier type 
    of MathComp.matrix. 
    We must construct the required hierarchy one by one, otherwise, the later 
    structure will fail.
    For example, choiceType need a eqType canonical declaration, and so on *)
  Section carrier_of_matrix.

    (* eqType *)
    Section eqType.
      (** reflect (x1 = x2) (x1 =? x2) *)
      Let A_eqbP : Equality.axiom Aeqb.
      Proof.
        hnf. intros. destruct (decidable x y) as [H|H]; auto.
        - apply Aeqb_true in H. rewrite H. constructor.
          apply Aeqb_true. auto.
        - apply Aeqb_false in H. rewrite H. constructor.
          apply Aeqb_false. auto.
      Qed.
      
      Let A_eqMixin := EqMixin A_eqbP.
      Canonical A_eqType := Eval hnf in EqType A A_eqMixin.
    End eqType.
    
    (* choiceType *)
    Section choiceType.
      Import Countable.

      Definition pickle (x : A) := 0%nat.
      Definition unpickle (n:nat) : option A := None.
      Definition pcancel : pcancel pickle unpickle. Admitted.
      Definition A_choiceType_mixin_of : mixin_of A :=
        Mixin pcancel.
      
      Let A_choiceMixin := ChoiceMixin A_choiceType_mixin_of.
      Canonical A_choiceType := ChoiceType A A_choiceMixin.
    End choiceType.
    
    (* zmodType *)
    Section zmodType.
      Import ssrfun.
      
      Let Aadd_assoc : associative Aadd.
      Proof.
        hnf;intros;ring.
      Qed.
      
      Let Aadd_comm : commutative Aadd.
      Proof.
        hnf;intros;ring.
      Qed.
      
      Let Aadd_left_id : left_id A0 Aadd.
      Proof.
        hnf;intros;ring.
      Qed.
      
      Let Aadd_left_inv : left_inverse A0 Aopp Aadd.
      Proof.
        hnf;intros;ring.
      Qed.
      
      Let A_zmodMixin := ZmodMixin Aadd_assoc Aadd_comm Aadd_left_id 
                           Aadd_left_inv.
      Canonical A_zmodType := Eval hnf in ZmodType _ A_zmodMixin.
    End zmodType.
    
    (* ringType *)
    Section ringType.
      Import ssrfun.
      
      Let Amul_assoc : associative Amul.
      Proof.
        hnf;intros;ring.
      Qed.
      
      Let Amul_left_id : left_id A1 Amul.
      Proof.
        hnf;intros;ring.
      Qed.
      
      Let Amul_right_id : right_id A1 Amul.
      Proof.
        hnf;intros;ring.
      Qed.
      
      Let Amul_left_distr : left_distributive Amul Aadd.
      Proof.
        hnf;intros;ring.
      Qed.
      
      Let Amul_right_distr : right_distributive Amul Aadd.
      Proof.
        hnf;intros;ring.
      Qed.
      
      (* 1 != 0%R *)
      Let A_1_neq_0 : negb (eq_op A1 (GRing.zero A_zmodType)).
      Proof.
        cbv. assert (H : Aeqb A1 A0 = false).
        - apply Aeqb_false. apply field_1_neq_0.
        - apply Aeqb_false in H.
          destruct Dec_eq. destruct decidable; auto.
      Qed.
      
      Let A_ringMixin := RingMixin Amul_assoc Amul_left_id Amul_right_id
                           Amul_left_distr Amul_right_distr A_1_neq_0.
      Canonical A_ringType := Eval hnf in RingType _ A_ringMixin.
      
    End ringType.
    
  End carrier_of_matrix.


  (** Matrix type *)

  (* details about Mathcomp.matrix is complex *)
  (*   Print matrix.       (* Inductive matrix := Matrix (_:finfun_of) *)
  Print finfun_of.    (* Inductive finfun_of := FinfunOf (_:finfun_on) *)
  Print finfun_on.    (* Inductive finfun_on := finfun_nil | finfun_cons *)
   *)  
  Definition mat (r c : nat) := matrix A r c.

  (** The equality is decidable *)
  Lemma meq_dec : forall {r c} (m1 m2 : mat r c), {m1 = m2} + {m1 <> m2}.
  Proof.
    intros. apply (@eq_comparable (matrix_eqType A_eqType r c)).
  Qed.

  (** Mathcomp issue: leq (S a) b <-> Nat.ltb a b *)
  (* Two different definitions for natural number comparision:
   leq is given by Mathcomp
   Nat.ltb is given by Coq Std.Lib *)
  Fact mathcomp_leq_iff_ltb : forall a b : nat, leq (S a) b <-> Nat.ltb a b.
  Proof.
    intros.
    destruct (@leP a b), (@Nat.ltb_spec a b).
  Admitted. (* ToDo: ? *)
  (* Some idea of the proof: owing to big difference of two definitions, maybe it is 
   hard to proof directly. We can proove it with the help of induction relation le.
   1. Convert Nat.ltb to le，use Nat.ltb_spec，
      Convert leq to le, use leP.
   2. Nat.ltb_spec : forall x y : nat, BoolSpec (lt x y) (le y x) (Nat.ltb x y)
      if lt x y，Nat.ltb x y = true
      then     ，Nat.ltb x y = false
    
      leP: forall {m n : nat}, reflect (le m n) (leq m n)
      if le m n，leq m n = true
      then     ，leq m n = false *)

  (** Get element of a matrix *)  
  Definition mnth' {r c} (m : mat r c) (ri ci : nat) : A.
  Proof.
    destruct (ri <? r) eqn:H1, (ci <? c) eqn:H2.
    { apply mathcomp_leq_iff_ltb in H1,H2.  (*  <? to <  *)
      pose (ri' := @Ordinal r ri H1).
      pose (ci' := @Ordinal c ci H2).
      exact (m ri' ci'). }
    all: exact A0.  (* all other situation is A0 *)
  Defined.

  Definition mnth {r c} (m : mat r c) (ri ci : nat) : A.
  Proof.
    destruct (ri < r) eqn:H1, (ci < c) eqn:H2.
    { exact (m (@Ordinal r ri H1) (@Ordinal c ci H2)). }
    all: exact A0.
  Defined.

  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
      m1 = m2 <-> 
        (forall ri ci (Hri : lt ri r) (Hci : lt ci c),
            mnth m1 ri ci = mnth m2 ri ci).
  Proof.
    intros. split; intros.
    { destruct (ri < r) eqn:H1, (ci < c) eqn:H2.
      { unfold mnth.
  Admitted.

  (** Create specific matrix *)
  Definition mk_mat_1_1 (a11 : A) : mat 1 1 :=
    matrix_of_fun_def 
      (fun i j => match i,j with (* i : ordinal_finType 1 *)
                  | Ordinal 0 _, Ordinal 0 _ => a11 
                  | _,_ => A0 
                  end).
  Definition mk_mat_3_1 (a1 a2 a3 : A) : mat 3 1 :=
    matrix_of_fun_def 
      (fun i j => match i,j with
                  | Ordinal 0 _, Ordinal 0 _ => a1 
                  | Ordinal 1 _, Ordinal 0 _ => a2 
                  | Ordinal 2 _, Ordinal 0 _ => a3 
                  | _,_ => A0 
                  end).
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A) : mat 3 3 := 
    matrix_of_fun_def 
      (fun i j => match i,j with
                  | Ordinal 0 _, Ordinal 0 _ => a11 
                  | Ordinal 0 _, Ordinal 1 _ => a12 
                  | Ordinal 0 _, Ordinal 2 _ => a13
                  | Ordinal 1 _, Ordinal 0 _ => a21 
                  | Ordinal 1 _, Ordinal 1 _ => a22 
                  | Ordinal 1 _, Ordinal 2 _ => a23 
                  | Ordinal 2 _, Ordinal 0 _ => a31 
                  | Ordinal 2 _, Ordinal 1 _ => a32 
                  | Ordinal 2 _, Ordinal 2 _ => a33 
                  | _,_ => A0 
                  end).
  Definition mk_mat_2_2 (a11 a12 a21 a22 : A) : mat 2 2 :=
    matrix_of_fun_def 
      (fun i j => match i,j with
                  | Ordinal 0 _, Ordinal 0 _ => a11 
                  | Ordinal 0 _, Ordinal 1 _ => a12 
                  | Ordinal 1 _, Ordinal 0 _ => a21 
                  | Ordinal 1 _, Ordinal 1 _ => a22 
                  | _,_ => A0 
                  end).

  (** Zero matrix *)
  Definition mat0 r c : mat r c
    := matrix_of_fun_def (fun i j => A0).

  (** A matrix is a nonzero matrix *)
  Definition matnonzero {r c} (m : mat r c) : Prop := m <> mat0 r c.

  (** Unit matrix *)
  Definition mat1 n : mat n n :=
    matrix_of_fun_def (fun i j => if (i == j) then A1 else A0).

  (** Mapping of a matrix *)
  Definition mmap {r c} (f : A -> A) (m : mat r c) : mat r c :=
    matrix_of_fun_def (fun i j => f (m i j)).

  (** Mapping of two matrices *)
  Definition mmap2 {r c} (f : A -> A -> A) (m1  m2 : mat r c) : mat r c :=
    matrix_of_fun_def (fun i j => f (m1 i j) (m2 i j)).

  Lemma mmap2_comm : forall {r c} (f : A -> A -> A)
                            (f_comm : forall a b : A, f a b = f b a)
                            (m1 m2 : mat r c), 
      mmap2 f m1 m2 = mmap2 f m2 m1.
  Proof.
    intros.
  Admitted.

  Lemma mmap2_assoc : forall {r c} (f : A -> A -> A)
                             (f_assoc : forall a b c, f a (f b c) = f (f a b) c)
                             (m1 m2 m3 : mat r c), 
      mmap2 f (mmap2 f m1 m2) m3 = mmap2 f m1 (mmap2 f m2 m3).
  Proof.
    intros.
  Admitted.

  (** Addition of matrix *)
  Definition madd {r c} (m1 m2 : mat r c) :=
    matrix_of_fun_def (fun i j => Aadd (m1 i j) (m2 i j)).
  Notation "m1 + m2" := (madd m1 m2) : mat_scope.

  Lemma madd_comm : forall {r c} (m1 m2 : mat r c), m1 + m2 = m2 + m1.
  Proof.
  Admitted.

  Lemma madd_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) + m3 = m1 + (m2 + m3).
  Proof.
  Admitted.

  Lemma madd_0_l : forall {r c} (m : mat r c), (mat0 r c) + m = m.
  Proof.
  Admitted.

  Lemma madd_0_r : forall {r c} (m : mat r c), m + (mat0 r c) = m.
  Proof.
  Admitted.

  (** Opposite of matrix *)
  Definition mopp {r c} (m : mat r c) : mat r c :=
    matrix_of_fun_def (fun i j => Aopp (m i j)).
  Notation "- m" := (mopp m) : mat_scope.

  Lemma mopp_opp : forall {r c} (m : mat r c), - - m = m.
  Proof.
  Admitted.

  Lemma mopp_exchange : forall {r c} (m1 m2 : mat r c), -m1 = m2 <-> m1 = -m2.
  Proof.
  Admitted.

  Lemma mopp_mat0 : forall {r c}, - (mat0 r c) = mat0 r c.
  Proof.
  Admitted.

  Lemma madd_opp : forall {r c} (m : mat r c), m + (-m) = mat0 r c.
  Proof.
  Admitted.

  Definition msub {r c} (m1 m2 : mat r c) :=
    matrix_of_fun_def (fun i j => Aadd (m1 i j) (Aopp (m2 i j))).
  Infix "-" := msub : mat_scope.

  Lemma msub_comm : forall {r c} (m1 m2 : mat r c), m1 - m2 = - (m2 - m1).
  Proof.
  Admitted.

  Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c), 
      (m1 - m2) - m3 = m1 - (m2 + m3).
  Proof.
  Admitted.

  Lemma msub_0_l : forall {r c} (m : mat r c), (mat0 r c) - m = - m.
  Proof.
  Admitted.

  Lemma msub_0_r : forall {r c} (m : mat r c), m - (mat0 r c) = m.
  Proof.
  Admitted.

  Lemma msub_self : forall {r c} (m : mat r c), m - m = (mat0 r c).
  Proof.
  Admitted.

  (** 矩阵数乘 *)
  Definition mcmul {r c} (a : A) (m : mat r c) : mat r c :=
    matrix_of_fun_def (fun i j => Amul a (m i j)).

  Notation "a c* m" := (mcmul a m) : mat_scope.

  Definition mmulc {r c} (m : mat r c) (a : A) : mat r c :=
    matrix_of_fun_def (fun i j => Amul (m i j) a).

  Notation "m *c a" := (mmulc m a) : mat_scope.

  Lemma mmulc_eq_mcmul : forall {r c} (a : A) (m : mat r c),  m *c a = a c* m.
  Proof.
  Admitted.

  Lemma mcmul_assoc : forall {r c} (a b : A) (m : mat r c), a c* (b c* m) = (a * b) c* m.
  Proof.
  Admitted.

  Lemma mcmul_perm : forall {r c} (a b : A) (m : mat r c), a c* (b c* m) = b c* (a c* m).
  Proof.
  Admitted.

  Lemma mcmul_add_distr_l : forall {r c} (a : A) (m1 m2 : mat r c), 
      a c* (m1 + m2) = (a c* m1) + (a c* m2).
  Proof.
  Admitted.

  Lemma mcmul_add_distr_r : forall {r c} (a b : A) (m : mat r c),
      (a + b)%A c* m = a c* m + b c* m.
  Proof.
  Admitted.

  (* 0 c* m = mat0 *)
  Lemma mcmul_0_l : forall {r c} (m : mat r c), A0 c* m = mat0 r c.
  Proof.
  Admitted.

  (* 1 * m = m *)
  Lemma mcmul_1_l : forall {r c} (m : mat r c), A1 c* m = m.
  Proof.
  Admitted.

  (* (-a) * m = - (a * m) *)
  Lemma mcmul_neg : forall {r c} a (m : mat r c), (- a)%A c* m = - (a c* m).
  Proof.
  Admitted.

  (* (-a) * (- m) = (a * m) *)
  Lemma mcmul_neg_mopp : forall {r c} a (m : mat r c), (-a)%A c* (-m) = a c* m.
  Proof.
  Admitted.

  (* a * m = m -> a = 1 \/ m = 0 *)
  Lemma mcmul_same_imply_coef1_or_mzero : forall {r c} a (m : mat r c),
      a c* m = m -> (a = A1) \/ (m = mat0 r c).
  Proof.
  Abort.

  (* m1 <> 0 -> m2 <> 0 -> m1 = k c* m2 -> k <> 0 *)
  Lemma mat_eq_mcmul_implfy_coef_neq0 : forall {r c} (m1 m2 : mat r c) k,
      matnonzero m1 -> matnonzero m2 -> (m1 = k c* m2) -> k <> A0.
  Proof.
  Abort.

  (* m <> 0 -> k c* m = 0 -> k = 0 *)
  Lemma mcmul_mnonzero_eq0_imply_k0 : forall {r c} (m : mat r c) k,
      matnonzero m -> mat0 r c = k c* m -> k = A0.
  Proof.
  Abort.

  (** transpose *)
  Definition mtrans {r c} (m : mat r c): mat c r :=
    matrix_of_fun_def (fun i j => m j i).

  Notation "m \T" := (mtrans m) : mat_scope.

  Lemma mtrans_trans : forall {r c} (m : mat r c), m \T \T = m.
  Proof.
  Admitted.

  (** 矩阵乘法 *)
  Definition mmul {r c s} (m1 : mat r c) (m2 : mat c s) : mat r s :=
    @mulmx A_ringType r c s m1 m2.
  Infix "*" := mmul : mat_scope.

  Lemma mmul_add_distr_l : forall {r c A} (m1 : mat r c) (m2 m3 : mat c A),
      m1 * (m2 + m3) = m1 * m2 + m1 * m3.
  Proof.
  Admitted.

  Lemma mmul_add_distr_r : forall {r c s} (m1 m2 : mat r c) (m3 : mat c s),
      (m1 + m2) * m3 = (m1 * m3) + (m2 * m3).
  Proof.
  Admitted.

  Lemma mmul_assoc : forall {r c s A} (m1 : mat r c) (m2 : mat c s) (m3 : mat s A),
      (m1 * m2) * m3 = m1 * (m2 * m3).
  Proof. intros. apply Logic.eq_sym. apply mulmxA. Qed.

  Lemma mmul_0_l : forall {r c A} (m : mat c A), (mat0 r c) * m = mat0 r A.
  Proof.
  Admitted.

  Lemma mmul_0_r : forall {r c A} (m : mat r c), m * (mat0 c A) = mat0 r A.
  Proof.
  Admitted.

  Lemma mmul_1_l : forall {r c} (m : mat r c), (mat1 r) * m = m.
  Proof.
  Admitted.

  Lemma mmul_1_r : forall {r c} (m : mat r c), m * (mat1 c) = m.
  Proof.
  Admitted.

  (*   (** Vector type *)
  Definition vecr n := mat 1 n.
  Definition vecc n := mat n 1.
  
  (** ** Construct a matrix with a vector and a a matrix *)
  
  (** Construct by row *)
  Definition mconsr {r c} (v : vecr c) (m : mat r c) : mat (S r) c.
  Proof.
    destruct v,m.
    refine (mk_mat ((hd [] mat_data) :: mat_data0) _ _).
    - simpl. f_equal. auto.
    - simpl. split; auto.
      destruct mat_data; simpl in *; try lia.
  Defined.
  
  (** Construct by column *)
  Definition mconsc {r c} (v : vecc r) (m : mat r c) : mat r (S c).
  Proof.
    destruct v as [v], m as [m].
    refine (mk_mat (consc (hdc A0 v) m) _ _).
    - apply consc_height; auto. rewrite hdc_length; auto.
    - apply consc_width; auto. rewrite hdc_length; subst; auto.
  Defined. *)

  (** list list to matrix *)

  (* Definition l2m_old {r c} (dl : list (list A)) (H1 : length dl = r) *)
  (*   (H2 : width dl c) : mat r c := mk_mat dl H1 H2. *)

  Definition l2m {r c} (dl : list (list A)) : mat r c.
  Proof.
    (* destruct (ri <? r) eqn:H1, (ci <? c) eqn:H2. *)
    (* { apply mathcomp_leq_iff_ltb in H1,H2. *)
    (*   pose (ri' := @Ordinal r ri H1). *)
    (*   pose (ci' := @Ordinal c ci H2). *)
    (*   exact (m ri' ci'). } *)
    (*   all: exact A0. *)
    (* Defined. *)
    (* matrix_of_fun_def (fun i j => *)
    (*                      match  *)
    (*                        dlnth Amul (m i j) a). *)
    apply (matrix_of_fun_def (fun i j => A0)).
  Defined.

  (* Learn finfun_on *)
  Section check_finfun_on.
    Variable r c : nat.
    Let fin_r_c_T := prod_finType (ordinal_finType r) (ordinal_finType c).
    
    (* it's complex form *)
  (*     Check @finfun_on fin_r_c_T (fun _ : 'I_r * 'I_c => A)
      (@enum_mem fin_r_c_T
        (@mem ('I_r * 'I_c) (predPredType ('I_r * 'I_c))
          (@PredOfSimpl.coerce ('I_r * 'I_c) (pred_of_argType ('I_r * 'I_c))))).
    
    (* simple form, benefit from type inference *)
    Check finfun_on (fun _ : 'I_r * 'I_c => A)
      (enum_mem (mem (PredOfSimpl.coerce (pred_of_argType ('I_r * 'I_c))))). *)
  End check_finfun_on.

  (** convert "finfun_on" to "list (list A)" *)
  Definition finfun_on_to_dlist (r c : nat)
    (f : finfun_on (fun _ : 'I_r * 'I_c => A)
           (enum_mem (mem (PredOfSimpl.coerce (pred_of_argType ('I_r * 'I_c))))))
    : list (list A) :=
    match f with
    | finfun_nil => []
    | finfun_cons _ _ _ _ => []
    end.

  Definition m2l {r c} (m : mat r c) : list (list A).
  Proof.
    destruct m. destruct f.
    apply (finfun_on_to_dlist r c f).
  Defined.

  Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
  Proof.
  Admitted.

  Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
  Proof.
  Admitted.

  Lemma m2l_l2m_id : forall {r c} (dl : list (list A)) (H1 : length dl = r)
                            (H2 : width dl c), @m2l r c (l2m dl) = dl.
  Proof.
  Admitted.

  Lemma l2m_m2l_id : forall {r c} (m : mat r c), l2m (m2l m) = m. 
  Proof.
  Admitted.

  Lemma l2m_inj : forall {r c} (d1 d2 : list (list A)),
      length d1 = r -> width d1 c -> 
      length d2 = r -> width d2 c -> 
      d1 <> d2 -> @l2m r c d1 <> l2m d2.
  Proof.
  Admitted.

  Lemma l2m_surj : forall {r c} (m : mat r c), 
      (exists d, l2m d = m).
  Proof.
  Admitted.

  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c),
      m1 <> m2 -> m2l m1 <> m2l m2.
  Proof.
  Admitted.

  Lemma m2l_surj : forall {r c} (d : list (list A)), 
      length d = r -> width d c -> 
      (exists m, @m2l r c m = d).
  Proof.
  Admitted.

  (** ** Other OPs and PROPs *)

  (** Convert between tuples and matrix *)

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
  Definition m2t_3x3 (m : mat 3 3) : @T_3x3 A :=
    ((mnth m 0 0, mnth m 0 1, mnth m 0 2), 
      (mnth m 1 0, mnth m 1 1, mnth m 1 2),
      (mnth m 2 0, mnth m 2 1, mnth m 2 2)).
  (*      
  Definition m2t_3x3 (m : mat 3 3) : @T_3x3 A.
    destruct m. rename mat_data into dl.
    remember (hd [] dl) as l1.
    remember (hd [] (tl dl)) as l2.
    remember (hd [] (tl (tl dl))) as l3.
    remember (hd A0 l1, hd A0 (tl l1), hd A0 (tl (tl l1))) as t1.
    remember (hd A0 l2, hd A0 (tl l2), hd A0 (tl (tl l2))) as t2.
    remember (hd A0 l3, hd A0 (tl l3), hd A0 (tl (tl l3))) as t3.
    exact (t1, t2, t3).
  Defined.
   *)  

  Lemma m2t_t2m_id_3x3 : forall (x : @T_3x3 A), m2t_3x3 (t2m_3x3 x) = x.
  (*     Proof.
    destruct x as ((t1,t2),t3).
    destruct t1 as ((a11,a12),a13).
    destruct t2 as ((a21,a22),a23).
    destruct t3 as ((a31,a32),a33).
    simpl. auto.
  Qed. *)
  Admitted.

  (*   Lemma t2m_m2t_id_3x3 (m : mat 3 3) : t2m_3x3 (m2t_3x3 m) = m.
    Proof.
    unfold t2m_3x3, m2t_3x3. unfold mk_mat_3_3.
    intros ri ci Hi Hj.
    do 3 (destruct ri; [do 3 (destruct ci; auto); lia | idtac]). lia.
  Qed.
  Admitted. *)
  Lemma t2m_m2t_id_3x3 : forall (m : mat 3 3),
      t2m_3x3 (m2t_3x3 m) = m.
  Proof.
  Admitted.

  (** m[0,0] : mat_1x1 -> A *)
  Definition scalar_of_mat (m : mat 1 1) := mnth m 0 0.

End FinFunMatrix.
