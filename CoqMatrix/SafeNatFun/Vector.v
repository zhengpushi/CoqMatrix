(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector Theory implemented with SafeNatFun (no Module)
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. This is safe version of NatFun, which corrected the shape problem
 *)


Require Export SafeNatFun.Matrix.


Generalizable Variable A B C Aeq Beq Ceq Aadd Aopp Amul Ainv.

(** Control the scope *)
Open Scope nat_scope.
Open Scope A_scope.
Open Scope mat_scope.
Open Scope vec_scope.

(* ######################################################################### *)
(** * Basic vector theory *)

Section basic_vectory_theory.
  
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0:A}.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.

  (** Vector type *)
  Definition vec n := @mat A n 1.

  (** make a vector by a function *)
  Definition mk_vec {n : nat} (f : nat -> A) : vec n :=
    mk_mat (fun i j => if j =? 0 then f i else A0).

  (** matrix equality *)
  Definition veq {n} (v1 v2 : vec n) := meq (Aeq:=Aeq) v1 v2.
  Infix "==" := veq : vec_scope.

  Notation "m ! i ! j " := (mnth (A0:=A0) m i j) : mat_scope.

  (** veq is equivalence relation *)
  Lemma veq_equiv : forall n, Equivalence (veq (n:=n)).
  Proof.
    intros. unfold veq. unfold meq.
    apply meq_equiv.
  Qed.

  (** Get element of vector (unsafe) *)
  Notation "v $ i " := (matf v i 0) : vec_scope.
  
  (** Get element of vector (safe) *)
  Definition vnth {n} (v : vec n) i : A := v!i!0.
  Notation "v ! i " := (vnth v i) : vec_scope.

  Lemma vnth_eq_vnth_raw : forall {n : nat} (v : vec n),
      (forall i, i < n -> v!i == v$i)%A.
  Proof.
    intros. unfold vnth. apply mnth_eq_mnth_raw; auto.
  Qed.

  (** veq and mnth should satisfy this constraint *)
  Lemma veq_iff_vnth : forall {n : nat} (v1 v2 : vec n),
      (v1 == v2) <-> (forall i, i < n -> (v1!i == v2!i)%A).
  Proof.
    unfold veq, vec, vnth.
    intros;  split; intros.
    - rewrite (meq_iff_mnth (A0:=A0)) in H. apply H; auto.
    - apply (meq_iff_mnth (A0:=A0)). intros.
      assert (j = 0) by lia. rewrite H2. apply H. auto.
  Qed.

  (* ==================================== *)
  (** ** List like operations for vector *)

  (** vcons *)
  Definition vcons {n} (a : A) (v : vec n) : vec (S n) :=
    mk_vec (fun i => match i with 0 => a | S i' => v $ i' end).

  Lemma vcons_spec : forall n a (v : vec n) i,
      ((vcons a v) $ 0 == a)%A /\ (i < n -> v $ i == (vcons a v) $ (S i))%A.
  Proof.
    intros. unfold vcons. split.
    - intros. solve_mnth.
    - solve_mnth.
  Qed.
    

  (** Get a vector from a given vector by remove one element *)
  Definition vremove {n : nat} (v : vec (S n)) (k : nat) : vec n :=
    mk_vec (fun i => if i <? k then v ! i else v ! (S i)).


  (* ==================================== *)
  (** ** Convert between list and vector *)
  (* Definition v2l {n} (v : vec n) : list A := @Matrix.mcol _ n 1 0 v. *)
  (* Definition l2v {n} (l : list A) : vec n := l2m (A0:=A0) (row2col l). *)

  Definition v2l {n} (v : vec n) : list A := map (fun i : nat => v $ i) (seq 0 n).

  Definition l2v n (l : list A) : vec n :=
    mk_mat (fun i j => if (i <? n) && (j =? 0) then nth i l A0 else A0).

  (** list of vector to dlist *)
  Definition vl2dl {n} (l : list (vec n)) : list (list A) :=
    map v2l l.
    

  Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
  Proof.
    intros. unfold v2l. rewrite map_length, seq_length; auto.
  Qed.

  Lemma v2l_l2v_id : forall {n} (l : list A),
      length l = n -> (@v2l n (@l2v n l) == l)%list.
  Proof.
    intros. unfold l2v,v2l. simpl.
    rewrite (list_eq_iff_nth A0 n); auto.
    - intros. rewrite ?nth_map_seq; auto.
      rewrite ?Nat.add_0_r. apply Nat.ltb_lt in H0. rewrite H0; simpl. easy.
    - rewrite map_length, seq_length; auto.
  Qed.

  Lemma l2v_v2l_id : forall {n} (v : vec n), l2v n (v2l v) == v.
  Proof.
    intros. destruct v as [v].
    unfold l2v,v2l. simpl. lma.
    rewrite ?nth_map_seq; auto.
    rewrite Nat.add_0_r. easy.
  Qed. 

  (* ==================================== *)
  (** ** Make concrete vector *)
  Definition mk_vec2 (a0 a1 : A) : vec 2 := l2v 2 [a0;a1].
  Definition mk_vec3 (a0 a1 a2 : A) : vec 3 := l2v 3 [a0;a1;a2].
  Definition mk_vec4 (a0 a1 a2 a3 : A) : vec 4 := l2v 4 [a0;a1;a2;a3].

  (* ==================================== *)
  (** ** Convert between tuples and vector *)
  Definition t2v_2 (t : @T2 A) : vec 2 :=
    let '(a,b) := t in l2v 2 [a;b].
  Definition t2v_3 (t : @T3 A) : vec 3 :=
    let '(a,b,c) := t in l2v 3 [a;b;c].
  Definition t2v_4 (t : @T4 A) : vec 4 :=
    let '(a,b,c,d) := t in l2v 4 [a;b;c;d].

  Definition v2t_2 (v : vec 2) : @T2 A := (v$0, v$1).
  Definition v2t_3 (v : vec 3) : @T3 A := (v$0, v$1, v$2).
  Definition v2t_4 (v : vec 4) : @T4 A := (v$0, v$1, v$2, v$3).

  Lemma v2t_t2v_id_2 : forall (t : A * A), v2t_2 (t2v_2 t) = t.
  Proof.
    intros. destruct t. simpl. unfold v2t_2. f_equal.
  Qed.

  Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v.
  Proof.
    intros. apply veq_iff_vnth. intros i Hi. simpl.
    repeat (try destruct i; auto; try lia); easy.
  Qed.

  (** mapping of a vector *)
  Definition vmap {n} (v : vec n) f : vec n := mmap f v.

  (** folding of a vector *)
  (*   Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)

  (** mapping of two matrices *)
  Definition vmap2 {n} (v1 v2 : vec n) f : vec n := mmap2 f v1 v2.

  (* ======================================================================= *)
  (** ** Advanced matrix construction by mixing vectors and matrices *)
  Section AdvancedConstrtuct.

    (* Check A. *)
    (* Check Equiv_Aeq. *)
    (* Context `{Equiv_Aeq : Equivalence A Aeq} {A0 A1 : A}. *)
    (* Infix "==" := (meq (Aeq:=Aeq)) : mat_scope. *)

    (* (** Vector type *) *)
    (* Definition vecr n := @mat A 1 n. *)
    (* Definition vecc n := @mat A n 1. *)
    
    (** Construct a matrix with a vector and a matrix by row *)
    Definition mconsr {r c} (v : vec c) (m : mat r c) : mat (S r) c :=
      mk_mat (fun i j => match i with
                         | O => v $ j
                         | S i' => m $ i' $ j
                         end).
    
    (** Construct a matrix with a vector and a matrix by column *)
    Definition mconsc {r c} (v : vec r) (m : mat r c) : mat r (S c) :=
      mk_mat (fun i j => match j with
                         | O => v $ i
                         | S j' => m $ i $ j'
                         end).
    
    (* (** Equality of two forms of ConstructByRow *) *)
    (* Lemma mconsr_eq {r c} (v : vecr c) (m : @mat A r c) : mconsr v m == (v, m). *)
    (* Proof. unfold mconsr. auto. Qed. *)
    
    (* (** Construct a matrix by rows with the matrix which row number is 0 *) *)
    (* Lemma mconsr_mr0 : forall {n} (v : @vec A n) (m : @mat A 0 n), *)
    (*   mconsr v m = [v]. *)
    (* Proof. intros. destruct m. unfold mconsr. auto. Qed. *)
    
    (* (** Construct a matrix by rows with the matrix which row column is 0 *) *)
    (* Lemma mconsr_mc0 : forall {n} (v : @vec A 0) (m : @mat A n 0), *)
    (*   mconsr v m = (tt, m). *)
    (* Proof. intros. destruct v. unfold mconsr. auto. Qed. *)
    
    (* (** Construct a matrix by columns with the matrix which row number is 0 *) *)
    (* Lemma mconsc_mr0 : forall {n} (v : @vec A 0) (m : @vec (@vec A n) 0), *)
    (*   mconsc v m = tt. *)
    (* Proof. intros. destruct m. unfold mconsc. auto. Qed.   *)

  End AdvancedConstrtuct.

End basic_vectory_theory.
Arguments l2v {A}.
Notation "v $ i " := (matf v i 0) : vec_scope.

Section test.
  Notation "v ! i " := (vnth (A0:=0) v i) : vec_scope.
  Definition v1 : vec 3 := l2v 0 3 [1;2;3].
  Definition m1 : mat 3 3 := l2m (A0:=0) [[10;11;12];[13;14;15];[16;17;18]].
  Goal v1!(v1!0) = 2. auto. Qed.
  Goal m2l (mconsr v1 m1) = [[1;2;3];[10;11;12];[13;14;15];[16;17;18]]. auto. Qed.
  Goal m2l (mconsc v1 m1) = [[1;10;11;12];[2;13;14;15];[3;16;17;18]]. auto. Qed.
End test.


(* ######################################################################### *)
(** * Ring vector theory implemented with SafeNatFun *)

Section ring_vector_theory.

  Context `{AG : AGroup}.
  Infix "+" := Aadd : A_scope.
  Infix "+" := (ladd (Aadd:=Aadd)) : list_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := (fun a b => a + (-b)) : A_scope.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.

  (** ** Zero vector *)
  Definition vec0 {n} : vec n := mat0 A0 n 1.

  (** Assert that a vector is an zero vector. *)
  Definition vzero {n} (v : vec n) : Prop := v == vec0.

  (** Assert that a vector is an non-zero vector. *)
  Definition vnonzero {n} (v : vec n) : Prop := ~(vzero v).
  
  (** vec0 is equal to mat0 with column 1 *)
  Lemma vec0_eq_mat0 : forall n, vec0 == mat0 A0 n 1.
  Proof.
    intros. easy.
  Qed.
  
  
  (** *** Vector addition *)

  Definition vadd {n} (v1 v2 : vec n) : vec n := madd (Aadd:=Aadd) v1 v2.
  Infix "+" := vadd : vec_scope.

  (** v1 + v2 = v2 + v1 *)
  Lemma vadd_comm : forall {n} (v1 v2 : vec n), (v1 + v2) == (v2 + v1).
  Proof.
    intros. apply madd_comm.
  Qed.

  (** (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma vadd_assoc : forall {n} (v1 v2 v3 : vec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof.
    intros. apply madd_assoc.
  Qed.

  (** vec0 + v = v *)
  Lemma vadd_0_l : forall {n} (v : vec n), vec0 + v == v.
  Proof.
    intros. apply madd_0_l.
  Qed.

  (** v + vec0 = v *)
  Lemma vadd_0_r : forall {n} (v : vec n), v + vec0 == v.
  Proof.
    intros. apply madd_0_r.
  Qed.

  
  (** *** Vector opposite *)
  
  Definition vopp {n} (v : vec n) : vec n := mopp (Aopp:=Aopp) v.
  Notation "- v" := (vopp v) : vec_scope.

  (** v + (- v) = vec0 *)
  Lemma vadd_opp : forall {n} (v : vec n), v + (- v) == vec0.
  Proof.
    intros. apply madd_opp.
  Qed.
  

  (** *** Vector subtraction *)

  Definition vsub {n} (v1 v2 : vec n) : vec n := v1 + (- v2).
  Infix "-" := vsub : vec_scope.


  (** *** Below, we need a ring structure *)
  Context `{R : Ring A Aadd A0 Aopp Amul A1 Aeq}.
  Infix "*" := Amul : A_scope.
  
  Add Ring ring_inst : make_ring_theory.

  (** *** Vector scalar multiplication *)

  Definition vcmul {n} a (v : vec n) : vec n := mcmul (Amul:=Amul) a v.
  Definition vmulc {n} (v : vec n) a : vec n := mmulc (Amul:=Amul) v a.
  Infix "c*" := vcmul : vec_scope.
  Infix "*c" := vmulc : vec_scope.

  (** v *c a = a c* v *)
  Lemma vmulc_eq_vcmul : forall {n} a (v : vec n), (v *c a) == (a c* v).
  Proof.
    intros. apply mmulc_eq_mcmul.
  Qed.

  (** a c* (b c* v) = (a * b) c* v *)
  Lemma vcmul_assoc : forall {n} a b (v : vec n), a c* (b c* v) == (a * b)%A c* v.
  Proof.
    intros. apply mcmul_assoc.
  Qed.

  (** a c* (b c* v) = b c* (a c* v) *)
  Lemma vcmul_perm : forall {n} a b (v : vec n), a c* (b c* v) == b c* (a c* v).
  Proof.
    intros. apply mcmul_perm.
  Qed.

  (** (a + b) c* v = (a c* v) + (b c* v) *)
  Lemma vcmul_add_distr_l : forall {n} a b (v : vec n),
      (a + b)%A c* v == (a c* v) + (b c* v).
  Proof.
    intros. apply mcmul_add_distr_r.
  Qed.

  (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
  Lemma vcmul_add_distr_r : forall {n} a (v1 v2 : vec n), 
      a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof.
    intros. apply mcmul_add_distr_l.
  Qed.

  (** 1 c* v = v *)
  Lemma vcmul_1_l : forall {n} (v : vec n), A1 c* v == v.
  Proof.
    intros. apply mcmul_1_l.
  Qed.

  (** 0 c* v = vec0 *)
  Lemma vcmul_0_l : forall {n} (v : vec n), A0 c* v == vec0.
  Proof.
    intros. apply mcmul_0_l.
  Qed.

  
  (** *** Vector dot product *)
  
  (** dot production of two vectors. *)
  Definition vdot {n : nat} (v1 v2 : vec n) : A :=
    fold_left Aadd (map (fun i => v1$i * v2$i) (seq 0 n)) A0.
  
  Infix "⋅" := vdot : vec_scope.

  (** vdot is a proper morphism respect to Aeq *)
  Lemma vdot_aeq_mor {n} :
    Proper (veq (Aeq:=Aeq) ==> veq (Aeq:=Aeq) ==> Aeq) (@vdot n).
  Proof.
    repeat (hnf; intros).
    apply fold_left_aeq_mor; try easy.
    rewrite (veq_iff_vnth (A0:=A0)) in H,H0.
    rewrite (list_eq_iff_nth A0 n); auto.
    - intros. rewrite !nth_map_seq; auto.
      rewrite Nat.add_0_r. rewrite <- ?(vnth_eq_vnth_raw (A0:=A0)); auto.
      rewrite H,H0; auto. easy.
    - rewrite map_length, seq_length; auto.
    - rewrite map_length, seq_length; auto.
  Qed.
  Global Existing Instance vdot_aeq_mor.

  (** dot production is commutative *)
  Lemma vdot_comm : forall {n} (v1 v2 : vec n), (v1 ⋅ v2 == v2 ⋅ v1)%A.
  Proof.
    intros. unfold vdot.
    apply fold_left_aeq_mor; try easy.
    apply SetoidListExt.map_ext. intros. ring.
  Qed.

  (** 0 * v = 0 *)
  Lemma vdot_0_l : forall {n} (v : vec n), (vec0 ⋅ v == A0)%A.
  Proof.
    intros.
    unfold vdot. cbn.
    destruct v as [v]; simpl.
    assert (map (fun i => A0 * v i 0) (seq 0 n) == map (fun i => A0) (seq 0 n))%list.
    { apply SetoidListExt.map_ext. intros. ring. }
    rewrite H. clear H.
    induction n; simpl; try easy.
    rewrite <- seq_shift. rewrite map_map. monoid_rw. auto.
  Qed.

  (** v * 0 = 0 *)
  Lemma vdot_0_r : forall {n} (v : vec n), (v ⋅ vec0 == A0)%A.
  Proof. intros. rewrite vdot_comm, vdot_0_l. easy. Qed.

End ring_vector_theory.

Section test.
  Import ZArith.
  Open Scope Z_scope.
  Open Scope vec_scope.
  
  Infix "+" := (vadd (Aadd:=Z.add)) : vec_scope.
  Notation "- v" := (vopp (Aopp:=Z.opp) v) : vec_scope.
  Infix "-" := (vsub (Aadd:=Z.add)(Aopp:=Z.opp)) : vec_scope.
  Infix "c*" := (vcmul (Amul:=Z.mul)) : vec_scope.
  Infix "⋅" := (vdot (A0:=0) (Aadd:=Z.add) (Amul:=Z.mul)) : vec_scope.

  Let v1 := l2v 0 3 [1;2;3].
  Let v2 := l2v 0 3 [4;5;6].
  (* Compute v2l (-v1). *)
  (* Compute v2l (v1 + v2). *)
  (* Compute v2l (v2 - v1). *)
  (* Compute v2l (3 c* v1). *)
  (* Compute v1⋅v2. *)

End test.



(* ######################################################################### *)
(** * Decidable-field vector theory implemented with SafeNatFun  *)

Section decidable_vector_theory.

  Context `{Dec_Aeq : @Decidable A Aeq} {A0:A}.
  
  Open Scope mat_scope.
  Open Scope vec_scope.

  (** veq is decidable *)
  Lemma veq_dec : forall (n : nat), Decidable (@veq A Aeq n).
  Proof. intros. apply meq_dec. Qed.

  Global Existing Instance veq_dec.

  (** It is decidable that if a vector is zero vector. *)
  Lemma vzero_dec : forall {n} (v : vec n),
      {vzero (A0:=A0)(Aeq:=Aeq) v} + {vnonzero (A0:=A0)(Aeq:=Aeq) v}.
  Proof.
    intros. apply veq_dec.
  Qed.
  
End decidable_vector_theory.


(** ** Others, later ... *)
(* 

  Lemma vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : V n) k,
    vnonzero v1 -> vnonzero v2 -> v1 = k c* v2 -> k <> X0.
  Proof.
    intros. intro. subst. rewrite vcmul_0_l in H. destruct H. easy.
  Qed.
  
  (* ==================================== *)
  (** ** 2-dim vector operations *)

  Definition vlen2 (v : V 2) : X :=
    let '(x,y) := v2t_2 v in
      (x * x + y * y)%X.
  
  (* ==================================== *)
  (** ** 3-dim vector operations *)

  Definition vlen3 (v : V 3) : X :=
    let '(x,y,z) := v2t_3 v in
      (x * x + y * y + z * z)%X.
      
  Definition vdot3 (v0 v1 : V 3) : X :=
    let '(a0,b0,c0) := v2t_3 v0 in
    let '(a1,b1,c1) := v2t_3 v1 in
      (a0 * a1 + b0 * b1 + c0 * c1)%X.
 *)
