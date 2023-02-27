(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with many new models.
  author    : ZhengPu Shi
  date      : 2021.12

  remark    :
  1. use sig in Coq, this is also called sub-type or refinement type
     Definition vec {A:Type} (n:nat) := {l : list A | length l = n}.

  2. use finite set as index of a function. (use Ordinal in MC project)
     Inductive ordinal (n:nat) := Ordinal (m:nat) (H:m<n).
     Definition vec {A:Type} (n:nat) := ordinal n -> A.
  
  3. use Fin.t in Coq as index of a function.
     Inductive fin (n:nat) : Set :=
     | F1 
     | FS (f : fin n) : fin (S n).
     Definition vec {A:Type} (n:nat) := fin n -> A.
 *)


Require Export MatrixTheory.

(* ######################################################################### *)
(** * Basic matrix theory implemented with NEW *)

(** Lots of models *)


(** Refinement type *)
(** About "refinement type",
    1. a video by ZhanBoHua naming "Refinement Type" introduced this concept,
       which can be fined by keyword "type system" in bilibili.com.
    2. it is a bit like dependent type.
    3. it is subtype also.
       then, what's the difference of "sub-type" and "refinement type"?
    4. it is sig or ex in Coq 
*)

Module BasicMatrixTheoryMA (E : ElementType) <: BasicMatrixTheory E.

  (** vector *)
  Section vec.
    Context {A : Type} {Aeq : relation A} {A0 : A}.
    Context `{Equiv_Aeq : Equivalence A Aeq}.
    Infix "==" := Aeq : A_scope.
    Infix "==" := (eqlistA Aeq) : list_scope.

    Open Scope nat_scope.
    Open Scope A_scope.
    Open Scope list_scope.
    Open Scope vec_scope.
    
    (** vec *)
    Definition vec (n : nat) : Type := {l : list A | length l = n}.

    (** vector given by repeatig an element *)
    Definition vconst {n} (a : A) : vec n.
      refine (exist _ (repeat a n) (repeat_length _ _)).
    Defined.

    (** vec of all A0 *)
    Definition vec0 {n} : vec n := vconst A0.

    (** vec to list *)
    Definition v2l {n : nat} (v : vec n) := proj1_sig v.

    (** vector equal *)
    Definition veq {n : nat} (v1 v2 : vec n) : Prop := v2l v1 == v2l v2.
    Infix "==" := veq : vec_scope.

    (** v2l is a proper morphism *)
    Lemma v2l_aeq_mor : forall n: nat,
        Proper ((veq (n:=n)) ==> (eqlistA Aeq)) v2l.
    Proof.
      intros. hnf. intros. apply H.
    Qed.
    Global Existing Instance v2l_aeq_mor.

    (** veq iff list eq *)
    Lemma veq_iff_list_eq : forall {n} (v1 v2 : vec n), v1 == v2 <-> (v2l v1 == v2l v2)%list.
    Proof.
      intros. easy.
    Qed.

    (** simplify a equation of veq *)
    Ltac veq_simpl :=
      intros;
      (* destruct all vec to a list and a proposition of its length equation *)
      repeat match goal with
        | v : vec _ |- _ => destruct v as [?v ?Hv]
        end;
      (* convert veq to list equal, thus the veq equation will be dropped *)
      repeat match goal with
        | H: veq ?v1 ?v2 |- _ => rewrite veq_iff_list_eq in H
        | |- veq _ _ => apply veq_iff_list_eq
        end;
      (* simplify *)
      simpl in *;
      (* try to solve *)
      try easy.

    Lemma veq_equiv : forall {n}, Equivalence (veq (n:=n)).
    Proof.
      intros. constructor; hnf; veq_simpl. rewrite H; auto.
    Qed.
    Global Existing Instance veq_equiv.

    (** Get n-th element of a vector *)  
    Definition vnth {n} (v : vec n) (i : nat) : A := nth i (v2l v) A0.

    (* Lemma vnth_iff_nth : forall {n} (v1 v2 : vec n) i, *)
    (*     ((vnth v1 i == vnth v2 i) <-> (nth i (v2l v1) A0) == (nth i (v2l v2) A0))%A. *)
    (* Proof. *)
    (*   intros. unfold vnth; split; intros; auto. *)
    (* Qed. *)

    (** veq and vnth should satisfy this constraint *)
    Lemma veq_iff_vnth : forall {n : nat} (v1 v2 : vec n),
        v1 == v2 <-> (forall i, i < n -> (vnth v1 i == vnth v2 i)%A).
    Proof.
      intros. split; intros; unfold vnth in *; veq_simpl.
      - rewrite H. easy.
      - apply (list_eq_iff_nth A0 n v1 v2 Hv0 Hv). easy.
    Qed.

  End vec.

  Section vec_test.
    Open Scope nat.
    Definition v : vec 3 := exist _ [1; 2; 3] eq_refl.
    (* Compute v2l v. *)
    (* Compute vnth v 0. *)
  End vec_test.
  
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

  (** matrix type *)
  Definition mat (r c : nat) : Type := @vec (@vec A c) r.
    
  (** mat to dlist *)
  Definition m2l {r c : nat} (m : mat r c) : list (list A) := map v2l (v2l m).

  (** matrix equality *)

  (* method1 *)
  Definition meq {r c : nat} (m1 m2 : mat r c) : Prop := veq (Aeq:=veq (Aeq:=Aeq)) m1 m2.
  (* method2 *)
  Definition meq2 {r c : nat} (m1 m2 : mat r c) : Prop := (m2l m1 == m2l m2)%dlist.

  (* Lemma meq_iff_meq2 : forall {r c : nat} (m1 m2 : mat r c), meq m1 m2 <-> meq2 m1 m2. *)
  (* Proof. *)
  (*   intros. unfold meq,meq2,m2l,v2l,veq. *)
  (*   destruct m1 as [m1 Hm1], m2 as [m2 Hm2]. simpl. *)
  (*   split; intros. *)
  (*   - *)
  (*     apply (map_aeq_mor (Aeq:=veq (Aeq:=Aeq))); hnf. *)
  (*     intros. *)
  (*   2:{ *)
  (*     apply (map_eq_imply_eq (Aeq:=veq (Aeq:=Aeq))) in H. *)
  (*     rewrite H. *)
  (*     Abort. *)

  Global Infix "==" := meq : mat_scope.

  (** simplify a equation of veq *)
  Ltac veq_simpl :=
    intros;
    (* destruct all vec to a list and a proposition of its length equation *)
    repeat match goal with
      | v : vec _ |- _ => destruct v as [?v ?Hv]
      end;
    (* convert veq to list equal, meanwhile the veq equation will be dropped *)
    repeat match goal with
      | H: veq ?v1 ?v2 |- _ => rewrite veq_iff_list_eq in H
      | |- veq _ _ => apply veq_iff_list_eq
      end;
    (* simplify *)
    simpl in *;
    (* try to solve *)
    try easy.

  (** destruct mat in hypothesis *)
  Ltac mat_destr :=
    match goal with
    | m : mat _ _ |- _ => destruct m as [m Hm]
    end.

  (** simplify a equation of meq *)
  Ltac meq_simpl :=
    intros;
    repeat mat_destr;
    unfold meq in *;
    simpl in *;
    try easy.

  Lemma meq_equiv : forall {r c}, Equivalence (meq (r:=r) (c:=c)).
  Proof.
    intros. constructor; hnf; meq_simpl.
    rewrite H; auto.
  Qed.
  Global Existing Instance meq_equiv.

  (* (** meq iff dlist eq *) *)
  (* Lemma meq_iff_dlist_eq : forall {r c} (m1 m2 : mat r c), *)
  (*     m1 == m2 <-> (m2l m1 == m2l m2)%dlist. *)
  (* Proof. *)
  (*   intros. easy. *)
  (* Qed. *)

  (** Get n-th element of a matrix *)
  Definition mnth {r c} (m : mat r c) (ri ci : nat) : A :=
    vnth (vnth m ri (A0:=(vec0 (A0:=A0) (n:=c)))) ci (A0:=A0).

  (** meq and mnth should satisfy this constraint *)
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> (forall ri ci, ri < r -> ci < c -> (mnth m1 ri ci == mnth m2 ri ci)%A).
  Proof.
    intros. split; intros.
    -
      intros.
      (** TRY TO CONSTRUCT Ltac for matrix equal.

          below code just for test. *)
      
  (*   (* destruct all mat to a list and a proposition of its length equation *) *)
  (*   repeat match goal with *)
  (*          | m : mat _ _ |- _ => destruct m as [?m ?Hm] *)
  (*          end. *)
  (*   unfold mnth,meq. *)
  (*   apply veq_iff_list_eq in H; unfold veq in H; simpl in H.  *)
    
  (*   (* convert meq to list equal, meanwhile the meq equation will be dropped *) *)
  (*   repeat match goal with *)
  (*          (* | H: meq ?m1 ?m2 |- _ => rewrite veq_iff_list_eq in H *) *)
  (*          | |- meq _ _ => apply veq_iff_list_eq *)
  (*          end; *)
  (*     (* simplify *) *)
  (*     simpl in *; *)
  (*     (* try to solve *) *)
  (*     try easy. *)

  (*   veq_simpl. *)
  (*     match goal with *)

  (*     unfold mat,meq in *. veq_simpl. *)
      
  (*     (* apply veq_iff_vnth; auto. *) *)
  (*     unfold mat in *. *)
  (*     apply veq_iff_vnth in H. *)
  (*     apply veq_iff_vnth. *)
  (*   apply meq_iff_mnth. *)
      (* Qed. *)
  Abort.
  
  (* (* ==================================== *) *)
  (* (** ** Convert between list list and matrix *) *)

  (* (** *** list list to mat *) *)
  
  (* Definition l2m {r c} (dl : list (list A)) : mat r c := @l2m A A0 r c dl. *)

  (* (** l2m is a proper morphism *) *)
  (* Lemma l2m_aeq_mor : forall r c, Proper (eqlistA (eqlistA Aeq) ==> meq) (@l2m r c). *)
  (* Proof. *)
  (*   Admitted. *)

  (* Global Existing Instance l2m_aeq_mor. *)
  
  (* Lemma l2m_inj : forall {r c} (d1 d2 : list (list A)), *)
  (*     length d1 = r -> width d1 c ->  *)
  (*     length d2 = r -> width d2 c ->  *)
  (*     ~(d1 == d2)%dlist -> ~(@l2m r c d1 == l2m d2). *)
  (* Proof. *)
  (*   intros. apply l2m_inj; auto. *)
  (* Qed. *)
  
  (* Lemma l2m_surj : forall {r c} (m : mat r c),  *)
  (*     (exists d, l2m d == m). *)
  (* Proof. *)
  (*   intros. apply l2m_surj. *)
  (* Qed. *)

  
  (* (** *** mat to list list *) *)
  (* Definition m2l {r c} (m : mat r c) : list (list A) := @m2l A r c m. *)

  (* (** m2l is a proper morphism *) *)
  (* Lemma m2l_aeq_mor : forall r c, Proper (meq ==> eqlistA (eqlistA Aeq)) (@m2l r c). *)
  (* Proof. *)
  (*   Admitted. *)

  (* Global Existing Instance m2l_aeq_mor. *)

  (* Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r. *)
  (* Proof. *)
  (*   intros. apply m2l_length. *)
  (* Qed. *)

  (* Global Hint Resolve m2l_length : mat. *)
  
  (* Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c. *)
  (* Proof. *)
  (*   intros. apply m2l_width. *)
  (* Qed. *)

  (* Global Hint Resolve m2l_width : mat. *)
  
  (* Lemma m2l_l2m_id : forall {r c} (dl : list (list A)) (H1 : length dl = r) *)
  (*                      (H2 : width dl c), (@m2l r c (l2m dl) == dl)%dlist. *)
  (* Proof. *)
  (*   intros. apply m2l_l2m_id; auto. *)
  (* Qed. *)
  
  (* Lemma l2m_m2l_id : forall {r c} (m : mat r c), l2m (m2l m) == m.  *)
  (* Proof. *)
  (*   intros. apply l2m_m2l_id; auto. *)
  (* Qed. *)
  
  (* Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), *)
  (*     ~(m1 == m2) -> ~(m2l m1 == m2l m2)%dlist. *)
  (* Proof. *)
  (*   intros. apply (m2l_inj (A0:=A0)). easy. *)
  (* Qed. *)
  
  (* Lemma m2l_surj : forall {r c} (d : list (list A)),  *)
  (*     length d = r -> width d c ->  *)
  (*     (exists m, @m2l r c m == d)%dlist. *)
  (* Proof. *)
  (*   intros. apply (m2l_surj (A0:=A0)); auto. *)
  (* Qed. *)
  
  (* (* ==================================== *) *)
  (* (** ** Specific matrix *) *)

  (* Definition mk_mat_1_1 (a11 : A) : mat 1 1 := mk_mat_1_1 (A0:=A0) a11. *)

  (* Definition mk_mat_3_1 (a1 a2 a3 : A) : mat 3 1 := mk_mat_3_1 (A0:=A0) a1 a2 a3. *)
  
  (* Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A) : mat 3 3  *)
  (*   := mk_mat_3_3 (A0:=A0) a11 a12 a13 a21 a22 a23 a31 a32 a33. *)

  (* Definition mk_mat_2_2 (a11 a12 a21 a22 : A) : mat 2 2 *)
  (*   := mk_mat_2_2 (A0:=A0) a11 a12 a21 a22. *)

  (* (* ==================================== *) *)
  (* (** ** Convert between tuples and matrix *) *)
  
  (* (** tuple_3x3 -> mat_3x3 *) *)
  (* Definition t2m_3x3 (t : @T_3x3 A) : mat 3 3 := t2m_3x3 (A0:=A0) t. *)
  
  (* (** mat_3x3 -> tuple_3x3 *) *)
  (* Definition m2t_3x3 (m : mat 3 3) : @T_3x3 A := m2t_3x3 m. *)
  
  (* (** m[0,0] : mat_1x1 -> A *) *)
  (* Definition scalar_of_mat (m : mat 1 1) := mnth m 0 0. *)

  (* (* ==================================== *) *)
  (* (** ** Matrix transposition *) *)
  
  (* Definition mtrans {r c} (m : mat r c): mat c r := *)
  (*   @mtrans A r c m. *)
  
  (* Global Notation "m \T" := (mtrans m) : mat_scope. *)
  
  (* Lemma mtrans_trans : forall {r c} (m : mat r c), mtrans (mtrans m) == m. *)
  (* Proof. *)
  (*   intros. apply mtrans_trans. *)
  (* Qed. *)
  
  (* (* ==================================== *) *)
  (* (** ** Mapping of matrix *) *)

  (* (** Mapping of a matrix *) *)
  (* Definition mmap {r c} (f : A -> A) (m : mat r c) : mat r c := @mmap A r c f m. *)
  
  (* Definition mmap2 {r c} (f: A -> A -> A) (m1 m2: mat r c) : mat r c := *)
  (*   @mmap2 A r c f m1 m2. *)
  
  (* Lemma mmap2_comm : forall {r c} (f : A -> A -> A) *)
  (*                      (f_comm : forall a b : A, (f a b == f b a)%A) *)
  (*                      (m1 m2 : mat r c),  *)
  (*     mmap2 f m1 m2 == mmap2 f m2 m1. *)
  (* Proof. *)
  (*   (* lma. (* this tactic is enough too. *) *) *)
  (*   intros. apply mmap2_comm. auto. *)
  (* Qed. *)
  
  (* Lemma mmap2_assoc : forall {r c} (f : A -> A -> A) *)
  (*                       (f_assoc : forall a b c, (f (f a b) c == f a (f b c))%A) *)
  (*                       (m1 m2 m3 : mat r c),  *)
  (*     mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3). *)
  (* Proof. *)
  (*   intros. apply mmap2_assoc. auto. *)
  (* Qed. *)

  (* (** Auto unfold these definitions *) *)
  (* Global Hint Unfold meq mmap mmap2 : mat. *)

  (* (** linear matrix arithmetic tactic for equation: split goal to every element *) *)
  (* Global Ltac lma := *)
  (*   autounfold with mat; *)
  (*   Matrix.lma. *)

End BasicMatrixTheoryMA.




Module BasicMatrixTheoryMB (E : ElementType) <: BasicMatrixTheory E.

  (* ==================================== *)
  (** ** Matrix element type *)
  Export E.

  Global Infix "==" := Aeq : A_scope.
  Global Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.

  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope mat_scope.

  (** ** ordinal *)
  Inductive ordinal (n : nat) : Type := Ordinal (m : nat) (H: m < n).
  Arguments Ordinal {n}.

  Definition nat_of_ord {n:nat} (o : ordinal n) := let '(Ordinal m _) := o in m.

  Section test.
    Let ord1 : ordinal 2.
      eapply (Ordinal 1). lia. Defined.
    (* Compute nat_of_ord ord1. *)
  End test.

  (** ** vector *)
  Section vec.
    Context {Aeq:@Decidable A Aeq}.
    Infix "==" := Aeq.
    
    Definition vec (n : nat) : Type := ordinal n -> A.

    Fixpoint veq {n:nat} (v1 v2 : vec n) : Prop :=
      match n with
      | O => True
              | n' => 

  (* ==================================== *)
  (** ** Matrix type and basic operations *)
  
  Definition mat (r c : nat) : Type := @vec (@vec A c) r.

  (** matrix equality *)
  Definition meq {r c : nat} (m1 m2 : mat r c) : Prop := @meq A Aeq r c m1 m2.
  Global Infix "==" := meq : mat_scope.

  Lemma meq_equiv : forall {r c}, Equivalence (meq (r:=r) (c:=c)).
  Proof. 
    intros. apply meq_equiv.
  Qed.

  Global Existing Instance meq_equiv.

  (** Get n-th element of a matrix *)  
  Definition mnth {r c} (m : mat r c) (ri ci : nat) := @mnth A r c m ri ci.

  (** meq and mnth should satisfy this constraint *)
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> (forall ri ci, ri < r -> ci < c -> (mnth m1 ri ci == mnth m2 ri ci)%A).
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

  Definition mk_mat_1_1 (a11 : A) : mat 1 1 := mk_mat_1_1 (A0:=A0) a11.

  Definition mk_mat_3_1 (a1 a2 a3 : A) : mat 3 1 := mk_mat_3_1 (A0:=A0) a1 a2 a3.
  
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A) : mat 3 3 
    := mk_mat_3_3 (A0:=A0) a11 a12 a13 a21 a22 a23 a31 a32 a33.

  Definition mk_mat_2_2 (a11 a12 a21 a22 : A) : mat 2 2
    := mk_mat_2_2 (A0:=A0) a11 a12 a21 a22.

  (* ==================================== *)
  (** ** Convert between tuples and matrix *)
  
  (** tuple_3x3 -> mat_3x3 *)
  Definition t2m_3x3 (t : @T_3x3 A) : mat 3 3 := t2m_3x3 (A0:=A0) t.
  
  (** mat_3x3 -> tuple_3x3 *)
  Definition m2t_3x3 (m : mat 3 3) : @T_3x3 A := m2t_3x3 m.
  
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

End BasicMatrixTheoryNF.
