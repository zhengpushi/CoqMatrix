(*
  Copyright 2023 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with record, (2D, from mat to vec)
  author    : ZhengPu Shi
  date      : 2023.11

  remark    :
  1. No dependent type, to unify "vec (2+3)" and "vec 5"
  2. Support two dimension, and then derived `cvec := mat n 1` and `rvec := mat 1 n`
 *)

Require Export Lia.
Require Export BasicConfig NatExt StrExt ListExt.
Require Import Extraction.

(* also contain "A*" which * is number, e.g. A0 A1 ... *)
Generalizable Variable A B C Aeq Beq Ceq Azero Aone Aadd Aopp Amul Ainv.

Open Scope nat_scope.

(* Old definition

Record mat (A : Type) (r c:nat) : Type :=
  mk_mat {
      mdata : list (list A);
      mheight : length mdata = r;
      mwidth : Forall (fun l => length l = c) mdata
    }.
Recursive Extraction mat.

 (* Extracted OCaml code, only left a list structure *)
(* type 'a mat = 'a list list *)
 *)

Record mat (A : Type) : Type :=
  mk_mat {
      msize_r : nat;
      msize_c : nat;
      mdata : list (list A);
      (* mdata0 : A;               (* default value *) *)
      msizeP : length mdata = msize_r /\ Forall (fun l => length l = msize_c) mdata
    }.
Recursive Extraction mat.

Arguments mk_mat {A}.
Arguments msize_r {A}.
Arguments msize_c {A}.
Arguments mdata {A}.
Arguments msizeP {A}.

Example mat_ex00 : mat nat. refine (mk_mat 0 0 [] _). auto. Defined.
Example mat_ex02 : mat nat. refine (mk_mat 0 2 [] _). auto. Defined.
Example mat_ex20 : mat nat. refine (mk_mat 2 0 [[];[]] _). auto. Defined.
Example mat_ex22 : mat nat. refine (mk_mat 2 2 [[1;2];[3;4]] _). auto. Defined.
Example mat_ex23 : mat nat. refine (mk_mat 2 3 [[1;2;3];[4;5;6]] _). auto. Defined.
Example mat_ex32 : mat nat. refine (mk_mat 3 2 [[1;2];[3;4];[5;6]] _). auto. Defined.

(* Matrix equality could be proved by the eqaulities of size and data *)
Lemma meq_rw : forall {A} (m1 m2 : mat A),
    msize_r m1 = msize_r m2 -> msize_c m1 = msize_c m2 ->
    mdata m1 = mdata m2 -> m1 = m2.
Proof.
  intros. destruct m1, m2. simpl in *. subst. f_equal.
  apply proof_irrelevance.
Qed.

(* Algebraic operations on matrix *)
Section malg.
  Context `{R:Ring}.
  Add Ring ring_inst : make_ring_theory.

  (* Matrix addition *)
  Definition madd (m1 m2 : mat A) : option (mat A).
    destruct m1 as [r1 c1 d1 [ph1 pw1]], m2 as [r2 c2 d2 [ph2 pw2]].
    destruct (r1 =? r2) eqn:Er; [| exact None].
    destruct (c1 =? c2) eqn:Ec; [| exact None].
    apply Nat.eqb_eq in Er,Ec.
    rewrite <- Er, <- Ec in *; clear Er Ec r2 c2.
    refine (Some (mk_mat r1 c1 (dmap2 Aadd d1 d2) _)). split.
    - rewrite dmap2_length; auto. rewrite ph1; auto.
    - apply dmap2_width; auto.
  Defined.
  
  (* Matrix scalar multiplication *)
  Definition mcmul (k : A) (m : mat A) : mat A.
    destruct m as [r c d [ph pw]].
    refine (mk_mat r c (dmap (Amul k) d) _). split.
    - rewrite dmap_length; auto.
    - apply dmap_width; auto.
  Defined.

  (* Matrix transpose *)
  Definition mtrans (m : mat A) : mat A.
    destruct m as [r c d [ph pw]].
    refine (mk_mat c r (dltrans d c) _). split.
    - rewrite dltrans_length; auto.
    - apply dltrans_width; auto.
  Defined.

  (* Matrix multiplication *)
  Definition mmul (m1 m2 : mat A) : option (mat A).
    destruct m1 as [r c d1 [ph1 pw1]], m2 as [c' s d2 [ph2 pw2]].
    destruct (c =? c') eqn:Ec; [| exact None].
    apply Nat.eqb_eq in Ec.
    rewrite <- Ec in *; clear Ec c'.
    refine (Some
              (mk_mat r s
                 (dldotdl d1 (dltrans d2 s)
                    (Aadd:=Aadd) (Amul:=Amul) (Azero:=Azero)) _)). split.
    - rewrite dldotdl_length with (r1:=r); auto.
    - apply dldotdl_width with (c:=c); auto.
      apply dltrans_length; auto. apply dltrans_width; auto.
  Defined.

End malg.

Recursive Extraction madd mcmul mtrans mmul.

(* Get element *)
Definition mget {A} (A0:A) (m : mat A) (i j : nat) : option A.
  destruct m as [r c d p].
  destruct (i <? r) eqn:Er; [| exact None].
  destruct (j <? c) eqn:Ec; [| exact None].
  apply (Some (nth j (nth i d nil) A0)).
Defined.

Recursive Extraction mget.

Compute mget 9 mat_ex23 0 0.
Compute mget 9 mat_ex23 0 2.
Compute mget 9 mat_ex23 1 1.

(* Get row *)
Definition mgetr {A} (m : mat A) (i : nat) : option (mat A).
  destruct m as [r c d [ph pw]].
  destruct (i <? r) eqn:Er; [| exact None].
  refine (Some (mk_mat 1 c [nth i d nil] _)). split.
  - auto.
  - constructor; auto.
    apply Forall_nth; auto. apply Nat.ltb_lt in Er. rewrite ph; auto.
Defined.

Recursive Extraction mgetr.

Compute mgetr mat_ex23 0.
Compute mgetr mat_ex23 1.
Compute mgetr mat_ex23 2.

(* Get column *)
Definition mgetc {A} (m : mat A) (j : nat) (A0:A) : option (mat A).
  destruct m as [r c d [ph pw]].
  destruct (j <? c) eqn:Ec; [| exact None].
  refine (Some (mk_mat r 1 (row2col (nthc A0 d j)) _)). split.
  - rewrite row2col_length. rewrite nthc_length. auto.
  - apply row2col_width.
Defined.

Compute mgetc mat_ex23 0 9.
Compute mgetc mat_ex23 1 9.
Compute mgetc mat_ex23 2 9.
Compute mgetc mat_ex23 3 9.

(* 数组打印 *)
Definition mprt {A} (m : mat A) (p : A -> string) : string :=
  dlst_prt (mdata m) p.

Compute mprt mat_ex23 (fun x => str_alignl (nat2str x) 3).
Compute mprt mat_ex32 (fun x => str_alignl (nat2str x) 3).

?
(** ** Convert between function and matrix *)
Section f2m_m2f.
  
  Context `{Aeq:relation A} (Azero:A).
  Infix "==" := Aeq : A_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.

  Definition f2m {r c} (f : nat -> nat -> A) : @mat A r c :=
    mk_mat (@f2dl A r c f) (f2dl_length r c f) (f2dl_width r c f).
  
  Definition m2f {r c} (m : mat r c) : (nat -> nat -> A) :=
    dl2f (r:=r) (c:=c) (Azero:=Azero) (mdata m).

End f2m_m2f.


(** ** matrix with specific size *)

(** mat_1_1 *)
Section mat_1_1.

  Context {A:Type}.
  Variable a : A.
  
  Let data := [[a]].
  Let cond_h : length data = 1. auto. Qed.  
  Let cond_w : width data 1. constructor; auto. Qed.
  
  Definition mk_mat_1_1 : mat 1 1 := mk_mat data cond_h cond_w.

End mat_1_1.


(** mat_1_2 *)
Section mat_1_2.
  
  Context {A:Type}.
  Variable a b : A.
  
  Let data : list (list A) := [[a; b]].
  Let cond_h : length data = 1. auto. Qed.  
  Let cond_w : width data 2. constructor; auto. Qed.
  
  Definition mk_mat_1_2' : mat 1 2 := mk_mat data cond_h cond_w.

End mat_1_2.


(** mat_0_c *)
Section mat_0_c.
  
  Context {A:Type}.
  Variable c : nat.

  Let data : list (list A) := [].
  Let cond_h : length data = 0. auto. Qed.  
  Let cond_w : width data c. constructor; auto. Qed.
  
  Definition mk_mat_0_c : mat 0 c := mk_mat data cond_h cond_w.

End mat_0_c.


(** mat_1_c *)
Section mat_1_c.
  
  Context {A:Type}.
  Variable l : list A.
  Variable c : nat.
  Variable H1 : length l = c.
  
  Let data : list (list A) := [l].
  Let cond_h : length data = 1. auto. Qed.  
  Let cond_w : width data c. constructor; auto. Qed.
  
  Definition mk_mat_1_c : mat 1 c := mk_mat data cond_h cond_w.

End mat_1_c.


(** mat_1_2, mat_1_3, ... *)
Definition mk_mat_1_2 {A} (a1 a2 : A) : mat 1 2 := 
  mk_mat_1_c [a1;a2] 2 eq_refl.

Definition mk_mat_1_3 {A} (a1 a2 a3 : A) : mat 1 3 := 
  mk_mat_1_c [a1;a2;a3] 3 eq_refl.

Definition mk_mat_1_4 {A} (a1 a2 a3 a4 : A) : mat 1 4 := 
  mk_mat_1_c [a1;a2;a3;a4] 4 eq_refl.


(** mat_r_0 *)
Section mat_r_0.
  
  Context {A:Type}.
  Variable l : list A.
  Variable r : nat.
  Variable H1 : length l = r.
  
  Let data : list (list A) := @dnil A r.
  Let cond_h : length data = r. unfold data. rewrite dnil_length. auto. 
  Qed.
  Let cond_w : width data 0. unfold data. apply dnil_width. Qed.
  
  Definition mk_mat_r_0 : mat r 0 := mk_mat data cond_h cond_w.

End mat_r_0.


(** mat_r_1 *)
Section mat_r_1.
  
  Context {A:Type}.
  Variable l : list A.
  Variable r : nat.
  Variable H1 : length l = r.
  
  Let data : list (list A) := row2col l.
  Let cond_h : length data = r. unfold data. rewrite row2col_length. auto. 
  Qed.
  Let cond_w : width data 1. unfold data. apply row2col_width; auto. Qed.
  
  Definition mk_mat_r_1 : mat r 1 := mk_mat data cond_h cond_w.

End mat_r_1.


(** mat_2_1, mat_3_1, ... *)
Definition mk_mat_2_1 {A} (a1 a2 : A) : mat 2 1 := 
  mk_mat_r_1 [a1;a2] 2 eq_refl.

Definition mk_mat_3_1 {A} (a1 a2 a3 : A) : mat 3 1 := 
  mk_mat_r_1 [a1;a2;a3] 3 eq_refl.

Definition mk_mat_4_1 {A} (a1 a2 a3 a4 : A) : mat 4 1 := 
  mk_mat_r_1 [a1;a2;a3;a4] 4 eq_refl.


(** mat_2_2 *)
Section mat_2_2.
  
  Context {A:Type}.
  Variable a11 a12 a21 a22 : A.
  
  Let data : list (list A) := [[a11;a12];[a21;a22]].
  Let cond_h : length data = 2. auto. Qed.
  Let cond_w : width data 2. unfold data. constructor; auto. Qed.
  
  Definition mk_mat_2_2 : mat 2 2 := mk_mat data cond_h cond_w.

End mat_2_2.


(** mat_3_3 *)
Section mat_3_3.
  
  Context {A:Type}.
  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.
  
  Let data : list (list A) := [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  Let cond_h : length data = 3. auto. Qed.
  Let cond_w : width data 3. unfold data. constructor; auto. Qed.
  
  Definition mk_mat_3_3 : mat 3 3 := mk_mat data cond_h cond_w.

End mat_3_3.


(** ** Matrix map to a dlist *)
Section matmapdl.

  Context {A B:Type} {r c : nat}.
  Variable f : A -> B.
  
  Definition matmapdl (m : mat r c) : list (list B) :=
    dmap f (mdata m).

  Lemma matmapdl_length : forall (m : mat r c), 
      length (matmapdl m) = r.
  Proof. 
    intros; simpl. unfold matmapdl. rewrite dmap_length.
    apply mheight.
  Qed.

  Lemma matmapdl_width : forall (m : mat r c), 
      width (matmapdl m) c.
  Proof. 
    intros; simpl. unfold matmapdl. rewrite <- dmap_width.
    apply mwidth.
  Qed.

End matmapdl.


(** ** Matrix map2 to a dlist *)
Section matmap2dl.
  
  Context {A B C : Type} {r c : nat}.
  Variable f : A -> B -> C.

  Definition matmap2dl (m1 : mat r c) (m2 : @mat B r c) 
    : list (list C) :=
    dmap2 f (mdata m1) (mdata m2).

  Lemma matmap2dl_length : forall (m1 : mat r c) (m2 : @mat B r c),
      length (matmap2dl m1 m2) = r.
  Proof. 
    intros; simpl. unfold matmap2dl. rewrite dmap2_length;
      repeat rewrite mheight; auto.
  Qed.

  Lemma matmap2dl_width : forall (m1 : mat r c) (m2 : @mat B r c),
      width (matmap2dl m1 m2) c.
  Proof. 
    intros; simpl. unfold matmap2dl. apply dmap2_width;
      apply mwidth.
  Qed.

End matmap2dl.


(** ** Matrix map *)
Section matmap.

  Context {A B : Type} {r c : nat}.
  Variable f : A -> B.
  
  Definition matmap (m : mat r c) : @mat B r c :=
    mk_mat (matmapdl f m) (matmapdl_length f m) (matmapdl_width f m).

End matmap.


(** ** Matrix map2 *)
Section matmap2.

  Context {A B C : Type} {r c : nat}.
  
  Definition matmap2 (f : A -> B -> C) (m1 : mat r c) (m2 : @mat B r c) 
    : @mat C r c :=
    mk_mat (matmap2dl f m1 m2) (matmap2dl_length f m1 m2) 
      (matmap2dl_width f m1 m2).

End matmap2.


(** ** Matrix map2 with same base type *)
Section matmap2_sametype.

  Context `{Aeq:relation A} `{Aadd:A->A->A}.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.

  Context `{Comm_Aadd : Commutative A Aadd Aeq}.
  Lemma matmap2_comm : forall {r c} (m1 m2 : mat r c),
      matmap2 Aadd m1 m2 == matmap2 Aadd m2 m1.
  Proof.
    intros. unfold meq,matmap2,matmap2dl; simpl.
    apply dmap2_comm; auto.
  Qed.
  
  Context `{Assoc_Aadd : Associative A Aadd Aeq}.
  Context `{Equiv_Aeq: Equivalence A Aeq}.
  Lemma matmap2_assoc : forall {r c} (m1 m2 m3 : mat r c),
      matmap2 Aadd (matmap2 Aadd m1 m2) m3 == matmap2 Aadd m1 (matmap2 Aadd m2 m3).
  Proof.
    intros. unfold meq,matmap2,matmap2dl; simpl.
    apply dmap2_assoc; auto.
  Qed.
  
End matmap2_sametype.


(** ** zero matrix and unit matrix *)
Section mat0_mat1.

  Context {A:Type} (Azero Aone : A).
  Definition mat0 {r c} := mk_mat (dlzero Azero r c) dlzero_length dlzero_width.
  Definition mat1 {n} := mk_mat (dlunit Azero Aone n) dlunit_length dlunit_width.

End mat0_mat1.


(** ** matrix transpose *)
Section mtrans.

  Context `{Aeq:relation A}.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  
  Definition mtrans {r c} (m : @mat A r c) : mat c r :=
    let dl := mdata m in
    mk_mat (dltrans dl c) 
      (dltrans_length dl c (mwidth m))
      (dltrans_width dl r c (mheight m) (mwidth m)).
  
  (** Transpose twice return back *)
  Context `{Equiv_Aeq: Equivalence A Aeq}.
  Lemma mtrans_trans : forall {r c} (m : mat r c),
      mtrans (mtrans m) == m.
  Proof.
    intros. destruct m; unfold meq; simpl.
    rewrite dltrans_trans; try easy.
  Qed.
  
End mtrans.


(** ** matrix addition,opposition,subtraction *)
Section madd_opp_sub.

  Context `{G:AGroup A Aadd Azero Aopp Aeq}.
  Notation Asub := (fun a b => Aadd a (Aopp b)).
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  
  (** matrix addition *)
  Definition madd {r c} (m1 m2 : mat r c) : mat r c :=
    matmap2 Aadd m1 m2.
  Infix "+" := madd : mat_scope.

  Lemma madd_aeq_mor : forall r c,
      Proper (meq (Aeq:=Aeq) ==> meq (Aeq:=Aeq) ==> meq (Aeq:=Aeq) (r:=r) (c:=c)) madd.
  Proof.
    unfold Proper, respectful.
    intros. destruct x, y, x0, y0. unfold meq in *; simpl in *.
    unfold matmap2dl; simpl. rewrite H,H0. easy.
  Qed.

  Global Existing Instance madd_aeq_mor.
  
  (** matrix opposition *)
  Definition mopp {r c} (m : mat r c) : mat r c :=
    matmap Aopp m.
  Notation "- m" := (mopp m) : mat_scope.

  Lemma mopp_aeq_mor : forall r c,
      Proper (meq (Aeq:=Aeq) ==> meq (Aeq:=Aeq) (r:=r) (c:=c)) mopp.
  Proof.
    unfold Proper, respectful.
    intros. destruct x, y. unfold meq in *; simpl in *.
    unfold matmapdl; simpl. rewrite H. easy.
  Qed.
  
  (* matrix subtraction *)
  Definition msub {r c} (m1 m2 : mat r c) : mat r c :=
    matmap2 Asub m1 m2.
  Infix "-" := msub : mat_scope.
  
  Global Existing Instance mopp_aeq_mor.

  Lemma msub_aeq_mor : forall r c,
      Proper (meq (Aeq:=Aeq) ==> meq (Aeq:=Aeq) ==> meq (Aeq:=Aeq) (r:=r) (c:=c)) msub.
  Proof.
    unfold Proper, respectful.
    intros. destruct x, y, x0, y0. unfold meq in *; simpl in *.
    unfold matmap2dl; simpl.
    rewrite H,H0. easy.
  Qed.

  Global Existing Instance msub_aeq_mor.

  Lemma madd_comm : forall {r c} (m1 m2 : mat r c),
      m1 + m2 == m2 + m1.
  Proof.
    intros. unfold meq,matmap2dl. apply dmap2_comm.
  Qed.
  
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : mat r c),
      (m1 + m2) + m3 == m1 + (m2 + m3).
  Proof.
    intros. unfold meq, matmap2dl. apply dmap2_assoc.
  Qed.
  
  (** 0 + m = m *)
  Lemma madd_zero_l : forall {r c} (m : mat r c), (mat0 Azero) + m == m.
  Proof.
    intros. unfold meq,matmap2dl.
    apply dladd_zero_l; auto. apply mheight. apply mwidth.
  Qed.

  (** m + 0 = m *)
  Lemma madd_zero_r : forall {r c} (m : mat r c), m + (mat0 Azero) == m.
  Proof.
    intros. unfold meq, madd.
    rewrite matmap2_comm. apply madd_zero_l.
  Qed.
  
  (** - (- m) = m *)
  Lemma mopp_opp : forall {r c} (m : mat r c), - (- m) == m.
  Proof.
    intros. unfold meq,mopp,matmap,matmapdl,dmap. simpl.
    (** Remark: with the help of "map_map, map_id on setoid", the proof is well *)
    rewrite map_map. rewrite map_id. easy.
    intros. rewrite map_map. rewrite map_id. easy.
    intros. rewrite group_inv_inv. easy.
  Qed.

  Lemma mopp_exchange : forall {r c} (m1 m2 : mat r c), -m1 == m2 <-> m1 == -m2.
  Proof.
    intros. split; intros.
    - rewrite <- H. rewrite mopp_opp. easy.
    - rewrite H. rewrite mopp_opp. easy. 
  Qed.

  Lemma mopp_mat0 : forall {r c:nat}, - (@mat0 A Azero r c) == mat0 Azero.
  Proof.
    intros. hnf. unfold mopp,mat0; simpl. unfold matmapdl; simpl.
    unfold dmap,dlzero. revert c.
    induction r; intros; simpl; try easy. apply cons_aeq_mor; auto.
    induction c; intros; simpl; try easy. apply cons_aeq_mor; auto.
    apply group_opp_zero_eq_zero.
  Qed.

  Lemma madd_opp : forall {r c} (m : mat r c), m + (-m) == mat0 Azero.
  Proof.
    intros. destruct m as [dl H W]. hnf.
    unfold mopp,madd,meq; simpl. unfold matmap2dl; simpl.
    unfold dmap2,matmapdl,dlzero,dmap. simpl.
    revert c dl H W. induction r; intros; simpl.
    - apply List.length_zero_iff_nil in H. subst. simpl. auto.
    - destruct dl. easy. inv H. inv W.
      rewrite map_cons. simpl. apply cons_aeq_mor.
      + (* needn't induction, use map_id and map2_map_map *)
        rewrite <- (map_id l (fun x => x)) at 1; try easy.
        rewrite map2_map_map with (g:=fun x => Aadd x (Aopp x)); try easy.
        apply map_eq_zero; auto. intros. group_simpl.
      + apply IHr; auto.
  Qed.

  (* m1 - m2 = - (m2 - m1) *)
  Lemma msub_comm : forall {r c} (m1 m2 : mat r c),
      m1 - m2 == - (m2 - m1).
  Proof.
    intros. destruct m1,m2.
    unfold meq,msub,mopp,matmap2,matmap2dl; simpl.
    unfold matmapdl; simpl. subst.
    rewrite (dlsub_comm _ _ c); easy.
  Qed.

  Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c),
      (m1 - m2) - m3 == m1 - (m2 + m3).
  Proof.
    intros. unfold meq,msub,mopp,madd,matmap2,matmap2dl. simpl.
    apply (dlsub_assoc _ _ _ c); try apply mwidth;
      repeat rewrite mheight; auto.
  Qed.
  
  (** 0 - m = - m *)
  Lemma msub_zero_l : forall {r c} (m : mat r c),
      (mat0 Azero) - m == - m.
  Proof.
    intros. unfold meq, msub, mopp, matmap2dl. simpl.
    unfold matmap2dl, matmapdl.
    apply dlsub_zero_l; auto. apply mheight. apply mwidth.
  Qed.
  
  (** m - 0 = m *)
  Lemma msub_zero_r : forall {r c} (m : mat r c),
      m - (mat0 Azero) == m.
  Proof.
    intros. unfold meq, msub, mopp, matmap2dl. simpl.
    unfold matmap2dl, matmapdl.
    apply dlsub_zero_r; auto. apply mheight. apply mwidth.
  Qed.
  
  (** m - m = 0 *)
  Lemma msub_self : forall {r c} (m : mat r c),
      m - m == (mat0 Azero).
  Proof.
    intros. unfold meq, msub, mopp, matmap2dl. simpl.
    unfold matmap2dl, matmapdl.
    apply dlsub_self; auto. apply mheight. apply mwidth.
  Qed.

End madd_opp_sub.



(** ** matrix multiplication *)
Section mcmul_mmulc_mmul.

  Context {A:Type} {Azero Aone:A}.
  Context `{R:Ring A Aadd Azero Aopp Amul Aone Aeq}.
  Add Ring ring_inst : make_ring_theory.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.

  Infix "+" := (madd (Aadd:=Aadd)) : mat_scope.
  Notation "- m" := (mopp (Aopp:=Aopp) m) : mat_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.

  Definition mcmul {r c : nat} (a : A) (m : @mat A r c) : @mat A r c.
    refine (mk_mat (dmap (fun x => Amul a x) (mdata m)) _ _).
    - rewrite dmap_length. destruct m. simpl. auto.
    - apply dmap_width. destruct m. simpl. auto.
  Defined.
  Infix "c*" := mcmul : mat_scope.

  Definition mmulc {r c : nat} (m : @mat A r c) (a : A) : @mat A r c.
    refine (mk_mat (dmap (fun x => Amul x a) (mdata m)) _ _).
    - rewrite dmap_length. destruct m. simpl. auto.
    - apply dmap_width. destruct m. simpl. auto.
  Defined.
  Infix "*c" := mmulc : mat_scope.

  Definition mmul {r c t : nat} (m1 : @mat A r c) (m2 : @mat A c t) : @mat A r t.
    refine (mk_mat (dldotdl (Aadd:=Aadd) (Azero:=Azero) (Amul:=Amul)
                      (mdata m1) (mdata (mtrans m2))) _ _).
    - destruct m1 as [dl1 H1 W1], m2 as [dl2 H2 W2]; simpl.
      apply dldotdl_length; auto.
    - destruct m1 as [dl1 H1 W1], m2 as [dl2 H2 W2]; simpl.
      apply (dldotdl_width _ _ _ c);
        auto using dltrans_length, dltrans_width.
  Defined.
  Infix "*" := mmul : mat_scope.

  (** matrix muliplication left distributve over addition. 
        A * (B + C) = A * B + A * C *)
  Lemma mmul_add_distr_l : forall {r c t} (m1 : mat r c) (m2 m3 : mat c t),
      m1 * (m2 + m3) == (m1 * m2) + (m1 * m3).
  Proof.
    intros. destruct m1,m2,m3.
    unfold meq; simpl. unfold matmap2dl; simpl.
    rewrite dltrans_dmap2; auto.
    rewrite (dldotdl_dmap2_distr_r _ _ _ mwidth0);
      auto using dltrans_length, dltrans_width. easy. lia.
  Qed.
  
  (** matrix muliplication right distributve over addition. 
        (A + B) * C = A * C + B * C *)
  Lemma mmul_add_distr_r : forall {r c t} (m1 m2 : mat r c) (m3 : mat c t),
      (m1 + m2) * m3 == (m1 * m3) + (m2 * m3).
  Proof.
    intros. destruct m1,m2,m3.
    unfold meq; simpl. unfold matmap2dl; simpl.
    rewrite (dldotdl_dmap2_distr_l _ _ _ mwidth0);
      auto using dltrans_length, dltrans_width. easy.
  Qed.

  (** matrix muliplication association. 
        (A * B) * C = A * (B * C) *)
  Lemma mmul_assoc : forall {r c t s} (m1 : mat r c) (m2 : mat c t) (m3 : mat t s),
      (m1 * m2) * m3 == m1 * (m2 * m3).
  Proof.
    intros. destruct m1,m2,m3.
    unfold meq; simpl. unfold matmap2dl; simpl.
    rewrite dldotdl_assoc; auto.
    rewrite dltrans_length; easy. apply dltrans_width; auto.
  Qed.
  
  (** 0 * A = 0 *)
  Lemma mmul_0_l : forall {r c t} (m : mat c t), (mat0 Azero) * m == (@mat0 A Azero r t).
  Proof.
    intros. destruct m; simpl.
    unfold meq; simpl.
    rewrite dldotdl_zero_l. rewrite dltrans_length; auto. easy.
    apply dltrans_width; auto.
  Qed.
  
  (** A * 0 = 0 *)
  Lemma mmul_0_r : forall {r c t} (m : mat r c), m * (mat0 Azero) == (@mat0 A Azero r t).
  Proof.
    intros. destruct m; simpl.
    unfold meq; simpl.
    rewrite dltrans_zero. rewrite dldotdl_zero_r; auto. subst. easy.
  Qed.
  
  (** 1 * A = A *)
  Lemma mmul_1_l : forall {r c} (m : mat r c), (mat1 Azero Aone) * m == m.
  Proof.
    intros. destruct m; simpl.
    unfold meq; simpl.
    rewrite dldotdl_dlunit_l;
      auto using dltrans_length, dltrans_width.
    apply dltrans_trans; auto.
  Qed.
  
  (** A * 1 = A *)
  Lemma mmul_1_r : forall {r c} (m : mat r c), m * (mat1 Azero Aone) == m.
  Proof.
    intros. destruct m; simpl.
    unfold meq; simpl.
    rewrite dltrans_dlunit.
    rewrite dldotdl_dlunit_r;
      auto using dltrans_length, dltrans_width. easy.
  Qed.
  
  (** a * M = M * a *)
  Lemma mmulc_eq_mcmul : forall {r c} (m : mat r c) a, m *c a == a c* m.
  Proof.
    intros. destruct m; simpl.
    unfold meq; simpl.
    rewrite dmap_ext with (g:=(fun x => (a*x)%A)). easy.
    intros. ring.
  Qed.

  (** a * (b * M) = (a * b) * M *)
  Lemma mcmul_assoc : forall {r c} (m : mat r c) a1 a2,
      a1 c* (a2 c* m) == (a1 * a2)%A c* m.
  Proof.
    intros. destruct m; simpl.
    unfold meq; simpl. unfold dmap; simpl.
    (* Remark: with the help of "map_ext on setoid", the proof is simplified. *)
    rewrite map_map. apply map_ext. intros.
    rewrite map_map. apply map_ext. intros. ring.
  Qed.
  
  (** a * (b * M) = (a * b) * M *)
  Lemma mcmul_perm : forall {r c} (m : mat r c) a1 a2,
      a1 c* (a2 c* m) == a2 c* (a1 c* m).
  Proof.
    intros. destruct m; simpl.
    unfold meq; simpl. unfold dmap; simpl.
    (* Remark: with the help of "map_ext on setoid", the proof is simplified. *)
    rewrite ?map_map. apply map_ext. intros.
    rewrite ?map_map. apply map_ext. intros. ring.
  Qed.

  (** a * (M1 + M2) = (a * M1) + (a * M2) *)
  Lemma mcmul_distr_l : forall {r c} a (m1 m2 : mat r c),
      a c* (m1 + m2) == (a c* m1) + (a c* m2).
  Proof.
    intros. destruct m1,m2; simpl.
    unfold meq; simpl. unfold matmap2dl; simpl.
    apply symmetry.
    apply dmap2_dmap_hom.
    intros. ring.
  Qed.
  
  (** (a1 + a2) * M = (a1 * M) + (a2 * M) *)
  Lemma mcmul_distr_r : forall {r c} a1 a2 (m : mat r c),
      (a1 + a2)%A c* m == (a1 c* m) + (a2 c* m).
  Proof.
    intros. destruct m; simpl.
    unfold meq; simpl. unfold matmap2dl; simpl.
    rewrite (dmap2_dmap_dmap _ _ (fun x => (a1 + a2) * x)%A). easy.
    intros. ring.
  Qed.

  (* 0 c* m = mat0 *)
  Lemma mcmul_0_l : forall {r c} (m : mat r c), Azero c* m == mat0 Azero.
  Proof.
    intros. destruct m; simpl.
    unfold meq; simpl.
    rewrite dmap_ext with (g:=(fun x => Azero)).
    - apply dmap_eq_zero; auto.
    - intros. ring. 
  Qed.
  
  (* 1 c* m = m *)
  Lemma mcmul_1 : forall {r c} (m : mat r c), Aone c* m == m.
  Proof.
    intros. destruct m; simpl.
    unfold meq; simpl. unfold dmap.
    apply map_id. intros.
    apply map_id. intros.
    ring.
  Qed.
  
  (* (-a) * m = - (a * m) *)
  Lemma mcmul_neg : forall {r c} a (m : mat r c), (- a)%A c* m == - (a c* m).
  Proof.
    intros. destruct m; simpl.
    unfold meq; simpl. unfold matmapdl; simpl. unfold dmap; simpl.
    rewrite map_map. apply map_ext. intros.
    rewrite map_map. apply map_ext. intros. ring.
  Qed.
  
  (* (-a) * (- m) = (a * m) *)
  Lemma mcmul_neg_mopp : forall {r c} a (m : mat r c),
      (- a)%A c* (- m) == a c* m.
  Proof.
    intros. destruct m; simpl.
    unfold meq; simpl. unfold matmapdl; simpl. unfold dmap; simpl.
    rewrite map_map. apply map_ext. intros.
    rewrite map_map. apply map_ext. intros. ring.
  Qed.

  (** Properties below, need a field structure *)
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv Aeq}.
  Context `{Dec_Aeq:Decidable A Aeq}.
  
  (** k * m = 0 -> (m = 0) \/ (k = 0) *)
  Lemma mcmul_eq0_imply_m0_or_k0 : forall {r c} (m : mat r c) k,
      let m0 := mat0 Azero in
      (k c* m == m0) -> (m == m0) \/ (k == Azero)%A.
  Proof.
    intros. unfold mcmul, meq in *; simpl in *.
    destruct m as [dl HH HW]; simpl in *.
    unfold dlzero, dmap in *.
    apply dlcmul_zero_imply_k0_or_dlzero in H; auto. tauto.
  Qed.

  (** (m <> 0 \/ k * m = 0) -> k = 0 *)
  Lemma mcmul_mnonzero_eq0_imply_k0 : forall {r c} (m : mat r c) k,
      let m0 := mat0 Azero in
      ~(m == m0) -> k c* m == m0 -> (k == Azero)%A.
  Proof.
    intros. apply mcmul_eq0_imply_m0_or_k0 in H0; auto. tauto.
  Qed.

  (** k * m = m -> k = 1 \/ m = 0 *)
  Lemma mcmul_same_imply_coef1_or_mzero : forall {r c} k (m : mat r c),
      k c* m == m -> (k == Aone)%A \/ (m == mat0 Azero).
  Proof.
    intros. destruct m. unfold mcmul,meq in *; simpl in *.
    apply (dlcmul_fixpoint_imply_k1_or_dlzero (r:=r) (c:=c)) in H; auto.
  Qed.
  
  (** (m1 <> 0 /\ m2 <> 0 /\ k * m1 = m2) -> k <> 0 *)
  Lemma mcmul_eq_mat_implfy_not_k0 : forall {r c} (m1 m2 : mat r c) k,
      let m0 := mat0 Azero in
      ~(m1 == m0) -> ~(m2 == m0) -> k c* m1 == m2 -> ~(k == Azero)%A.
  Proof.
    intros. intro. destruct m1,m2. unfold meq in *; simpl in *. unfold dmap in *.
    rewrite (map_ext) with (g:=map (fun x=>Azero)) (l:=mdata0) in H1.
    - setoid_rewrite dmap_eq_zero with (dl:=mdata0) in H1.
      (* ToDo: why can not use "rewrite"? *)
      rewrite H1 in H0. destruct H0; easy. auto. auto.
    - intros. apply map_ext. intros. rewrite H2. ring.
  Qed.
  

End mcmul_mmulc_mmul.

(* Arguments mmul Azero Aadd Amul {r c t}. *)
(* Arguments mcmul Amul {r c}. *)
(* Arguments mmulc Amul {r c}. *)


(** ** Matrix_1x1 to scalar *)
Section mat_1_1_to_scalar.

  Context {A:Type}.
  Variable Azero : A.
  
  Definition mat_1_1_to_s (m : @mat A 1 1) : A.
  Proof.
    destruct m as [dl].
    refine (hd Azero (hd [] dl)).
  Defined.
  
End mat_1_1_to_scalar.

(* Arguments mat_1_1_to_s {A}. *)


(** ** Convert from list list to mat *)

Section l2m.
  Context `{Equiv_Aeq:Equivalence A Aeq}.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  Variable Azero : A.
  
  (** list to fixed-length list *)
  Fixpoint l2v_aux (l : list A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n' => (hd Azero l) :: (l2v_aux (tl l) n')
    end.
  
  Lemma l2v_aux_length : forall (l : list A) (n : nat),
      length (l2v_aux l n) = n.
  Proof.
    intros l n. gd l. induction n; intros; simpl; auto.
  Qed.
  
  Lemma l2v_aux_eq : forall (l : list A) (n : nat) 
                            (H1 : length l = n), (l2v_aux l n == l)%list.
  Proof.
    intros l n. gd l. induction n; intros; simpl.
    - apply (length_zero_iff_nil (Aeq:=Aeq)) in H1. easy.
    - destruct l. easy. inv H1. apply cons_aeq_mor; auto. simpl. easy.
  Qed.
  
  (* list list to fixed-shape list list *)
  Fixpoint l2m_aux (dl : list (list A)) (r c : nat) : list (list A)
    := match r with
       | 0 => []
       | S n' => (l2v_aux (hd nil dl) c) :: (l2m_aux (tl dl) n' c)
       end.
  
  Lemma l2m_aux_length : forall (dl : list (list A)) (r c : nat),
      length (l2m_aux dl r c) = r.
  Proof.
    intros dl r. gd dl. induction r; intros; simpl; auto.
  Qed.
  
  Lemma l2m_aux_width : forall (dl : list (list A)) (r c : nat),
      width (l2m_aux dl r c) c.
  Proof.
    unfold width; intros dl r. revert dl.
    induction r; intros; simpl; auto. constructor; auto.
    apply l2v_aux_length.
  Qed.
  
  Lemma l2m_aux_eq : forall (dl : list (list A)) (r c : nat) 
                            (H1 : length dl = r) (H2 : width dl c),
      (l2m_aux dl r c == dl)%dlist.
  Proof.
    intros dl r. gd dl. induction r; intros; simpl; auto.
    - apply (length_zero_iff_nil (Aeq:=eqlistA Aeq)) in H1. easy.
    - destruct dl. easy. inv H1. inv H2.
      rewrite IHr; auto. simpl. rewrite l2v_aux_eq; auto. easy.
  Qed.

  Definition l2m (dl : list (list A)) (r c : nat) : mat r c :=
    mk_mat (l2m_aux dl r c) (l2m_aux_length dl r c) (l2m_aux_width dl r c).
  
  Lemma l2m_inj : forall {r c} (d1 d2 : list (list A)),
      length d1 = r -> width d1 c -> 
      length d2 = r -> width d2 c -> 
      ~(d1 == d2)%dlist -> ~(l2m d1 r c == l2m d2 r c).
  Proof.
    intros. unfold l2m. unfold meq; simpl.
    rewrite ?l2m_aux_eq; auto.
  Qed.
  
  Lemma l2m_surj : forall {r c} (m : mat r c), (exists d, l2m d r c == m).
  Proof.
    intros. exists (mdata m). unfold l2m,meq; simpl.
    apply l2m_aux_eq; auto. apply mheight. apply mwidth.
  Qed.

  Context `{R : Ring A Aadd Azero (Aeq:=Aeq)}.
  Infix "+" := (madd (Aadd:=Aadd)) : mat_scope.

  (** m2l (m1 + m2) = (m2l m1) + (m2l m2) *)
  Lemma m2l_madd_homo : forall r c (m1 m2 : mat r c),
      (mdata (m1 + m2) == dmap2 Aadd (mdata m1) (mdata m2))%dlist.
  Proof.
    intros. destruct m1,m2. simpl. unfold matmap2dl. simpl. easy.
  Qed.

End l2m.

(* Arguments l2v_aux {A}. *)
(* Arguments l2m_aux {A}. *)
(* Arguments l2m_aux_length {A}. *)
(* Arguments l2m_aux_width {A}. *)
(* Arguments l2m {A}. *)


(* ======================================================================= *)
(** ** Extra Properties *)
Section Extra.

  Context {A:Type} (Azero:A).
  (** Vector type *)
  Definition vecr n := @mat A 1 n.
  Definition vecc n := @mat A n 1.
  
  (** Construct a matrix with a row vector and a a matrix *)
  Definition mconsr {r c} (v : vecr c) (m : @mat A r c) : @mat A (S r) c.
    destruct v as [v], m as [m].
    refine (mk_mat ((hd [] v) :: m) _ _); simpl; auto.
    unfold width in *. constructor; auto.
    destruct v; try easy. simpl. inv mwidth0. auto.
  Defined.
  
  (** Construct a matrix with a column row vector and a a matrix *)
  Definition mconsc {r c} (v : vecc r) (m : @mat A r c) : @mat A r (S c).
    destruct v as [v], m as [m].
    refine (mk_mat (consc (hdc Azero v) m) _ _).
    - apply consc_length; auto. rewrite hdc_length; auto.
    - apply consc_width; auto. rewrite hdc_length; subst; auto.
  Defined.
  
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

  
  (* Definition det_of_mat_3_3 (m : mat 3 3) : A := *)
  (*   let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) := *)
  (*     m2t_3x3 m in *)
  (*   let b1 := (a11 * a22 * a33)%A in *)
  (*   let b2 := (a12 * a23 * a31)%A in *)
  (*   let b3 := (a13 * a21 * a32)%A in *)
  (*   let c1 := (a11 * a23 * a32)%A in *)
  (*   let c2 := (a12 * a21 * a33)%A in *)
  (*   let c3 := (a13 * a22 * a31)%A in *)
  (*   let b := (b1 + b2 + b3)%A in *)
  (*   let c := (c1 + c2 + c3)%A in *)
  (*     (b - c)%A. *)

  (* Definition skew_sym_mat_of_v3 (v : V3) : mat 3 3. *)
  (* Proof. *)
  (*   destruct (v3_to_t3 v) as [[x y] z]. *)
  (*   refine (mk_mat_3_3  *)
  (*     Azero    (-z)    y *)
  (*     z     Azero     (-x) *)
  (*     (-y)  x       Azero)%A. *)
  (* Defined. *)
  
  (* Definition v3cross (v1 v2 : V3) : vec 3 := (skew_sym_mat_of_v3 v1) * v2. *)
  
  (* Definition so3 (m : mat 3 3) : Prop :=  *)
  (*   let so3_mul_unit : Prop := (m \T) * m = mat1 3 in *)
  (*   let so3_det : Prop := (det_of_mat_3_3 m) = Aone in *)
  (*     so3_mul_unit /\ so3_det. *)

End Extra.


(* ======================================================================= *)
(** ** Matrix Inversion with gauss elimination, by ShenNan. *)
Section MatInv.

  (** fold a sequence to a value *)
  Fixpoint reduce {A} (n: nat) (f: A -> nat -> A) (zero: A) : A :=
    match n with
    | O => zero
    | S n' => f (reduce n' f zero) n'
    end.
  (* reduce 5 f 0 *)
  (* f (reduce 4 f 0) 4 *)
  (* f (f (reduce 3 f 0) 3) 4 *)
  (* f (f (f (reduce 2 f 0) 2) 3) 4 *)
  (* f (f (f (f (reduce 1 f 0) 1) 2) 3) 4 *)
  (* f (f (f (f (f (reduce 0 f 0) 1) 2) 3) 4 *)
  (* f (f (f (f (f 0 1) 2) 3) 4 *)
  (* Compute reduce 5 Nat.add 0. *)

  (* Understand the "reduce" function *)
  Section test.
    (*   R a f 3 *)
    (* = f (R a f 2) 2 *)
    (* = f (f (R a f 1) 1) 2 *)
    (* = f (f (f (R a f 0) 0) 1) 2 *)
    (* = f (f (f a 0) 1) 2 *)
    (* that is: (a0 + f0) + f1 + ... *)
    Let Fixpoint reduce' {A} (a0:A) (f: A -> nat -> A) (n:nat) : A :=
          match n with
          | O => a0
          | S n' => f (reduce' a0 f n') n'
          end.

    Import Reals.
    Let f1 : nat -> R := fun i => INR i.
    (* Compute reduce' R0 (fun r0 i => Rplus r0 (f1 i)) 5. *)
    (* Compute reduce' 0 Nat.add 5. *)

  End test.


  (** 任给两个序列f g，个数n，以及关系R，生成所有这些点对点对上的关系 *)
  Definition pointwise_n {A} (n: nat) (R: relation A) : relation (nat -> A) :=
    fun (f g : nat -> A) => forall (i: nat), i < n -> R (f i) (g i).

  (** 对于序列m1 m2, 若前 S n 个点对上都有关系R，则前 n 个点对上也有关系R。*)
  Lemma pointwise_n_decr {A}:
    forall (n : nat) (m1 m2 : nat -> A) (R : relation A),
      pointwise_n (S n) R m1 m2 -> pointwise_n n R m1 m2.
  Proof. unfold pointwise_n. intuition. Qed.

  
  Context `{F : Field}.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Infix "*" := (mmul (Azero:=Azero)(Aadd:=Aadd)(Amul:=Amul)) : mat_scope.

  (* sum f(0) f(1) ... f(k-1) *)
  Notation sum k f := (reduce k (fun acc x => (acc + f x)%A) Azero).

  (** (m1 * m2)[i,j] = m1.row[i] dot m2.col[j] *)
  Parameter Mtimes_help : forall {m n p} (m1: @mat A m n) (m2: @mat A n p),
    forall i j,
      i < m -> j < p ->
      mnth Azero (m1 * m2) i j = sum n (fun k => ((mnth Azero m1 i k) * (mnth Azero m2 k j))%A).

  (** (f m1 m2)[i,j] = f m1[i,j] m2[i,j] *)
  Parameter Melement_op_help :
    forall {m n} (m1: @mat A m n) (m2: @mat A m n) (op: A -> A -> A),
    forall i j,
      i < m -> j < n ->
      mnth Azero (matmap2 op m1 m2) i j = op (mnth Azero m1 i j) (mnth Azero m2 i j).
  

End MatInv.


(* Import FieldR. *)
(* Module Import MatrixR := MatrixThy FieldDefR. *)

Module coordinate_transform_test.

  Import Reals.
  Open Scope R.
  Open Scope mat_scope.
  
  (* ref:
  https://en.wikipedia.org/wiki/Matrix_(mathematics)#Basic_operations
   *)

  Infix "*" := Rmult : A_scope.
  Infix "+" := Rplus : A_scope.
  Infix "+" := (madd (Aadd:=Rplus)) : mat_scope.
  Infix "*" := (mmul (Aadd:=Rplus) (Amul:=Rmult) (Azero:=R0)) : mat_scope.
  Infix "c*" := (mcmul (Amul:=Rmult)) : mat_scope.
  Notation "m \T" := (mtrans m) : mat_scope.
  Infix "==" := (meq (Aeq:=eq)) : mat_scope.

  Definition m1 := l2m 0 [[1;3;1];[1;0;0]] 2 3.
  Definition m2 := l2m 0 [[0;0;5];[7;5;0]] 2 3.
  Definition m3 := l2m 0 [[1;3;6];[8;5;0]] 2 3.
  Example madd_m1_m2_eq_m3 : m1 + m2 == m3.
  Proof.
    unfold meq; simpl. cbn. repeat constructor; ring.
  Qed.

  Definition m4 := l2m 0 [[1; 8;-3];[4;-2; 5]] 2 3.
  Definition m5 := l2m 0 [[2;16;-6];[8;-4;10]] 2 3.
  Example mscale_2_m4_eq_m5 : 2 c* m4 == m5.
  Proof.
    unfold meq; simpl. cbn. repeat constructor; ring.
  Qed.
  
  Definition m6 := l2m 0 [[1;2;3];[0;-6;7]]   2 3.
  Definition m7 := l2m 0 [[1;0];[2;-6];[3;7]] 3 2.
  Example mtrans_m6_eq_m7 : m6\T == m7.
  Proof.
    unfold meq; simpl. easy.
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
                                          (cos φ * cos θ))%A.
  
  Opaque cos sin.

  Lemma Rx_Ry_Rz_eq_Rbe : (Rz ψ)\T * (Ry θ)\T * (Rx φ)\T == R_b_e_direct.
  Proof.
    unfold meq; simpl. cbn. repeat constructor; ring.
  Qed.
  
End coordinate_transform_test.

