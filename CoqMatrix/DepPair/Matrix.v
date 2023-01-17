(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Recursive Pair 
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. the definition of vec inspired by Coquelicot.
  2. all definitions are polymorphism.
 *)

From CoqExt Require Export SetoidListListExt.

Require Export Arith.   (* minus_plus *)
Require Export Lia.
Require Export FunctionalExtensionality.
Require Export DepPair.Vector.

Open Scope nat_scope.
Open Scope A_scope.
Open Scope vec_scope.
Open Scope mat_scope.

Generalizable Variable A B C Aeq Beq Ceq Aadd Aopp Amul Ainv.


(** ** Definitions of matrix module, it is implemented as a Vector 2 *)
Section mat.
  
  Context {A : Type}.
  
  Definition mat (r c : nat) : Type := @vec (@vec A c) r.

  Lemma mat_r0 (c : nat) (m : mat 0 c) : m = tt.
  Proof.
    destruct m. auto.
  Qed.
  
  Lemma mat_rS (r c : nat) (m : mat (S r) c) : {v & {m' | m = (v, m')}}.
  Proof.
    apply vec_S.
  Qed.
  
End mat.

(* Arguments mat {A}. *)
(* Arguments mat_r0 {A c}. *)
(* Arguments mat_rS {A r c}. *)

Example mat_ex1 : mat 2 3 := [[1;2;3];[4;5;6]].
Example mat_ex2 : mat 2 3 := [[7;8;9];[10;11;12]].
Example mat_ex3 : mat 3 2 := [[1;2];[3;4];[5;6]].

(** ** Equality of two matrices *)
Section meq.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  
  Definition meq {r c} (m1 m2 : mat r c) := veq (Aeq:=veq (Aeq:=Aeq)) m1 m2.

  Lemma meq_equiv : forall r c, Equivalence (meq (r:=r) (c:=c)).
  Proof.
    intros. apply veq_equiv.
  Qed.

  Global Existing Instance meq_equiv.

End meq.


(** ** Construct a matrix with a function *)
Section mmake.
  
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.

  Definition mmake (r c : nat) (f : nat -> nat -> A) : mat r c :=
    vmake r (fun ic => (vmake c (f ic))).
  
  Lemma mmake_row_S : forall {r c : nat} (f : nat -> nat -> A),
      mmake (S r) c f == (vmake c (f 0), mmake r c (fun i j => f (S i) j)).
  Proof.
    unfold mmake,vmake. intros; simpl. split. easy. rewrite vmakeAux_S. easy.
  Qed.
  
End mmake.


(** ** Get (ir,rc) element of a matrix *)
Section mnth.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0 : A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  
  Definition mnth {r c} (m : mat r c) (ir ic : nat) : A := 
    vnth (A0:=A0) ic (vnth (A0:=vconst c A0) ir m).

  (** meq and mnth should satisfy this constraint *)
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> (forall ri ci, ri < r -> ci < c -> (mnth m1 ri ci == mnth m2 ri ci)%A).
  Proof.
    unfold meq, mnth. intros. split; intros.
    - rewrite H. easy.
    - apply (veq_iff_vnth (A0:=vconst c A0)). intros.
      apply (veq_iff_vnth (A0:=A0)). intros. auto.
  Qed.

  Lemma mnth_mmake : forall {r c} f i j,
      i < r -> j < c -> (mnth (mmake r c f) i j == f i j)%A.
  Proof.
    unfold mnth, mmake. intros.
    rewrite vnth_vmake_valid; auto.
    rewrite vnth_vmake_valid; auto. easy.
  Qed.

End mnth.

Arguments mnth {A} A0 {r c}.


(** Convert between matrix and list list *)
Section m2l_l2m.

  Context `{Equiv_Aeq : Equivalence A Aeq} {A0 : A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  
  Fixpoint m2l {r c} : (@mat A r c) -> list (list A) :=
    match r with
    | O => fun (m : @vec (@vec A c) 0) => nil
    | S r' => fun (m : @vec (@vec A c) (S r')) =>
               cons (v2l (fst m)) (m2l (snd m))
    end.

  Fixpoint l2m (dl : list (list A)) (r c : nat) {struct r} : @mat A r c :=
    match r as r0 return (@vec (@vec A c) r0) with
    | 0 => tt
    | S n' => (l2v (A0:=A0) (hd nil dl) c, l2m (tl dl) n' c)
    end.

  Lemma m2l_l2m_id : forall {r c} (dl : list (list A)) (H1 : length dl = r)
                       (H2 : width dl c), (m2l (l2m dl r c) == dl)%dlist.
  Proof.
    induction r; intros; simpl.
    - apply length_zero_iff_nil in H1. subst. easy.
    - destruct dl. easy. inv H1. inv H2. simpl.
      f_equiv; auto. apply v2l_l2v_id. auto.
  Qed.
  
  Lemma l2m_m2l_id : forall {r c} (m : mat r c), l2m (m2l m) r c == m. 
  Proof.
    unfold mat. induction r; intros; vsimp; simpl; auto.
    split; auto. apply l2v_v2l_id.
  Qed.
  
End m2l_l2m.

Arguments m2l {A r c}.
Arguments l2m {A} A0 dl r c.


(** ** Construct a matrix with same element *)
Section mconst.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := (meq (Aeq:=Aeq)) : A_scope.
  
  Definition mconst (r c : nat) (a : A) : mat r c := mmake r c (fun _ _ => a).

  Lemma mconst_r0 {c} a : mconst 0 c a = tt.
  Proof.
    auto.
  Qed.

  Lemma mconst_rS {r c} a : (mconst (S r) c a == (vconst c a, mconst r c a)).
  Proof.
    split; simpl.
    - apply vmake_const_eq_vconst.
    - rewrite vmakeAux_S. easy.
  Qed.

  Lemma mconst_c0 {r} a : mconst r 0 a == vec0 tt r.
  Proof.
    unfold mconst,mmake,vmake. rewrite vmakeAux_const_eq_vconst. easy.
  Qed.

  Lemma mat_c0 {r : nat} (m : mat r 0) : m == vec0 tt r.
  Proof.
    induction r; simpl; auto. destruct m; auto.
  Qed.
  
End mconst.


(** ** Construct a matrix with a vector and a matrix *)
Section mcons.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  
  (** Construct by row *)
  Definition mconsr {r c} (v : @vec A c) (m : @mat A r c) : @mat A (S r) c :=
    (v, m).
  
  (** Construct by column *)
  Fixpoint mconsc {r c} : vec r -> @mat A r c -> @mat A r (S c) :=
    match r with
    | O => fun (v : vec 0) (m : mat 0 c) => tt
    | S r' => fun (v : vec (S r')) (m : mat (S r') c) =>
               ((fst v, fst m), mconsc (snd v) (snd m))
    end.

  Infix "@" := mconsc : mat_scope.

  (** mconsc is proper morphism *)
  Lemma mconsc_aeq_mor : forall r c : nat,
      Proper (veq (Aeq:=Aeq)(n:=r) ==>
                veq (Aeq:=veq (Aeq:=Aeq)(n:=c)) ==>
                veq (Aeq:=veq (Aeq:=Aeq)(n:=S c))) mconsc.
  Proof.
    unfold Proper, respectful.
    induction r; intros; vsimp; simpl; auto. split; auto. apply IHr; auto.
  Qed.

  Global Existing Instance mconsc_aeq_mor.
  
  (** Equality of two forms of ConstructByRow *)
  Lemma mconsr_eq {r c} (v : vec c) (m : mat r c) : mconsr v m == (v, m).
  Proof.
    simpl. split; easy.
  Qed.
  
  (** Construct a matrix by rows with the matrix which row number is 0 *)
  Lemma mconsr_mr0 : forall {n} (v : vec n) (m : mat 0 n), mconsr v m == [v].
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** Construct a matrix by rows with the matrix which row column is 0 *)
  Lemma mconsr_mc0 : forall {n} (v : vec 0) (m : mat n 0), mconsr v m == (tt, m).
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** Construct a matrix by columns with the matrix which row number is 0 *)
  Lemma mconsc_mr0 : forall {n} (v : vec 0) (m : mat 0 n), v @ m == tt.
  Proof.
    intros. simpl. auto.
  Qed.
  
  (** Note that, mconsc_mc0 is in another section below, it need v2cm *)

  (** Get a row vector of the matrix build by mconsc with v and m, equal to 
      build the vector with two parts which are the n-th element of v and m *)
  Lemma vnth_mconsc : forall r c {A0:A} (v: vec (A:=A) r) (m: mat (A:=A) r c) i,
      (vnth (A0:=vec0 A0 (S c)) i (v @ m) ==
         (vnth (A0:=A0) i v, vnth (A0:=vec0 A0 c) i m))%vec.
  Proof.
    unfold mat; induction r; intros; vsimp; simpl. easy.
    destruct i. easy.
    specialize (IHr c A0 v v1 i).
    (** Tips: We need to handle type conversion manually *)
    (* Set Printing Implicit. *)
    assert (((vnth (A0:=(A0, vec0 A0 c)) i (v @ v1)):(vec (S c)))
            == (vnth (A0:=A0) i v, vnth (A0:=vec0 A0 c) i v1))%vec by auto.
    destruct (vnth (A0:=(A0, vec0 A0 c)) i (v @ v1)). easy.
  Qed.
  
End mcons.


(** ** Get head row, tail rows, head column and tail columns of a matrix *)
Section mhd_mtl.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  Infix "@" := mconsc : mat_scope.

  (** Get head row of a matrix *)
  Definition mhdr {r c} (m : @mat A (S r) c) : vec c := fst m.
  
  (** Get tail rows of a matrix *)
  Definition mtlr {r c} (m : @mat A (S r) c) : @mat A r c := snd m.
  
  (** Get head column of a matrix *)
  Fixpoint mhdc {r c} : @mat A r (S c) -> vec r :=
    match r with
    | O => fun (m : mat 0 (S c)) => tt
    | S r' => fun (m : mat (S r') (S c)) =>
               (fst (fst m), mhdc (snd m))
    end.
  
  (** Get tail columns of a matrix *)
  Fixpoint mtlc {r c} : @mat A r (S c) -> @mat A r c :=
    match r with
    | O => fun (m : mat 0 (S c)) => tt
    | S r' => fun (m : mat (S r') (S c)) =>
               (snd (fst m), mtlc (snd m))
    end.

  (** mhdc is proper morphism *)
  Lemma mhdc_aeq_mor : forall r c,
      Proper (meq (Aeq:=Aeq)(r:=r)(c:=S c) ==> veq (Aeq:=Aeq)(n:=r)) mhdc.
  Proof.
    unfold Proper, respectful, mat.
    induction r; intros; simpl; auto. split.
    - f_equiv. rewrite H. easy.
    - apply IHr. rewrite H. easy.
  Qed.

  Global Existing Instance mhdc_aeq_mor.

  (** mtlc is proper morphism *)
  Lemma mtlc_aeq_mor : forall r c,
      Proper (meq (Aeq:=Aeq)(r:=r)(c:=S c) ==> meq (Aeq:=Aeq)(r:=r)(c:=c)) mtlc.
  Proof.
    unfold Proper, respectful, mat.
    induction r; intros; simpl; auto. split.
    - f_equiv. rewrite H. easy.
    - apply IHr. rewrite H. easy.
  Qed.

  Global Existing Instance mtlc_aeq_mor.

  (** consr (hdr m) (tlr m) = m *)
  Lemma mhdr_mtlr {r c} (m : @mat A (S r) c) : mconsr (mhdr m) (mtlr m) == m.
  Proof.
    destruct m. simpl. easy.
  Qed.

  (** consc (hdc m) (tlc m) = m *)
  Lemma mhdc_mtlc {r c} (m : @mat A r (S c)) : (mhdc m) @ (mtlc m) == m.
  Proof.    
    induction r; destruct m; simpl; auto. destruct v; simpl. split; auto. easy.
  Qed.

  (** hdc (const) = const *)
  Lemma mhdc_const_const_eq_const : forall {r c} a,
      (mhdc (vconst r (vconst (S c) a)) == vconst r a)%vec.
  Proof.
    induction r; intros; simpl; auto. split. easy. apply IHr.
  Qed.
  
  (** Head row of a matrix which constructed by rows *)
  Lemma mhdr_mconsr : forall {r c} (v : @vec A c) (m : @mat A r c),
      (mhdr (mconsr v m) == v)%vec.
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** Tail rows of a matrix which constructed by rows *)
  Lemma mtlr_mconsr : forall {r c} (v : @vec A c) (m : @mat A r c),
      mtlr (mconsr v m) == m.
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** Head column of a matrix which constructed by columns *)
  Lemma mhdc_mconsc : forall {r c} (v : @vec A r) (m : @mat A r c),
      (mhdc (v @ m) == v)%vec.
  Proof.
    induction r; intros; destruct m,v; simpl; auto. easy.
  Qed.
  
  (** Tail columns of a matrix which constructed by columns *)
  Lemma mtlc_mconsc : forall {r c} (v : @vec A r) (m : @mat A r c),
      mtlc (v @ m) == m.
  Proof.
    induction r; intros; destruct m,v; simpl; auto. easy.
  Qed.

  (** The n-th of a vector constructed by mhdc, equal to mnth element. *)
  Lemma vnth_mhdc : forall r c {A0 : A} (m : mat (A:=A) r (S c)) i,
      (vnth (A0:=A0) i (mhdc m) == mnth A0 m i 0)%A.
  Proof.
    unfold mat; induction r; intros; vsimp; simpl. easy.
    destruct i. easy.
    unfold mnth in *. simpl. rewrite IHr. simpl. easy.
  Qed.

End mhd_mtl.


(** Convert from a vector to a row matrix or column matrix, and convert the 
 matrix back to a vector *)
Section v2m_m2v.
  
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  
  (* (** Type Conversion *) *)
  (* Definition vv2m {r c} (vv : @vec (@vec A c) r) : @mat A r c := vv. *)
  (* Definition m2vv {r c} (m : @mat A r c) : @vec (@vec A c) r := m. *)
  
  (* Lemma vv2m_eq : forall {r c} (vv : @vec (@vec A c) r), vv = vv2m vv. *)
  (* Proof. intros. easy. Qed. *)
  (* Lemma m2vv_eq : forall {r c} (m : @mat A r c), m = m2vv m. *)
  (* Proof. intros. easy. Qed. *)
  (* Lemma m2vv_vv2m_id : forall {r c} (vv : @vec (@vec A c) r),  *)
  (*     vv == m2vv (vv2m vv). *)
  (* Proof. intros. easy. Qed. *)
  (* Lemma vv2m_m2vv_id : forall {r c} (m : @mat A r c), m = vv2m (m2vv m). *)
  (* Proof. intros. auto. Qed. *)
  
  (** Convert a vector to a row matrix *)
  Definition v2rm {n} (v : @vec A n) : @mat A 1 n := [v].
  
  (** Convert a row matrix to a vector *)
  Definition rm2v {n} (m : @mat A 1 n) : @vec A n := fst m.

  (** Convert a vector to a column matrix *)
  Fixpoint v2cm {n} : @vec A n -> @mat A n 1 :=
    match n with
    | O => fun (v : @vec A 0) => tt
    | S r' => fun (v : @vec A (S r')) => ([fst v], v2cm (snd v))
    end.

  (** Convert a column matrix to a vector *)
  Fixpoint cm2v {n} : @mat A n 1 -> @vec A n :=
    match n with
    | O => fun (m : @mat A 0 1) => let v : @vec A 0 := tt in v
    | S r' => fun (m : @mat A (S r') 1) =>
               let v : @vec A (S r') :=
                 (fst (fst m), cm2v (snd m)) in v
    end.
  
  Lemma v2rm_rm2v_id : forall {n} (m : @mat A 1 n), v2rm (rm2v m) == m.
  Proof.
    unfold mat; induction n; intros; vsimp; simpl; auto. easy.
  Qed.

  Lemma rm2v_v2rm_id : forall {n} (v : @vec A n), (rm2v (v2rm v) == v)%vec.
  Proof.
    unfold mat; induction n; intros; vsimp; simpl; auto. easy.
  Qed.

  Lemma v2cm_cm2v_id : forall {n} (m : @mat A n 1), v2cm (cm2v m) == m.
  Proof.
    unfold mat; induction n; intros; vsimp; simpl; auto. easy.
  Qed.
  
  Lemma cm2v_v2cm_id : forall {n} (v : @vec A n), (cm2v (v2cm v) == v)%vec.
  Proof.
    unfold mat; induction n; intros; vsimp; simpl; auto. easy.
  Qed.
  
  Lemma rm2v_eq_mhdr : forall {n} (m : @mat A 1 n), (rm2v m == mhdr m)%vec.
  Proof.
    unfold mat; induction n; intros; vsimp; simpl; auto. easy.
  Qed.
  
  Lemma cm2v_eq_mhdc : forall {n} (m : @mat A n 1), (cm2v m == mhdc m)%vec.
  Proof.
    unfold mat; induction n; intros; vsimp; simpl; auto. easy.
  Qed.

  Lemma mat_r1_ex_v2rm : forall {n} (m : @mat A 1 n), {v | m == v2rm v}.
  Proof.
    unfold mat; induction n; intros; vsimp; simpl; eauto. exists (a,v). easy.
  Qed.
  
  Lemma mat_c1_ex_v2cm : forall {n} (m : @mat A n 1), {v | m == v2cm v}.
  Proof.
    unfold mat; induction n; intros; vsimp; simpl; eauto.
    destruct (IHn v0). exists (a,x). easy.
  Qed.
  
  (** Construct a matrix by columns with the matrix which column is 0 *)
  Lemma mconsc_mc0 : forall {n} (v : @vec A n) (m : @mat A n 0), mconsc v m == v2cm v.
  Proof.
    unfold mat; induction n; intros; vsimp; simpl; auto. easy.
  Qed.
  
End v2m_m2v.

(* Arguments v2rm {A n}. *)
(* Arguments rm2v {A n}. *)
(* Arguments v2cm {A n}. *)
(* Arguments cm2v {A n}. *)
(* Arguments v2rm_rm2v_id {A n}. *)
(* Arguments rm2v_v2rm_id {A n}. *)
(* Arguments v2cm_cm2v_id {A n}. *)
(* Arguments cm2v_v2cm_id {A n}. *)
(* Arguments rm2v_eq_mhdr {A n}. *)
(* Arguments cm2v_eq_mhdc {A n}. *)
(* Arguments mat_r1_ex_v2rm {A n}. *)
(* Arguments mat_c1_ex_v2cm {A n}. *)
(* Arguments mconsc_mc0 {A n}. *)


(* Transpose a matrix *)
Section mtrans.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  Infix "@" := mconsc : mat_scope.

  Fixpoint mtrans {r c} : @mat A r c -> mat c r :=
    match c with
    | O => fun (m : @mat A r 0) => tt
    | S c' => fun (m : @mat A r (S c')) => (mhdc m, mtrans (mtlc m))
    end.

  Notation "m \T" := (mtrans m) : mat_scope.

  
  (** mtrans is a proper morphism *)
  Lemma mtrans_aeq_mor : forall r c,
      Proper (meq (Aeq:=Aeq)(r:=r)(c:=c) ==> meq (Aeq:=Aeq)(r:=c)(c:=r)) mtrans.
  Proof.
    unfold Proper, respectful.
    intros r c. revert r. induction c; intros; simpl; auto. split; auto.
    - rewrite H. easy.
    - apply IHc. rewrite H. easy.
  Qed.

  Global Existing Instance mtrans_aeq_mor.

  
  (** Head row of a transposed matrix equal to Head column *)
  Lemma mhdr_mtrans_eq_mhdc : forall {r c} (m : @mat A r (S c)),
    (mhdr (m\T) == mhdc m)%vec.
  Proof.
    induction r; intros; try easy.
  Qed.
  
  (** Tail rows of a transposed matrix equal to transposed tail columns *)
  Lemma mtlr_mtrans_eq_mtrans_mtlc : forall {r c} (m : @mat A r (S c)),
    mtlr (m\T) == (mtlc m)\T.
  Proof.
    induction r; intros; try easy.
  Qed.
  
  (** Head column of a transposed matrix equal to Head row *)
  Lemma mhdc_mtrans_eq_mhdr : forall {r c} (m : @mat A (S r) c),
      (mhdc (m\T) == mhdr m)%vec.
  Proof.
    unfold mhdr. destruct m. simpl. induction c; destruct v; simpl; auto.
    split; try easy.
  Qed.
  
  (** Tail columns of a transposed matrix equal to transposed tail rows *)
  Lemma mtlc_mtrans_eq_mtrans_mtlr : forall {r c} (m : @mat A (S r) c),
    mtlc (m\T) == (mtlr m)\T.
  Proof.
    unfold mtlr. induction c; destruct m; simpl; auto. split; try easy.
    rewrite IHc. simpl. easy.
  Qed.

  (** Transpose twice return back *)
  Lemma mtrans_trans : forall {r c} (m : @mat A r c), m\T\T == m.
  Proof.
    induction r; intros; destruct m; simpl; auto.
    rewrite mhdc_mtrans_eq_mhdr. rewrite mtlc_mtrans_eq_mtrans_mtlr.
    rewrite IHr. simpl. easy.
  Qed.
  
  (** Transpose a matrix composed by head column and tail columns, equal to 
      seperately transpose two part of them append by row *)
  Lemma mtrans_hdc_tlc : forall {r c} (m : @mat A r (S c)),
      ((mhdc m) @ (mtlc m))\T == (mhdr (m\T), mtlr (m\T)).
  Proof.
    destruct r; intros; vsimp; simpl. easy. split.
    - split; try easy. rewrite mhdc_mtlc. easy.
    - apply mtrans_aeq_mor. constructor; try easy.
      rewrite mhdc_mtlc. easy.
  Qed.

  (** Transpose a matrix composed by head row and tail rows, equal to 
      seperately transpose two part of them append by column *)
  Lemma mtrans_hdr_tlr : forall {r c} (m : @mat A (S r) c),
      ((mhdr m, mtlr m) : @mat A (S r) c)\T == (mhdc (m\T)) @ (mtlc (m\T)).
  Proof.
    unfold mat. destruct r; intros; vsimp; simpl.
    - induction c; intros; simpl; auto. split; auto. split; easy.
    - induction c; intros; simpl; auto. split; auto. split; easy.
  Qed.
  
  (** Transpose a zero rows matrix *)
  Lemma mtrans_r0 {n} (m : @mat A 0 n) : m\T == vec0 tt n.
  Proof.
    induction n; simpl; auto; f_equal; auto.
  Qed.
  
  (** Transpose a zero columns matrix *)
  Lemma mtrans_c0 {n} (m : @mat A n 0) : m\T == tt.
  Proof.
    induction n; simpl; auto.
  Qed.
  
  (** Transpose a one row matrix *)
  Lemma mtrans_r1 : forall {n} (m : @mat A 1 n), m\T == v2cm (rm2v m).
  Proof. 
    induction n; intros; destruct m; simpl; auto. split; try easy.
    rewrite IHn. simpl. easy.
  Qed.

  (** Transpose a one column matrix *)
  Lemma mtrans_c1 : forall {n} (m : @mat A n 1), m\T == v2rm (cm2v m).
  Proof. 
    destruct n; intros; destruct m; simpl; auto.
    destruct v; destruct v. simpl.
    repeat split; try easy. rewrite cm2v_eq_mhdc. easy.
  Qed.

  (** Transpose a one column matrix created by a vector *) 
  Lemma mtrans_v2cm : forall {n} (v : @vec A n), (v2cm v)\T == v2rm v.
  Proof. 
    destruct n; intros; destruct v; simpl; auto.
    repeat split; try easy.
    rewrite <- cm2v_eq_mhdc. rewrite cm2v_v2cm_id. easy.
  Qed.

  (** Transpose a one row matrix created by a vector *) 
  Lemma mtrans_v2rm : forall {n} (v : @vec A n), (v2rm v)\T == v2cm v.
  Proof. 
    destruct n; intros; destruct v; simpl; auto.
    rewrite mtrans_r1. simpl. easy.
  Qed.
  
  (** Transpose a matrix which build by row *)
  Lemma mtrans_consr : forall {r c} (v : @vec A c) (m : @mat A r c),
      ((v, m) : mat (S r) c)\T == v @ (m\T).
  Proof.
    induction c; intros; destruct v; simpl; auto. easy.
  Qed.

  (** Transpose a matrix which build column *)
  Lemma mtrans_consc : forall {r c} (v : @vec A r) (m : @mat A r c),
      (mconsc v m)\T == (v, m\T).
  Proof.
    destruct r; intros; destruct m,v; simpl; auto. easy.
    rewrite mhdc_mconsc. rewrite mtlc_mconsc. easy.
  Qed.
  
End mtrans.


(** ** Mapping matrix *)
Section mmap.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  
  Fixpoint mmap {r c} (f : A -> A) : mat r c -> mat r c :=
    match r with
    | O => fun (m : mat 0 _) => tt
    | S r' => fun (m : mat (S r') c) => (vmap f (fst m), mmap f (snd m))
    end.

  Fixpoint mmap2 {r c} (f : A -> A -> A) : mat r c -> mat r c -> mat r c :=
    match r with
       | O => fun (m1 m2 : mat 0 _) => tt
       | S r' => fun (m1 m2 : mat (S r') c) => 
                   (vmap2 f (fst m1) (fst m2), mmap2 f (snd m1) (snd m2))
       end.

  Lemma mmap2_comm : forall {r c} (m1 m2 : mat r c) (f : A -> A -> A)
                       (Comm : forall a b, (f a b == f b a)%A),
    mmap2 f m1 m2 == mmap2 f m2 m1.
  Proof.
    unfold mat. induction r,c; intros; vsimp; simpl; auto. split; try easy.
    - split; try easy. apply vmap2_comm. constructor. auto.
    - apply IHr; auto.
  Qed.

  Lemma mmap2_assoc : forall {r c} (m1 m2 m3 : mat r c) (f : A -> A -> A)
                        (Assoc : forall a b c, (f (f a b) c == f a (f b c))%A),
      mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
  Proof.
    unfold mat. induction r,c; intros; vsimp; simpl; auto. split; try easy.
    - split; try easy. apply vmap2_assoc. constructor. auto.
    - apply IHr; auto.
  Qed.

End mmap.


(** ** Zero matrix *)
Section mat0.

  Context `{Equiv_Aeq : Equivalence A Aeq} (A0 : A).
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope. 
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  Notation "m \T" := (mtrans m) : mat_scope.
  
  Definition mat0 r c : @mat A r c := mmake r c (fun i j => A0).
  
  Lemma mat0_eq_vec0 {r c} : mat0 r c == vec0 (vec0 A0 c) r.
  Proof.
    unfold mat0. unfold mmake.
    rewrite vmake_const_eq_vconst. unfold vec0. f_equiv.
    apply vmake_const_eq_vconst.
  Qed.
  
  Lemma mat0_S : forall {r c}, mat0 (S r) c == ((vec0 A0 c, mat0 r c) : mat (S r) c).
  Proof.
    intros. rewrite mat0_eq_vec0. simpl. split; try easy.
    rewrite mat0_eq_vec0. easy.
  Qed.

  (** mhdr (mat0) = vec0 *)
  Lemma mhdr_mat0 : forall {r c}, (mhdr (mat0 (S r) c) == vec0 A0 c)%vec.
  Proof.
    intros. simpl. apply vmake_const_eq_vconst.
  Qed.
  
  (** mhdc (mat0) = vec0 *)
  Lemma mhdc_mat0 : forall {r c}, (mhdc (mat0 r (S c)) == vec0 A0 r)%vec.
  Proof.
    induction r; intros; simpl; auto. split; try easy. rewrite <- IHr.
    f_equiv. cbn. apply vmakeAux_S.
  Qed.
  
  (** mtlr (mat0) = mat0 *)
  Lemma mtlr_mat0 : forall {r c}, mtlr (mat0 (S r) c) == mat0 r c.
  Proof.
    intros. simpl. apply vmakeAux_S.
  Qed.
  
  (** mtlc (mat0) = mat0 *)
  Lemma mtlc_mat0 : forall {r c}, mtlc (mat0 r (S c)) == mat0 r c.
  Proof.
    induction r; intros; simpl; auto. split.
    - apply vmakeAux_S.
    - cbn. unfold mat0,mmake,vmake in *.
      rewrite (vmakeAux_S r 0 (fun _ => vmakeAux c 0 (fun _ => A0))).
      rewrite <- IHr. f_equiv.
      simpl. apply vmakeAux_S.
  Qed.
  
  (** v2cm (vec0) = mat0 *)
  Lemma v2cm_vec0_eq_mat0 : forall {n}, v2cm (vec0 A0 n) == mat0 n 1.
  Proof.
    unfold mat. induction n; intros; vsimp; simpl; auto. split; try easy.
    rewrite IHn. cbn. unfold mat0, mmake, vmake.
    apply symmetry. simpl. apply vmakeAux_S.
  Qed.
  
  (** v2rm (vec0) = mat0 *)
  Lemma v2rm_vec0_eq_mat0 : forall {n}, v2rm (vec0 A0 n) == mat0 1 n.
  Proof.
    intros. unfold v2rm. unfold mat0,mmake. simpl.
    rewrite vmake_const_eq_vconst. easy.
  Qed.

  (** mat0\T = mat0 *)
  Lemma mtrans_mat0 : forall {r c}, (mat0 r c)\T == mat0 c r.
  Proof.
    intros r c. revert r. induction c; intros; simpl; auto. split.
    - rewrite mhdc_mat0. rewrite vmake_const_eq_vconst. easy.
    - rewrite mtlc_mat0. rewrite IHc.
      unfold mat0,mmake,vmake. rewrite vmakeAux_S. easy.
  Qed.

End mat0.


(** ** Unit matrix *)
Section mat1.
  
  Context `{Equiv_Aeq : Equivalence A Aeq} (A0 A1 : A).
  Infix "==" := Aeq : A_scope. 
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope. 
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope. 
  Notation "m \T" := (mtrans m) : mat_scope.

  Fixpoint mat1 n : mat n n :=
    match n with
    | O => tt
    | S n' =>
        let v1 := vconst n' A0 in
        mconsr ((A1, v1) : vec (S n')) (mconsc v1 (mat1 n'))
    end.
  
  (** mat1\T = mat1 *)
  Lemma mtrans_mat1 : forall {n}, (mat1 n)\T == mat1 n.
  Proof.
    induction n; simpl; auto. split.
    - split. easy. rewrite mhdc_mconsc. easy.
    - rewrite mtlc_mconsc. rewrite mtrans_consr.
      rewrite IHn. easy.
  Qed.
  
  (** Another definition of mat1, function style instead of structure style,
      similiar to mat0 *)
  Definition mat1f n : mat n n := 
    mmake n n (fun ri ci => if ri =? ci then A1 else A0) .

  Lemma mat1_eq_mat1f : forall n, mat1 n == mat1f n.
  Proof.
    induction n; simpl; auto. split; auto.
    - split; auto. easy. rewrite vmakeAux_S. rewrite vmakeAux_const_eq_vconst. easy.
    - apply (veq_iff_vnth (A0:=vec0 A0 (S n))). intros.
      rewrite IHn. rewrite vmakeAux_S.
      rewrite vnth_mconsc.
      rewrite vnth_vmakeAux_valid by lia. simpl. split; auto.
      + rewrite vnth_const; auto. easy.
      + unfold mat1f, mmake.
        rewrite vnth_vmake_valid; auto. unfold vmake. rewrite vmakeAux_S.
        f_equiv. hnf. intros; subst.
        rewrite Nat.add_0_r. easy.
  Qed.
End mat1.


(** ** Get row or column of a matrix as a vector *)
Section mrow_mcol.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0 : A}.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope. 
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope. 

  (* Note that, mhdr and mtlr is a bit different, they only working on "mat (S r) c"
     type. Here, mrow and mcol are designed for "mat r c" type. *)
  
  Definition mrow {r c} ir (m : @mat A r c) : vec c :=
    vnth (A0:=vec0 A0 c) ir m.

  Fixpoint mcol {r c} (ic : nat) : @mat A r c -> vec r :=
    match r with
    | O => fun (m : mat 0 _) => tt
    | S r' => fun (m : mat (S r') c) => 
                (vnth (A0:=A0) ic (fst m), mcol ic (snd m))
    end.

  Lemma mrow_0 {r c} (m : @mat A (S r) c) : (mrow 0 m == mhdr m)%vec.
  Proof.
    destruct m. simpl. easy.
  Qed.

  Lemma mrow_S {r c} i (m : @mat A (S r) c) : (mrow (S i) m == mrow i (mtlr m))%vec.
  Proof.
    destruct m. simpl. easy.
  Qed.

  Lemma mcol_0 {r c} (m : @mat A r (S c)) : (mcol 0 m == mhdc m)%vec.
  Proof.
    induction r; destruct m; simpl; auto. easy.
  Qed.

  Lemma mcol_S {r c} i (m : @mat A r (S c)) : (mcol (S i) m == mcol i (mtlc m))%vec.
  Proof.
    induction r; destruct m; simpl; auto. easy.
  Qed.

End mrow_mcol.


(** ** Append two matrix with same column number or row number *)
Section mapp.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope. 
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope. 

  (** Append two matrix with same column number by row *)
  Definition mappr {r1 r2 c} (m1 : @mat A r1 c) (m2 : @mat A r2 c)
    : @mat A (r1 + r2) c := vapp m1 m2.

  (** Append two matrix with same row number by column *)
  Fixpoint mappc {r c1 c2} : @mat A r c1 -> @mat A r c2 -> @mat A r (c1 + c2) :=
    match r with
    | O => fun _ _ => tt
    | S r' => fun (m1 : mat (S r') c1) (m2 : mat (S r') c2) =>
               (vapp (fst m1) (fst m2), mappc (snd m1) (snd m2))
    end.

End mapp.


(** ** Split a matrix to two parts by row or column *)
Section msplit.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0:A}.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope. 
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope. 

  (** Split a matrix to two parts by row *)
  Definition msplitr r1 r2 {c} (m: @mat A (r1+r2) c) 
    : (@mat A r1 c) * (@mat A (r1+r2-r1) c) :=
    (vfirstn (A0:=vconst c A0) r1 m, vskipn r1 m).
  
  (** I can't write this lemma, because of type issue. Fix it below *)
  (* Lemma mappr_msplitr r1 r2 {c} def (m : @mat A (r1+r2) c) : *)
  (*   mappr (msplitr r1 r2 def m) = m. *)
  
  (** Convert Type as well, but too complicated!! *)
  Definition cvtMatShape r1 r2 {c} (m1 : @mat A (r1 + r2 - r1) c) 
    : @mat A r2 c.
  Proof.
    rewrite Nat.add_comm in m1.
    rewrite Nat.add_sub in m1.
    exact m1. 
  Defined.

  Definition msplitr' r1 r2 {c} (m: @mat A (r1+r2) c) 
    : (@mat A r1 c) * (@mat A r2 c) :=
    (vfirstn (A0:=vconst c A0) r1 m, cvtMatShape r1 r2 (vskipn r1 m)).
  
  Lemma mappr_msplitr' r1 r2 {c} (m : @mat A (r1+r2) c) :
    let '(m1,m2) := msplitr' r1 r2 m in
    let m' : @mat A (r1+r2) c := mappr m1 m2 in
    m' == m.
  Proof.
    unfold mat; induction r1,r2; vsimp; simpl in *; auto.
    (* simpl. induction r1. *)
    (* - induction r2; destruct m; simpl. *)
    (*   + unfold cvtMatShape. simpl (0+0-0). unfold eq_rect. Abort. *)
    Abort.
  
  (** Split a matrix to two parts by column *)
  Fixpoint msplitc {r} c1 c2 : 
    (@mat A r (c1+c2)) -> (@mat A r c1) * (@mat A r (c1+c2-c1)) := 
    match r with
    | O => fun (_ : mat 0 (c1+c2)) => (tt, tt)
    | S r' => fun (m : mat (S r') (c1+c2)) =>
                let defV : vec (c1+c2) := vconst (c1+c2) A0 in
                let (m1, m2) := msplitc c1 c2 (vtl m) in
                ((vfirstn (A0:=A0) c1 (vhd defV m), m1), (vskipn c1 (vhd defV m), m2))
    end.
  
End msplit.


(** ** matrix algebra *)
(** matrix addition, opposition, subtraction, scalar multiplication, multiplication *)
Section mat_alg.
  (* Variable A : Type. *)
  (* Variable A0 : A. *)
  (* Variable fadd fmul : A -> A -> A. *)
  (* Variable fadd_comm : forall a b, fadd a b = fadd b a. *)
  (* Variable fmul_comm : forall a b, fmul a b = fmul b a. *)
  (* Variable fadd_assoc : forall a b c, fadd (fadd a b) c = fadd a (fadd b c). *)
  (* Variable fmul_assoc : forall a b c, fmul (fmul a b) c = fmul a (fmul b c). *)
  (* Variable fmul_fadd_dist_l : forall a b c,  *)
  (*     fmul a (fadd b c) = fadd (fmul a b) (fmul a c). *)
  (* Variable fmul_0_l : forall a, fmul A0 a = A0. *)
  (* Variable fadd_0_l : forall a, fadd A0 a = a. *)
  (* Variable fadd_0_r : forall a, fadd a A0 = a. *)

  Context `{AG : AGroup}.

  Infix "+" := Aadd : A_scope.
  Infix "+" := (vadd (Aadd:=Aadd)) : vec_scope.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  Infix "@" := mconsc : mat_scope.
  Notation "m \T" := (mtrans m) : mat_scope.

  
  (** *** Matrix Addition *)
  
  Definition madd {r c} (m1 m2 : @mat A r c) : @mat A r c :=
    vmap2 (vadd (Aadd:=Aadd)) m1 m2.
  Infix "+" := madd : mat_scope.
  Open Scope mat_scope.

  (** madd is proper morphism *)
  Lemma madd_aeq_mor : forall r c,
      Proper (meq (Aeq:=Aeq) ==> meq (Aeq:=Aeq) ==> meq (Aeq:=Aeq))
        (madd (r:=r)(c:=c)).
  Proof.
    intros. apply (vadd_aeq_mor (AG:=vec_AG c)).
  Qed.

  Global Existing Instance madd_aeq_mor.

  (** (v1 @ m1) + (v2 @ m2) = (v1 + v2) @ (m1 + m2) *)
  Lemma madd_mconsc : forall {r c} (v1 v2 : @vec A r) (m1 m2 : mat r c),
      (v1 @ m1) + (v2 @ m2) == (v1 + v2) @ (m1 + m2).
  Proof.
    unfold mat; induction r; intros; vsimp; simpl; auto. split; try easy.
    (* Tips: type issue *)
    Fail rewrite IHr.
    assert (v1 @ v4 + v2 @ v0 == (v1 + v2) @ (v4 + v0)); auto.
  Qed.

  (** m1 + m2 = m2 + m1 *)
  Lemma madd_comm : forall {r c} (m1 m2 : @mat A r c), m1 + m2 == m2 + m1.
  Proof.
    intros. apply (vadd_comm (AG:=vec_AG c)).
  Qed.

  (** (m1 + m2) + m3 = m1 + (m2 + m3) *)
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : @mat A r c), (m1 + m2) + m3 == m1 + (m2 + m3).
  Proof.
    intros. apply (vadd_assoc (AG:=vec_AG c)).
  Qed.

  (** mat0 + m = m *)
  Lemma madd_0_l : forall {r c} (m : @mat A r c), (mat0 A0 r c) + m == m.
  Proof.
    (* Tips: reuse group and vector theory, good example *)
    intros. rewrite mat0_eq_vec0. apply (vadd_0_l (AG:=vec_AG c)).
  Qed.

  (** m + mat0 = m *)
  Lemma madd_0_r : forall {r c} (m : @mat A r c), m + (mat0 A0 r c) == m.
  Proof.
    intros. rewrite mat0_eq_vec0. apply (vadd_0_r (AG:=vec_AG c)).
  Qed.
  
  (** (m1 + m2)\T = m1\T + m2\T *)
  Lemma mtrans_madd : forall {r c} (m1 m2 : @mat A r c), (m1 + m2)\T == m1\T + m2\T.
  Proof.
    induction r; intros.
    - destruct m1,m2. simpl. rewrite ?mtrans_r0. 
      induction c; simpl; auto.
    - destruct m1 as [v1 m1], m2 as [v2 m2].
      rewrite !mtrans_consr. rewrite madd_mconsc. rewrite <- IHr.
      unfold madd. simpl. rewrite mtrans_consr. easy.
  Qed.

  
  (** *** Matrix Opposition *)

  Definition mopp {r c} (m : mat r c) : mat r c := vmap (vopp (Aopp:=Aopp)) m.
  Notation "- m" := (mopp m) : mat_scope.

  (** mopp is proper morphism *)
  Lemma mopp_aeq_mor : forall r c,
      Proper (meq (Aeq:=Aeq) ==> meq (Aeq:=Aeq)) (mopp (r:=r)(c:=c)).
  Proof.
    intros. apply (vopp_aeq_mor (AG:=vec_AG c)).
  Qed.

  Global Existing Instance mopp_aeq_mor.

  (** - (- m) = m *)
  Lemma mopp_mopp : forall {r c} (m : mat r c), - (- m) == m.
  Proof.
    induction r; intros; destruct m; simpl; auto. split; auto.
    - apply vopp_vopp.
    - apply IHr.
  Qed.
  
  
  (** *** Matrix Subtraction *)
  
  Definition msub {r c} (m1 m2 : @mat A r c) : @mat A r c :=
    m1 + (-m2).
  (* vmap2 (vsub fsub) m1 m2. *)
  Infix "-" := msub : mat_scope.
  
  (** msub is proper morphism *)
  Lemma msub_aeq_mor : forall r c,
      Proper (meq (Aeq:=Aeq) ==> meq (Aeq:=Aeq) ==> meq (Aeq:=Aeq)) (msub (r:=r)(c:=c)).
  Proof.
    intros. apply (vsub_aeq_mor (AG:=vec_AG c)).
  Qed.

  Global Existing Instance msub_aeq_mor.

  (** m1 - m2 = - (m2 - m1) *)
  Lemma msub_comm : forall {r c} (m1 m2 : @mat A r c), m1 - m2 == - (m2 - m1).
  Proof.
    intros. apply (vsub_comm (AG:=vec_AG c)).
  Qed.

  (** (m1 - m2) - m3 = m1 - (m2 + m3) *)
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : @mat A r c), (m1 - m2) - m3 == m1 - (m2 + m3).
  Proof.
    intros. apply (vsub_assoc (AG:=vec_AG c)).
  Qed.

  (** mat0 - m = - m *)
  Lemma msub_0_l : forall {r c} (m : mat r c), (mat0 A0 r c) - m == - m.
  Proof.
    intros. rewrite mat0_eq_vec0. apply (vsub_0_l (AG:=vec_AG c)).
  Qed.
  
  (** m - mat0 = - m *)
  Lemma msub_0_r : forall {r c} (m : mat r c), m - (mat0 A0 r c) == m.
  Proof.
    intros. rewrite mat0_eq_vec0. apply (vsub_0_r (AG:=vec_AG c)).
  Qed.

  (** m - m = mat0 *)
  Lemma msub_self : forall {r c} (m : mat r c), m - m == mat0 A0 r c.
  Proof.
    intros. rewrite mat0_eq_vec0. apply (vsub_self (AG:=vec_AG c)).
  Qed.

  
  (** *** Below, we need Ring structure *)
  Context `{R : Ring A Aadd A0 Aopp Amul A1 Aeq}.
  Add Ring ring_inst : make_ring_theory.

  Infix "*" := Amul : A_scope.
  Infix "c*" := (vcmul (Amul:=Amul)) : vec_scope.
  Infix "*c" := (vmulc (Amul:=Amul)) : vec_scope.
  Notation vdot := (vdot (Aadd:=Aadd)(A0:=A0)(Amul:=Amul)).

  
  (** *** Scalar multiplication *)

  (** Left scalar multiplication *)
  Definition mcmul {r c : nat} a m : mat r c := mmap (fun x => a * x) m.
  Infix "c*" := mcmul : mat_scope.

  (** Right scalar multiplication *)
  Definition mmulc {r c : nat} m a : mat r c := mmap (fun x => x * a) m.
  Infix "*c" := mmulc : mat_scope.

  (** m *c a = a c* m *)
  Lemma mmulc_eq_mcmul : forall {r c} (a : A) (m : mat r c), m *c a == a c* m.
  Proof.
    induction r; intros; simpl; auto. split; auto.
    - apply (vmulc_eq_vcmul a).
    - apply IHr. 
  Qed.

  (** a c* (b c* m) = (a * b) c* m *)
  Lemma mcmul_assoc : forall {r c} (a b : A) (m : mat r c),
      a c* (b c* m) == (a * b) c* m.
  Proof.
    induction r; intros; simpl; auto. split; [|apply IHr].
    apply (vcmul_assoc a b).
  Qed.

  (** a c* (b c* m) = b c* (a c* m) *)
  Lemma mcmul_perm : forall {r c} (a b : A) (m : mat r c),
      a c* (b c* m) == b c* (a c* m).
  Proof.
    induction r; intros; simpl; auto. split; [|apply IHr].
    apply (vcmul_perm a b).
  Qed.

  (** a c* (m1 + m2) = (a c* m1) + (a c* m2) *)
  Lemma mcmul_add_distr_l : forall {r c} (a : A) (m1 m2 : mat r c),
      a c* (m1 + m2) == (a c* m1) + (a c* m2).
  Proof.
    induction r; intros; simpl; auto. split; [|apply IHr].
    apply (vcmul_add_distr_l a).
  Qed.

  (** (a + b) c* m = (a c* m) + (b c* m) *)
  Lemma mcmul_add_distr_r : forall {r c} (a b : A) (m : mat r c),
      (a + b)%A c* m == (a c* m) + (b c* m).
  Proof.
    induction r; intros; simpl; auto. split; [|apply IHr].
    apply (vcmul_add_distr_r a).
  Qed.

  (** 0 c* m = mat0 *)
  Lemma mcmul_0_l : forall {r c} (m : mat r c), A0 c* m == mat0 A0 r c.
  Proof.
    induction r; intros; simpl; auto. destruct m. simpl. split.
    - pose proof (vcmul_0_l (n:=c)).
      unfold vcmul in H. rewrite H. rewrite vmake_const_eq_vconst. easy.
    - unfold mcmul in IHr. rewrite IHr.
      rewrite vmakeAux_S. easy.
  Qed.

  (** A1 c* m = m *)
  Lemma mcmul_1_l : forall {r c} (m : mat r c), A1 c* m == m.
  Proof.
    induction r; intros; simpl; auto. destruct m. split; [|apply IHr].
    simpl. apply (vcmul_1_l v).
  Qed.

  (** *** Inner product a vector and a matrix. v(c) *' m(r,c) = v(r) *)

  Fixpoint vdotm {r c} (v : @vec A c) : @mat A r c -> @vec A r :=
    match r with 
    | O => fun (m : mat 0 _) => tt
    | S r' => fun (m : mat (S r') c) => 
               (vdot v (fst m), vdotm v (snd m))
    end.

  (** vdotm is proper morphism *)
  Lemma vdotm_aeq_mor : forall r c : nat,
      Proper (veq (Aeq:=Aeq)(n:=c) ==>
                meq (Aeq:=Aeq)(r:=r)(c:=c) ==>
                veq (Aeq:=Aeq)(n:=r)) vdotm.
  Proof.
    unfold Proper, respectful.
    induction r; intros; vsimp; simpl; auto. split; auto.
    - rewrite H,H0. easy.
    - apply IHr; auto. rewrite H0. easy.
  Qed.

  Global Existing Instance vdotm_aeq_mor.
  
  Lemma vdotm_c0 : forall {n} (v : vec 0) (m : mat n 0), (vdotm v m == (vec0 A0 n))%vec.
  Proof.
    induction n; intros; destruct v; simpl; auto. split; auto.
    destruct m. simpl. cbn. easy.
  Qed.
  
  Lemma vdotm_r0 : forall {n} (v : vec n) (m : mat 0 n), vdotm v m = tt.
  Proof.
    induction n; intros; destruct v,m; simpl; auto.
  Qed.
  
  Lemma vdotm_split : forall {r c} (v : vec c) (m : mat (S r) c),
      (vdotm v m == (vdot v (mhdr m), vdotm v (mtlr m)))%vec.
  Proof.
    induction r; intros; simpl; try easy.
  Qed.

  Lemma vdotm_cons : forall {r c} a (v : vec c) (m : mat r (S c)),
      (@vdotm r (S c) (a, v) m == (a c* (mhdc m)) + (vdotm v (mtlc m)))%vec.
  Proof.
    induction r; intros; destruct m; simpl; auto.
    split; try easy.
    rewrite IHr. easy.
  Qed.
  
  Lemma vdotm_vcmul : forall {r c} a (v : vec c) (m : mat r c),
      (vdotm (a c* v) m == a c* (vdotm v m))%vec.
  Proof.
    induction r; intros; destruct m; simpl; auto. rewrite IHr. split; try easy.
    apply vdot_vcmul_l.
  Qed.
  
  Lemma vdotm_add_distr_l : forall {r c} (v : vec r) (m1 m2 : mat c r),
      (vdotm v (m1 + m2)%mat == (vdotm v m1) + (vdotm v m2))%vec.
  Proof.
    intros r c. revert c.
    induction c; intros; destruct m1,m2; simpl; auto.
    split; try easy. apply vdot_vadd_l.
    rewrite <- IHc. easy.
  Qed.
  
  Lemma vdotm_add_distr_r : forall {r c} (v1 v2 : vec c) (m : mat r c),
      (vdotm (v1 + v2) m == (vdotm v1 m) + (vdotm v2 m))%vec.
  Proof.
    induction r; intros; destruct m; simpl; auto. split; try easy.
    apply vdot_vadd_r.
  Qed.
  
  (** 0 . m = 0 *)
  Lemma vdotm_0_l : forall {r c} (m : @mat A r c),
      (vdotm (vec0 A0 c) m == vec0 A0 r)%vec.
  Proof.
    induction r; intros; simpl; auto. split; [|easy].
    apply vdot_0_l.
  Qed.
  
  (** v . 0 = 0 *)
  Lemma vdotm_0_r : forall {r c} (v : vec c), (vdotm v (mat0 A0 r c) == vec0 A0 r)%vec.
  Proof.
    induction r; intros; simpl; auto. split.
    - rewrite vmake_const_eq_vconst. rewrite vdot_0_r. easy.
    - rewrite vmakeAux_const_eq_vconst.
      rewrite vmake_const_eq_vconst.
      rewrite <- ?vec0_eq_vconst0.
      rewrite <- mat0_eq_vec0.
      auto.
  Qed.
  
  (** v . 1 = v *)
  Lemma vdotm_1_r : forall {n} (v : vec n), (vdotm v (mat1 A0 A1 n) == v)%vec.
  Proof.
    induction n; intros; destruct v; simpl; auto. split.
    - rewrite vdot_S. rewrite vdot_0_r; auto. ring.
    - rewrite vdotm_cons. rewrite mtlc_mconsc. rewrite mhdc_mconsc.
      rewrite IHn. rewrite <- vec0_eq_vconst0. rewrite vcmul_0_r.
      apply vadd_0_l.
  Qed.

  
  (** *** Inner product two matrix. m(r1,c) *' (m(r2,c) = m(r1,r2) *)
  
  Fixpoint mdot {r c t} : (@mat A r c) -> (@mat A t c) -> (@mat A r t) :=
    match r with
    | O => fun (m1 : mat 0 _) m2 => tt
    | S r' => fun (m1 : mat (S r') _) m2 => 
                (vdotm (fst m1) m2, mdot (snd m1) m2)
    end.

  (** mdot is proper morphism *)
  Lemma mdot_aeq_mor : forall r c t : nat,
      Proper (meq (Aeq:=Aeq)(r:=r)(c:=c) ==>
                meq (Aeq:=Aeq)(r:=t)(c:=c) ==>
                meq (Aeq:=Aeq)(r:=r)(c:=t)) mdot.
  Proof.
    unfold Proper, respectful.
    induction r; intros; vsimp; simpl; auto. split; auto.
    - rewrite H,H0. easy.
    - apply IHr; auto. rewrite H. easy.
  Qed.

  Global Existing Instance mdot_aeq_mor.
  
  (** v . m = m . v *)
  Lemma vdotm_comm_mdot : forall {r c} (v : vec c) (m : @mat A r c),
      (vdotm v m == cm2v (mdot m (v2rm v)))%vec.
  Proof.
    induction r; intros; destruct m; simpl; auto. split; auto.
    apply vdot_comm.
  Qed.
  
  Lemma mhdc_mdot_eq_vdotm : forall {r c t} (v : vec c) (m1 : mat r c) (m2 : mat t c), 
    (mhdc (@mdot t c (S r) m2 (v, m1)) == vdotm v m2)%vec.
  Proof.
    induction t; destruct m2; simpl; auto. split; auto.
    apply vdot_comm.
  Qed.
  
  (** tl (m1 . m2) = m1 . (tl m2). *)
  Lemma mtlc_mdot : forall {r c t} (m1 : mat r c) (m2 : mat (S t) c),
      mtlc (mdot m1 m2) == mdot m1 (mtlr m2).
  Proof. 
    induction r; intros; destruct m1,m2; simpl; auto. split; auto.
    easy. apply IHr. 
  Qed.

  (** (v, m1) . m2 = ((v . m2), (m1 . m2)) *)
  Lemma mdot_split_l {r c t} (v : vec c) (m1 : mat r c) (m2 : mat t c) :
    @mdot (S r) c t (v, m1) m2 == ((vdotm v m2), (mdot m1 m2)).
  Proof.
    induction r; destruct m1; simpl; try easy.
  Qed.

  (** (m1 . (v, m2)) = (m1 . v) @ (m1 . m2) *)
  Lemma mdot_split_r {r c t} (v : vec c) (m1 : mat r c) (m2 : mat t c) :
    mdot m1 ((v, m2):mat (S t) c) == (cm2v (mdot m1 (v2rm v))) @ (mdot m1 m2).
  Proof.
    induction r; destruct m1; simpl; auto. rewrite IHr. easy.
  Qed.

  (** m1 . m2 = (m2 . m1)\T *)
  Lemma mdot_comm : forall {r c t} (m1 : @mat A r c) (m2 : @mat A t c),
      mdot m1 m2 == (mdot m2 m1)\T.
  Proof.
    induction r; intros; destruct m1; simpl; auto. split.
    - rewrite mhdc_mdot_eq_vdotm. easy.
    - rewrite IHr. f_equiv. rewrite mtlc_mdot. simpl. easy.
  Qed.

  (** m1[r,0] . m2[c,0] = mat0 *)
  Lemma mdot_c0_c0_eq_mat0 : forall {r c} (m1 : mat r 0) (m2 : mat c 0),
      mdot m1 m2 == mat0 A0 r c.
      (* mdot m1 m2 = vconst r (vec0 A0 c). *)
  Proof.
    induction r; intros; destruct m1; simpl; auto. split.
    - rewrite vdotm_c0. rewrite vmake_const_eq_vconst. easy.
    - rewrite IHr.
      rewrite vmakeAux_const_eq_vconst. rewrite vmake_const_eq_vconst.
      rewrite mat0_eq_vec0. easy.
  Qed.
  
  (** hdr ((v,m1) . m2) = v . m2 *)
  Lemma mhdr_mdot : forall {r c t} (v : vec c) (m1 : mat r c) (m2 : mat t c),
      (mhdr (mdot ((v, m1) : mat (S r) c) m2) == vdotm v m2)%vec.
  Proof.
    induction r; intros; destruct m1; simpl; easy.
  Qed.
  
  (** hdc (m1 . (v, m2)) = v . m1 *)
  Lemma mhdc_mdot : forall {r c t} (m1 : mat r c) (v : vec c) (m2 : mat t c),
      (mhdc (mdot m1 ((v, m2) : mat (S t) c)) == vdotm v m1)%vec.
  Proof.
    induction r; intros; destruct m1; simpl; auto. split; auto.
    apply vdot_comm.
  Qed.

  (** (v . m1) . m2 = v . (m2 . m1\T) *)
  Lemma vdotm_assoc : forall {r c t} (v : vec r) (m1 : mat c r) (m2 : mat t c),
      (vdotm (vdotm v m1) m2 == vdotm v (mdot m2 (m1\T)))%vec.
  Proof.
    induction r; intros; destruct v; simpl.
    - rewrite ?vdotm_0_l. easy.
    - rewrite ?vdotm_cons. rewrite vdotm_add_distr_r. f_equiv.
      + rewrite vdotm_vcmul. rewrite mhdc_mdot. easy.
      + rewrite IHr. rewrite mtlc_mdot. simpl. easy.
  Qed.

  (** (m1 . m2) . m3 == m1 . (m3 . m2\T) *)
  Lemma mdot_assoc : forall {r c t s} (m1: @mat A r c) (m2: @mat A t c) (m3: @mat A s t),
      mdot (mdot m1 m2) m3 == mdot m1 (mdot m3 (m2\T)).
  Proof.
    induction r; intros; destruct m1; simpl; auto. split; auto.
    apply vdotm_assoc.
  Qed.

  (** m1 . (m2 + m3) = (m1 . m2) + (m1 . m3) *)
  Lemma mdot_add_distr_l : forall {r c t} (m1 : @mat A r c) (m2 m3 : @mat A t c),
      mdot m1 (m2 + m3) == (mdot m1 m2) + (mdot m1 m3).
  Proof.
    induction r; intros; destruct m1; simpl; auto. split; auto.
    - apply vdotm_add_distr_l.
    - apply IHr.
  Qed.

  (** (m1 + m2) . m3 = (m1 . m3) + (m2 . m3) *)
  Lemma mdot_add_distr_r : forall {r c t} (m1 m2 : @mat A r c) (m3 : @mat A t c),
      mdot (m1 + m2) m3 == (mdot m1 m3) + (mdot m2 m3).
  Proof.
    induction r; intros; destruct m1; simpl; auto. split; auto.
    - apply vdotm_add_distr_r.
    - apply IHr. 
  Qed.

  (** m . mat0 = mat0 *)
  Lemma mdot_0_r : forall {r c t} (m : @mat A r c), mdot m (mat0 A0 t c) == mat0 A0 r t.
  Proof.
    induction r; intros; destruct m; simpl; auto. split.
    - rewrite vdotm_0_r. rewrite vmake_const_eq_vconst. easy.
    - rewrite IHr. rewrite mat0_eq_vec0.
      rewrite vmakeAux_const_eq_vconst. rewrite vmake_const_eq_vconst. easy. 
  Qed.

  (** mat0 . m = mat0 *)
  Lemma mdot_0_l : forall {r c t} (m : @mat A t c), mdot (mat0 A0 r c) m == mat0 A0 r t.
  Proof.
    intros. rewrite mdot_comm. rewrite mdot_0_r.
    rewrite mtrans_mat0. easy.
  Qed.

  (** mat1 . m = m\T *)
  Lemma mdot_1_l : forall {r c} (m : @mat A r c),
    mdot (mat1 A0 A1 c) m == m\T.
  Proof.
  Abort.

  
  (** *** Vector multiplication (I don't sure what's the exact name?) *)
  (** v1 * v2 : vec r -> vec c -> mat r c.
      Example: 
      (a1 a2) * (b1 b2 b3)
      = [[a1b1 a1b2 a1b3];
         [a2b1 a2b2 a2b3]]
   *)
  Definition vmul {r c} (v1 : @vec A r) (v2 : @vec A c) : @mat A r c :=
    (* mmake r c (fun ri ci => Amul (vnth (A0:=A0) ri v1) (vnth (A0:=A0) ci v2)). *)
    vmake r (fun ri => vcmul (Amul:=Amul) (vnth (A0:=A0) ri v1) v2).

  (* Lemma vmul_aeq_mor : forall (r c:nat), *)
  (*     Proper (veq (Aeq:=Aeq) ==> veq (Aeq:=Aeq) ==> meq (Aeq:=Aeq)) *)
  (*       (vmul (r:=r)(c:=c)). *)
  (*   Admitted. *)
  (* Global Existing Instance vmul_aeq_mor. *)

  (* v1 . (a,v2) = (v1 *c a) @ (v1 . v2) *)
  Lemma vmul_cons_r : forall r c a (v1 : vec r) (v2 :vec c),
      vmul v1 ((a,v2):vec (S c)) == mconsc ((v1 *c a)%vec) (vmul v1 v2).
  Proof.
    induction r; intros; vsimp; simpl; auto. split.
    - split; try easy.
    - unfold vmul in *. unfold vmake in *. unfold vmulc in *.
      (* Tips: type issue. because "vec (S c)" is diff with "(prod A (@vec A c))" *)
      Fail rewrite vmakeAux_S.
      (* Check (prod A (@vec A c)). *)
      
      (* So, manually type issue *)
      assert (vmakeAux r 1
                (fun ri : nat => (match ri with
                              | 0 => a0
                              | S i' => vnth (A0:=A0) i' v
                              end c* v2)%vec) ==
                vmakeAux r 0 (fun ri => (vnth (A0:=A0) ri v) c* v2)%vec)
        by apply vmakeAux_S. rewrite H; clear H.
      assert (vmakeAux r 1
                (fun ri : nat => (match ri with
                              | 0 => a0
                              | S i' => vnth (A0:=A0) i' v
                              end c* ((a, v2):vec (S c)))%vec) ==
                vmakeAux r 0 (fun ri => (vnth (A0:=A0) ri v) c* ((a, v2):vec (S c)))%vec)
        by apply vmakeAux_S. rewrite H; clear H.
      rewrite IHr. easy.
  Qed.

  (** Tail column of a matrix build by vmakeAux, equal to a matrix build by
      vmakeAux directly *)
  Lemma mtlc_vmakeAux : forall (r c r_ofst : nat) (f : nat -> vec (S c)),
      mtlc (vmakeAux r r_ofst (fun ri => f ri)) ==
        vmakeAux r r_ofst (fun ri => (vtl (f ri))).
  Proof.
    induction r; intros; simpl; auto. split. easy.
    rewrite IHr. easy.
  Qed.

  (** Tail column of a matrix build by vmake, equal to a matrix build by
      vmake directly *)
  Lemma mtlc_vmake : forall (r c : nat) (f : nat -> vec (S c)),
      mtlc (vmake r (fun ri => f ri)) == vmake r (fun ri => (vtl (f ri))).
  Proof.
    intros. unfold vmake. rewrite mtlc_vmakeAux. easy.
  Qed.

  (** vmul v1 v2 = (vmul v2 v1)\T *)
  Lemma vmul_comm_eq_trans_comm : forall r c (v1 : vec r) (v2 : vec c),
      vmul v1 v2 == (vmul v2 v1)\T.
  Proof.
    induction r; intros; simpl; auto. vsimp; simpl. split.
    - rewrite vmul_cons_r. rewrite mhdc_mconsc.
      rewrite vmulc_eq_vcmul. easy.
    - unfold vmul in *. unfold vmake in *.
      rewrite vmakeAux_S. rewrite IHr. f_equiv.
      unfold vcmul. simpl.
      rewrite mtlc_vmakeAux. simpl. f_equiv.
  Qed.

  (** vmul vec0 v = mat0 *)
  Lemma vmul_0_l : forall r c (v : vec c), vmul (vec0 A0 r) v == mat0 A0 r c.
  Proof.
    induction r; intros; vsimp; simpl; auto. split; auto.
    - rewrite vcmul_0_l. rewrite vmake_const_eq_vconst. easy.
    - rewrite ?vmakeAux_S.
      apply (veq_iff_vnth (A0:=vec0 A0 c)). intros.
      rewrite ?vnth_vmakeAux_valid by lia.
      unfold vec0. rewrite vnth_const by lia. rewrite vcmul_0_l.
      rewrite vmake_const_eq_vconst. easy.
  Qed.

  (** vmul v vec0 = mat0 *)
  Lemma vmul_0_r : forall r c (v : vec r), vmul v (vec0 A0 c) == mat0 A0 r c.
  Proof.
    intros. rewrite vmul_comm_eq_trans_comm. rewrite vmul_0_l.
    rewrite mtrans_mat0. easy.
  Qed.

  (** mdot (v1 @ m1) (v2 @ m2) = (vmul v1 v2) + (mdot m1 m2). *)
  Lemma mdot_consc_consc : forall r c s (v1: vec r) (m1: mat r c) (v2: vec s) (m2: mat s c),
      mdot (v1 @ m1) (v2 @ m2) == (vmul v1 v2) + (mdot m1 m2).
  Proof.
    unfold mat; induction r; intros; vsimp; simpl; auto. split.
    - rewrite vdotm_cons. rewrite mhdc_mconsc. rewrite mtlc_mconsc. easy.
    - rewrite IHr.
      (* Tips: here, a subtle problem. we shouldn't use "unfold madd".
         If we do it, after "f_equiv", we cannot prove.
         Because typeclasses issue.
         The details could be checked after "Set Printing All".
         We can find the "eq" and "Aeq" differences *)
      (* unfold madd. *)
      f_equiv.
      rewrite vmakeAux_S. unfold vmul. unfold vmake. f_equiv.
  Qed.


  (** *** Matrix Multiplication. m1(r,c) * m2(c,t) = m(r,t) *)
  
  Definition mmul {r c s} (m1 : @mat A r c) (m2 : @mat A c s) : @mat A r s :=
    mdot m1 (m2\T).
  Infix "*" := mmul : mat_scope.

  (** (m1 * m2)\T = m2\T * m1\T *)
  Lemma mmul_trans : forall {r c s} (m1 : @mat A r c) (m2 : @mat A c s),
      (m1 * m2)\T == (m2\T) * (m1\T).
  Proof.
    intros. unfold mmul. rewrite <- mdot_comm. rewrite mtrans_trans. easy.
  Qed.

  (** (m1 * m2) * m3 = m1 * (m2 * m3) *)
  Lemma mmul_assoc : forall {r c s t} (m1: @mat A r c) (m2: @mat A c s) (m3: @mat A s t),
      (m1 * m2) * m3 == m1 * (m2 * m3).
  Proof.
    intros. unfold mmul. rewrite <- mdot_comm.
    rewrite mdot_assoc. rewrite mtrans_trans. easy.
  Qed.

  (** m1 * (m2 + m3) = (m1 * m2) + (m1 * m3) *)
  Lemma mmul_add_distr_l : forall {r c s} (m1 : mat r c) (m2 m3 : mat c s), 
      m1 * (m2 + m3) == (m1 * m2) + (m1 * m3).
  Proof.
    intros. unfold mmul. rewrite mtrans_madd.
    rewrite mdot_add_distr_l. easy.
  Qed.

  (** (m1 + m2) * m3 = (m1 * m3) + (m2 * m3) *)
  Lemma mmul_add_distr_r : forall {r c s} (m1 m2 : mat r c) (m3 : mat c s), 
      (m1 + m2) * m3 == (m1 * m3) + (m2 * m3).
  Proof.
    intros. unfold mmul. rewrite mdot_add_distr_r. easy.
  Qed.

  (** (v1, m1) * m2 = ((v1 . m2\T), m1 * m2) *)
  Lemma mmul_consr_l : forall {r c s} (v1 : vec c) (m1 : mat r c) (m2 : mat c s),
      ((v1, m1) : mat (S r) c) * m2 == (vdotm v1 (m2\T), m1 * m2).
  Proof.
    intros. unfold mmul. rewrite mdot_split_l. easy.
  Qed.
  
  (* a difficult lemma *)
  (** (v1 @ m1) * (v2, m2) = [v1^T]*[v2] + m1 * m2 *)
  Lemma mmul_consc_consr : forall {r c s} (v1 : vec r) (m1 : mat r c) (v2 : vec s)
                             (m2 : mat c s),
      (v1 @ m1) * (v2, m2) == ((v2cm v1) * (v2rm v2)) + (m1 * m2).
  Proof.
    unfold mmul. 
    induction r.
    - intros; simpl; auto.
    - induction c; intros; simpl.
      + destruct v1,m1,m2. destruct v0. simpl. split.
        * rewrite vdotm_0_l. rewrite vadd_0_r. easy.
        * rewrite IHr. rewrite mdot_c0_c0_eq_mat0.
          rewrite ?madd_0_r.
          (* Tips: manually type conversion *)
          assert (vmap2 (vadd (Aadd:=Aadd)) (mdot (v2cm v) (v2rm v2 \T)) (mat0 A0 r s)
                  == madd (mdot (v2cm v) (v2rm v2 \T)) (mat0 A0 r s)).
          { easy. }
          rewrite H. rewrite madd_0_r. easy.
      + destruct v1,m1,m2. destruct v0. simpl. split; try apply IHr.
        rewrite vdotm_cons. rewrite vdotm_cons.
        rewrite mhdc_mtrans_eq_mhdr. simpl.
        unfold v2rm; simpl. rewrite ?vdotm_cons.
        rewrite ?mtlc_mtrans_eq_mtrans_mtlr. simpl.
        rewrite ?mhdc_mtrans_eq_mhdr. simpl.
        rewrite vdotm_c0. rewrite vadd_0_r.        
        rewrite <- vadd_assoc. easy.
  Qed.

  (** mat0 * m = mat0 *)
  Lemma mmul_0_l : forall {r c t} (m : mat c t), (mat0 A0 r c) * m == mat0 A0 r t.
  Proof.
    intros. unfold mmul. rewrite mdot_0_l. easy.
  Qed.

  (** m * mat0 = mat0 *)
  Lemma mmul_0_r : forall {r c t} (m : mat r c), m * (mat0 A0 c t) == mat0 A0 r t.
  Proof.
    intros. unfold mmul. rewrite mtrans_mat0. rewrite mdot_0_r. easy.
  Qed.

  (** m * mat1 = m *)
  Lemma mmul_1_r : forall {r c} (m : mat r c), m * (mat1 A0 A1 c) == m.
  Proof.
    induction r; intros; destruct m; simpl; auto. split.
    - rewrite mtrans_mat1. rewrite vdotm_1_r. easy.
    - apply IHr.
  Qed.

  (** mat1 * m = m *)
  Lemma mmul_1_l : forall {r c} (m : mat r c), (mat1 A0 A1 r) * m == m.
  Proof.
    induction r; intros; destruct m; simpl; auto. split.
    - rewrite vdotm_cons. rewrite vdotm_0_l. rewrite vadd_0_r.
      rewrite mhdc_mtrans_eq_mhdr. simpl. rewrite vcmul_1_l. easy.
    - rewrite mtrans_consr.
      rewrite mdot_consc_consc.
      unfold mmul in IHr. rewrite IHr.
      rewrite vmul_0_l. apply madd_0_l.
  Qed.

  (** *** Row-vector multiply a matrix, or matrix multiply column-vector.
      1. v(r) converted to mv(1,r)
      2. v(r) * m(r,c) = mv(1,r) * m(r,c) = m'(1,c) *)

  Definition vmulm {r c} (v : @vec A r) (m : @mat A r c) : (@mat A 1 c) :=
    (v2rm v) * m.
  
  Definition mmulv {r c} (m : @mat A r c) (v : @vec A c) : @mat A r 1:=
    m * (v2cm v).
  
End mat_alg.

