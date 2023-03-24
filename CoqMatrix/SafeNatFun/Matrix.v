(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Function (Safe version)
  author    : ZhengPu Shi
  date      : 2021.12
  remark    :
  1. This is the safe version of NatFun implementation, that means,
     we modified the definition of matrix type to improve the type safety.
     Though the modification is minor, but all the related scipts need to
     be rewritten.
  2. The old definition of matrix type is:
         Definition mat {A} (r c : nat) := nat -> nat -> A.
     while new definition of matrix type is:
         Record mat {A} (r c : nat) := mk_mat {
           matf : nat -> nat -> A
         }.
 *)


Require Export TupleExt HierarchySetoid SetoidListListExt.
Require Export Sequence.


Generalizable Variable A B C Aeq Beq Ceq Aadd Aopp Amul Ainv.

(** Control the scope *)
Open Scope nat_scope.
Open Scope A_scope.
Open Scope mat_scope.


(* ==================================== *)
(** ** Matrix type *)
Section Def.

  (** We define a _matrix_ as a record which contain only one filed _matf_,
      and that is a function of "nat -> nat -> A" type.
      Meanwhile, we give two arguments r and c as the parts of mat type to represent 
      the rows and columns of a matrix. *)
  Record mat {A} (r c : nat) :=
    mk_mat {
        matf : nat -> nat -> A
      }.

  (** square matrix *)
  Definition smat {A} n := @mat A n n.
  
End Def.

Arguments mk_mat {A r c}.
Arguments matf {A r c}.


(* ==================================== *)
(** ** Equality of matrix *)
Section meq.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  
  (** Two matrices are considered equal if each corresponding element
      whose index is in the bounds is equal.  *)
  Definition meq {r c : nat} (m1 m2 : mat r c) : Prop := 
    forall i j, i < r -> j < c -> matf m1 i j == matf m2 i j.
  Infix "==" := meq : mat_scope.
  
  Lemma meq_refl : forall {r c} (m : mat r c), m == m.
  Proof.
    intros. intros i j Hi Hj. easy.
  Qed.
  
  Lemma meq_sym : forall {r c} (m1 m2 : mat r c), m1 == m2 -> m2 == m1.
  Proof.
    intros r c m1 m2 H1. unfold meq in *. intros i j Hi Hj.
    apply symmetry. apply H1; auto.
  Qed.
  
  Lemma meq_trans : forall {r c} (m1 m2 m3 : mat r c),  m1 == m2 -> m2 == m3 -> m1 == m3.
  Proof.
    intros r c m1 m2 m3 H1 H2. unfold meq in *. intros i j Hi Hj.
    rewrite H1, <- H2; auto. easy.
  Qed.

  Lemma meq_equiv : forall r c : nat, Equivalence (@meq r c).
  Proof.
    constructor; intro; intros.
    apply meq_refl.
    apply meq_sym; auto.
    apply meq_trans with y; auto.
  Qed.

  Global Existing Instance meq_equiv.
  
  (** Meq is decidable *)
  Lemma meq_dec {Dec_Aeq : Decidable Aeq} : forall {r c}, Decidable (@meq r c).
  Proof.
    intros. constructor. intros. apply seq2eq_dec.
  Qed.
  
End meq.

(* ==================================== *)
(** ** Get element of a matrix *)
Section mnth.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  
  Definition mnth {r c} (m : mat r c) (ri ci : nat) : A := matf m ri ci.
  Notation "m ! i ! j " := (mnth m i j) : mat_scope.
  
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> 
        (forall ri ci, ri < r -> ci < c -> (m1!ri!ci == m2!ri!ci)%A).
  Proof.
    intros. split; intros; auto.
  Qed.
  
End mnth.

Global Hint Unfold mnth : core.
Notation "m ! i ! j " := (mnth m i j) : mat_scope.


(* ==================================== *)
(** ** Get row of a matrix *)
Section mrow.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.

  (** Get a row which row index is ri *)
  Definition mrow {r c : nat} (ri : nat) (m : mat r c) : list A :=
    map (fun i => m!ri!i) (seq 0 c).

  Lemma mrow_length : forall {r c} ri (m : mat r c), length (mrow ri m) = c.
  Proof.
    intros. unfold mrow. rewrite map_length. apply seq_length.
  Qed.

  (** (mrow m i)[j] = m[i][j] *)
  Lemma nth_mrow : forall {r c} ri ci (m : mat r c) a,
      ri < r -> ci < c -> (nth ci (mrow ri m) a == m ! ri ! ci)%A.
  Proof.
    intros. unfold mrow.
    rewrite nth_map_seq; auto.
    rewrite Nat.add_0_r. easy.
  Qed.
  
End mrow.


(* ==================================== *)
(** Convert between list list and mat *)
Section l2m_m2l.

  Context `{Equiv_Aeq : Equivalence A Aeq} {A0 : A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  
  (** list list to mat.
      Note: we need manually specify the dimension of the matrix. *)
  Definition l2m {r c} (dl : list (list A)) : mat r c :=
    mk_mat (fun ri ci =>
              if (Nat.ltb ri r) && (Nat.ltb ci c) then
                nth ci (nth ri dl []) A0
              else A0).
  
  (** mat to list list *)
  Definition m2l {r c} (m : mat r c) : list (list A) :=
    map (fun i => (map (fun j => m!i!j) (seq 0 c))) (seq 0 r).

  Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
  Proof.
    intros. unfold m2l. rewrite map_length, seq_length. auto.
  Qed.
  
  Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
  Proof.
    intros. unfold width,m2l.
    apply Forall_map.
    apply Forall_nth. intros. rewrite map_length, seq_length; auto.
  Qed.

  Lemma l2m_m2l_id : forall {r c} (m : mat r c), (@l2m r c (m2l m)) == m.
  Proof.
    intros. destruct m as [m].
    unfold l2m,m2l. simpl. intros i j Hi Hj. simpl.
    assert (r >? i). { apply Nat.ltb_lt; auto. }
    assert (c >? j). { apply Nat.ltb_lt; auto. }
    rewrite H,H0; simpl.
    rewrite ?nth_map_seq; auto. rewrite ?Nat.add_0_r. easy.
  Qed.

  Lemma m2l_l2m_id : forall {r c} (dl : list (list A)),
      (length dl = r) -> (width dl c) -> (m2l (@l2m r c dl) == dl)%dlist.
  Proof.
    intros. unfold l2m,m2l. simpl.
    rewrite (dlist_eq_iff_nth_nth r c (A0:=A0)); auto.
    - intros. rewrite ?nth_map_seq; auto.
      rewrite ?Nat.add_0_r. apply Nat.ltb_lt in H1,H2. rewrite H1,H2; simpl. easy.
    - rewrite map_length, seq_length; auto.
    - apply width_map. intros. rewrite map_length, seq_length; auto.
  Qed.

  Lemma l2m_inj : forall {r c} (d1 d2 : list (list A)),
      length d1 = r -> width d1 c -> length d2 = r -> width d2 c ->
      ~(d1 == d2)%dlist -> ~(@l2m r c d1 == l2m d2).
  Proof.
    intros.
    unfold l2m. intro. unfold meq in *. simpl in *. destruct H3.
    rewrite (dlist_eq_iff_nth_nth r c (A0:=A0)); auto.
    intros. specialize (H4 ri ci H3 H5).
    apply Nat.ltb_lt in H3,H5. rewrite H3,H5 in H4. simpl in H4. auto.
  Qed.
  
  Lemma l2m_surj : forall {r c} (m : mat r c), (exists d, l2m d == m).
  Proof.
    intros. exists (@m2l r c m). apply l2m_m2l_id.
  Qed.
  
  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), ~(m1 == m2) -> ~(m2l m1 == m2l m2)%dlist.
  Proof.
    intros. destruct m1 as [m1], m2 as [m2]. unfold meq in *; simpl in *.
    unfold m2l. simpl. intro.
    destruct H. intros.
    rewrite (dlist_eq_iff_nth_nth r c (A0:=A0)) in H0.
    - specialize (H0 i j H H1).
      rewrite ?nth_map_seq in H0; auto. rewrite ?Nat.add_0_r in H0. auto.
    - rewrite map_length, seq_length; auto.
    - rewrite map_length, seq_length; auto.
    - apply width_map. intros. rewrite map_length, seq_length; auto.
    - apply width_map. intros. rewrite map_length, seq_length; auto.
  Qed.
  
  Lemma m2l_surj : forall {r c} (d : list (list A)),
      length d = r -> width d c -> (exists m, (@m2l r c m == d)%dlist).
  Proof.
    intros. exists (@l2m r c d). apply m2l_l2m_id; auto.
  Qed.

End l2m_m2l.

(* Definition m := @l2m _ 0 2 2 [[1;2;3;4];[10;11;12;13]]. *)
(* Compute m2l m. *)

(* Global Hint Resolve m2l_length : mat. *)
(* Global Hint Resolve m2l_width : mat. *)


(* ==================================== *)
(** ** Get column *)
Section mcol.

  Context {A : Type}.
  
  (* Aux function, r_init is the offset of row index *)
  Fixpoint mcolAux (r c : nat) (ci : nat) (r_init : nat) (m : mat r c) : list A :=
    match r with
    | O => nil
    | S r' => m ! r_init ! ci :: (mcolAux r' c ci (S r_init) (mk_mat (matf m)))
    end.
  
  Definition mcol {r c : nat} (ci : nat) (m : mat r c) := mcolAux r c ci 0 m.
  
End mcol.


(* ==================================== *)
(** ** Right shift columns *)
Section mshift.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0 A1 : A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  Context {A1_neq_A0 : ~(A1 == A0)%A}.
  
  (** Right shift columns *)
  Definition mshiftc {r c} (m : @mat A r c) (k : nat) : mat r c :=
    mk_mat (fun i j => m ! i ! (j + k)).
  
  (** ∃ m m' k (m = m' /\ mshiftc m k <> mshiftc m' k *)
  Lemma mshiftc_neq : exists r c (m1 m2 : mat r c) (k : nat),
      m1 == m2 /\ ~(mshiftc m1 k == mshiftc m2 k). 
  Proof.
    set (m1 := @mk_mat _ 2 2 (fun (i j : nat) => if (j <? 2)%nat then A1 else A0)).
    set (m2 := @mk_mat _ 2 2 (fun (i j : nat) => if (j <? 3)%nat then A1 else A0)).
    exists 2, 2, m1, m2, (1%nat). split.
    - apply meq_iff_mnth. unfold m1, m2. intros i j Hi Hj. unfold mnth.
      destruct j as [|[|]]; destruct i as [|[|]]; simpl; try easy; lia.
    - intros F.
      assert (1 < 2)%nat by lia.
      apply meq_iff_mnth in F. unfold meq in F.
      specialize (F _ _ H H).
      unfold m1, m2, mshiftc in F.
      simpl in F.
      apply A1_neq_A0. easy.
  Qed.
  
End mshift.


(* ==================================== *)
(** ** Matrix Automation *)

(** Useful tactic for solving A = B for concrete A, B *)

Ltac solve_end :=
  match goal with
  | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.

(** Convert mat to function *)
Ltac mat_to_fun :=
  match goal with
  | m : mat ?r ?c |- _ => destruct m as [m]
  end.

(** Some modification of this tactic:
1. use a alternate lemma NatExt.lt_S_n instead of lt_S_n,
   because Coq report it is deprecated since 8.16
2. disable "clear Hi, clear Hj", because these two conditions are needed in 
   some cases. 
3. call "mat_to_fun" first, to unpack the mat structure to a function
 *)

Ltac by_cell :=
  intros;
  (* try apply meq_imply_eq; *)
  let i := fresh "i" in
  let j := fresh "j" in
  let Hi := fresh "Hi" in
  let Hj := fresh "Hj" in
  intros i j Hi Hj; try solve_end;
  repeat mat_to_fun;
  repeat (destruct i as [|i]; simpl;
          [|apply NatExt.lt_S_n in Hi]; try solve_end);
  (* clear Hi; *)
  repeat (destruct j as [|j]; simpl;
          [|apply NatExt.lt_S_n in Hj]; try solve_end)
(* clear Hj *)
.

Global Ltac lma :=
  by_cell;
  try (
      try (compute; ring);
      try (compute; field);
      try (compute; easy));
  simpl.


(* ==================================== *)
(** ** Build concrete matrix *)
Section SpecifyDims.

  Context {A : Type} {A0 : A}.

  Notation mat := (@mat A).
  Notation l2m := (l2m (A0:=A0)).
  
  Definition mk_mat_0_c c : mat 0 c := l2m [].

  Definition mk_mat_1_1 (a11 : A) : mat 1 1 := l2m [[a11]].
  Definition mk_mat_1_2 (a11 a12 : A) : mat 1 2 := l2m [[a11;a12]].
  Definition mk_mat_1_3 (a11 a12 a13 : A) : mat 1 3 := l2m [[a11;a12;a13]].
  Definition mk_mat_1_4 (a11 a12 a13 a14 : A) : mat 1 4 := l2m [[a11;a12;a13;a14]].
  Definition mk_mat_1_c c (l : list A) : mat 1 c := l2m [l].
  
  Definition mk_mat_r_0 r : mat r 0 := l2m [].

  Definition mk_mat_2_1 (a11 a21 : A) : mat 2 1 := l2m [[a11];[a21]].
  Definition mk_mat_2_2 (a11 a12 a21 a22 : A) : mat 2 2 := l2m [[a11;a12];[a21;a22]].
  
  Definition mk_mat_3_1 (a11 a21 a31 : A) : mat 3 1 := l2m [[a11];[a21];[a31]].
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A) : mat 3 3 :=
    l2m [[a11;a12;a13]; [a21;a22;a23]; [a31;a32;a33]].

  Definition mk_mat_4_1 (a11 a21 a31 a41 : A) : mat 4 1 :=
    l2m [[a11];[a21];[a31];[a41]].
  Definition mk_mat_4_4 (a11 a12 a13 a14 a21 a22 a23 a24
                           a31 a32 a33 a34 a41 a42 a43 a44 : A) : mat 4 4 :=
    l2m [[a11;a12;a13;a14]; [a21;a22;a23;a24];[a31;a32;a33;a34]; [a41;a42;a43;a44]].
  
  Definition mk_mat_r_1 r (l : list A) : mat r 1 :=
    mk_mat (fun ri ci : nat => if (ci =? 0)%nat then (nth ri l A0) else A0).
  
End SpecifyDims.


(* ==================================== *)
(** ** Mapping of matrix *)
Section Map.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  
  Definition mmap {r c} (f : A -> A) (m : mat r c) : mat r c :=
    mk_mat (fun i j => f (m ! i ! j)).
  
  Definition mmap2 {r c} (f : A -> A -> A) (m1 m2 : mat r c) : mat r c :=
    mk_mat (fun i j => f (m1 ! i ! j) (m2 ! i ! j)).
  
  Lemma mmap2_comm : forall {r c} (f : A -> A -> A)
                            (f_comm : forall a b : A, (f a b == f b a)%A)
                            (m1 m2 : mat r c), 
      mmap2 f m1 m2 == mmap2 f m2 m1.
  Proof.
    intros r c f H1. intros m1 m2.
    unfold mmap2, meq. intros i j Hi Hj. apply H1.
  Qed.
  
  Lemma mmap2_assoc : forall {r c} (f : A -> A -> A)
                             (f_assoc : forall a b c, (f (f a b) c == f a (f b c))%A)
                             (m1 m2 m3 : mat r c), 
      mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
  Proof.
    intros r c f H1. intros m1 m2 m3.
    unfold mmap2, meq. intros i j Hi Hj. apply H1.
  Qed.
  
End Map.


(* ==================================== *)
(** ** Matrix transposition *)
Section mtrans.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0 A1 : A}.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  
  Definition mtrans {r c} (m : @mat A r c): mat c r :=
    mk_mat (fun i j => m ! j ! i).
  Notation "m \T" := (mtrans m) : mat_scope.
  
  (** Transpose twice keep unchanged. *)
  Lemma mtrans_trans : forall {r c} (m : @mat A r c), m \T \T == m.
  Proof. lma. Qed.

End mtrans.


(* ==================================== *)
(** ** Zero matrirx and identity matrix *)
Section mat0_mat1.
  Context `{Equiv_Aeq : Equivalence A Aeq} (A0 A1 : A).
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  Notation "m \T" := (mtrans m) : mat_scope.

  (** *** Zero matrix *)
  Definition mat0 (r c : nat) : mat r c :=
    mk_mat (fun _ _ => A0).

  (** mat0\T = mat0 *)
  Lemma mtrans_mat0_eq_mat0 : forall {r c : nat}, (mat0 r c)\T == mat0 c r.
  Proof. lma. Qed.

  
  (** *** Identity matrix *)
  Definition mat1 (n : nat) : mat n n :=
    mk_mat (fun i j => if (i =? j)%nat then A1 else A0).
  
  (** mat1\T = mat1 *)
  Lemma mtrans_mat1_eq_mat1 : forall {n : nat}, (mat1 n)\T == (mat1 n).
  Proof.
    lma. unfold mtrans,mat1. simpl. replace (j =? i) with (i =? j); try easy.
    apply Nat.eqb_sym.
  Qed.

End mat0_mat1.


(* ==================================== *)
(** ** Matrix algebra *)
(** Matrix addition, opposition, subtraction, scalar multiplication, multiplication. *)
Section malg.
  Context `{AG : AGroup}.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := (fun a b => a + (-b)) : A_scope.
  Infix "==" := Aeq : A_scope.

  Infix "+" := (ladd (Aadd:=Aadd)) : list_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.

  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.

  (** *** Matrix addition *)
  
  Definition madd {r c} (m1 m2 : mat r c) : mat r c :=
    mk_mat (fun i j => m1!i!j + m2!i!j).
  Infix "+" := madd : mat_scope.

  (** m1 + m2 = m2 + m1 *)
  Lemma madd_comm : forall {r c} (m1 m2 : mat r c), m1 + m2 == (m2 + m1).
  Proof.
    lma. amonoid_simpl.
  Qed.

  (** (m1 + m2) + m3 = m1 + (m2 + m3) *)
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) + m3 == m1 + (m2 + m3).
  Proof.
    lma. monoid_simpl.
  Qed.

  (** mat0 + m = m *)
  Lemma madd_0_l : forall {r c} (m : mat r c), mat0 A0 r c + m == m. 
  Proof.
    lma. monoid_simpl.
  Qed.

  (** m + mat0 = m *)
  Lemma madd_0_r : forall {r c} (m : mat r c), m + mat0 A0 r c == m. 
  Proof.
    lma. monoid_simpl.
  Qed.
  
  (** Get element of addition with two matrics equal to additon of 
      corresponded elements. *)
  Lemma madd_nth : forall {r c} (m1 m2 : mat r c) ri ci,
      ((m1 + m2)%mat ! ri ! ci == (m1!ri!ci) + (m2!ri!ci))%A.
  Proof.
    intros.
    unfold madd, mnth. easy.
  Qed.

  (** (m1 + m2)[ri] = m1[ri] + m2[ri] *)
  Lemma mrow_madd : forall {r c} ri (m1 m2 : mat r c),
      (ri < r) -> (mrow ri (m1 + m2)%mat == (mrow ri m1) + (mrow ri m2))%list.
  Proof.
    intros. unfold mrow.
    rewrite (list_eq_iff_nth A0 c).
    - intros.
      replace (
          (map (fun i0 : nat => m1 ! ri ! i0) (seq 0 c) +
             map (fun i0 : nat => m2 ! ri ! i0) (seq 0 c)))%list
        with ((map (fun i0 : nat => m1 ! ri ! i0 + m2 ! ri ! i0) (seq 0 c))%A).
      + rewrite ?nth_map_seq; auto. rewrite Nat.add_0_r. easy.
      + admit.
    - rewrite map_length. apply seq_length.
  Admitted.

  
  (** *** Matrix opposition *)
  
  Definition mopp {r c} (m : mat r c) : mat r c :=
    mk_mat (fun i j => - (m!i!j)).
  Notation "- a" := (mopp a) : mat_scope.

  (** - (- m) = m *)
  Lemma mopp_opp : forall {r c} (m : mat r c), - (- m) == m.
  Proof.
    lma. unfold mopp. apply group_inv_inv.
  Qed.
  
  
  (** *** Matrix subtraction *)
  
  Definition msub {r c} (m1 m2 : mat r c) : mat r c :=
    mk_mat (fun i j => m1!i!j - m2!i!j).
  Infix "-" := msub : mat_scope.

  (** m1 - m2 = -(m2 - m1) *)
  Lemma msub_comm : forall {r c} (m1 m2 : mat r c), m1 - m2 == - (m2 - m1).
  Proof.
    lma. rewrite group_inv_distr,group_inv_inv. f_equiv.
  Qed.

  (** (m1 - m2) - m3 = m1 - (m2 + m3) *)
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 - m2) - m3 == m1 - (m2 + m3).
  Proof.
    lma. rewrite group_inv_distr.
    monoid_simpl. f_equiv. amonoid_simpl.
  Qed.

  (** mat0 - m = - m *)
  Lemma msub_0_l : forall {r c} (m : mat r c), (mat0 A0 r c) - m == - m.
  Proof.
    lma. monoid_simpl.
  Qed.

  (** m - mat0 = m *)
  Lemma msub_0_r : forall {r c} (m : mat r c), m - (mat0 A0 r c) == m.
  Proof.
    lma. rewrite group_opp_zero_eq_zero. monoid_simpl.
  Qed.

  (** m + (-m) = mat0 *)
  Lemma madd_opp : forall r c (m : mat r c), m + (-m) == mat0 A0 r c.
  Proof.
    lma. group_simpl.
  Qed.

  (** m - m = mat0 *)
  Lemma msub_self : forall {r c} (m : mat r c), m - m == (mat0 A0 r c).
  Proof.
    lma. group_simpl.
  Qed.


  (** *** Below, we need a ring structure *)
  Context `{R : Ring A Aadd A0 Aopp Amul A1 Aeq}.
  Infix "*" := Amul : A_scope.
  
  Add Ring ring_inst : make_ring_theory.
  
  
  (** *** Scalar multiplication of matrix *)

  (** Left scalar multiplication of matrix *)
  Definition mcmul {r c} (a : A) (m : mat r c) : mat r c :=
    mk_mat (fun i j => (a * m!i!j)).
  Infix "c*" := mcmul : mat_scope.
  
  (** Right scalar multiplication of matrix *)
  Definition mmulc {r c} (m : mat r c) (a : A) : mat r c :=
    mk_mat (fun i j => (m!i!j * a)).
  Infix "*c" := mmulc : mat_scope.

  (** mcmul is a proper morphism *)
  Lemma mcmul_aeq_mor : forall r c: nat,
      Proper (Aeq ==>
                meq (Aeq:=Aeq)(r:=r)(c:=c) ==>
                meq (Aeq:=Aeq)(r:=r)(c:=c)) mcmul.
  Proof.
    lma. lma.
    rewrite meq_iff_mnth in H. simpl in H.
    specialize (H i0 j0 Hi0 Hj0). rewrite Hi,H. easy.
  Qed.

  Global Existing Instance mcmul_aeq_mor.

  (** m *c a = a c* m *)
  Lemma mmulc_eq_mcmul : forall {r c} (a : A) (m : mat r c), m *c a == a c* m.
  Proof. lma. Qed.

  (** 0 c* m = mat0 *)
  Lemma mcmul_0_l : forall {r c} (m : mat r c), A0 c* m == mat0 A0 r c.
  Proof. lma. Qed.

  (** a c* mat0 = mat0 *)
  Lemma mcmul_0_r : forall {r c} a, a c* mat0 A0 r c == mat0 A0 r c.
  Proof. lma. Qed.

  (** 1 c* m = m *)
  Lemma mcmul_1_l : forall {r c} (m : mat r c), A1 c* m == m.
  Proof. lma. Qed.

  (** a c* mat1 equal to a diagonal matrix which main diagonal elements all are a *)
  Lemma mcmul_1_r : forall {n} a,
      a c* mat1 A0 A1 n == mk_mat (fun ri ci => if (ri =? ci)%nat then a else A0).
  Proof.
    lma. unfold mcmul,mat1. destruct (i =? j); ring.
  Qed.

  (** a c* (b c* m) = (a * b) c* m *)
  Lemma mcmul_assoc : forall {r c} (a b : A) (m : mat r c), a c* (b c* m) == (a * b) c* m.
  Proof. lma. Qed.

  (** a c* (b c* m) = b c* (a c* m) *)
  Lemma mcmul_perm : forall {r c} (a b : A) (m : mat r c), a c* (b c* m) == b c* (a c* m).
  Proof. lma. Qed.

  (** a c* (m1 + m2) = (a c* m1) + (a c* m2) *)
  Lemma mcmul_add_distr_l : forall {r c} (a : A) (m1 m2 : mat r c), 
      a c* (m1 + m2) == (a c* m1) + (a c* m2).
  Proof. lma. Qed.
  
  (** (a + b) c* m = (a c* m) + (b c* m) *)
  Lemma mcmul_add_distr_r : forall {r c} (a b : A) (m : mat r c), 
      (a + b)%A c* m == (a c* m) + (b c* m).
  Proof. lma. Qed.


  (** *** Matrix multiplication *)
  Definition mmul {r c t : nat} (m1 : mat r c) (m2 : mat c t) : mat r t :=
    mk_mat
      (fun x z => seqsum (Aadd:=Aadd)(A0:=A0) (fun y => m1!x!y * m2!y!z) c).
  Infix "*" := mmul : mat_scope.

  (** (m1 * m2) * m3 = m1 * (m2 * m3) *)
  Lemma mmul_assoc : forall {r c s t : nat} (m1 : mat r c) (m2 : mat c s) (m3: mat s t), 
      (m1 * m2) * m3 == m1 * (m2 * m3).
  Proof.
    lma.
    induction c; simpl.
    - apply seqsum_seq0. intros. ring.
    - rewrite <- IHc. rewrite seqsum_cmul_l. rewrite <- seqsum_add.
      apply seqsum_eq; intros. ring.
      apply agroupComm.
  Qed.

  (** m1 * (m2 + m3) = m1 * m2 + m1 * m3 *)
  Lemma mmul_add_distr_l : forall {r c s : nat} (m1 : mat r c) (m2 m3 : mat c s), 
      m1 * (m2 + m3) == m1 * m2 + m1 * m3.
  Proof.
    lma. unfold mmul,mnth,madd.
    rewrite <- seqsum_add. apply seqsum_eq; intros. ring.
    apply agroupComm.
  Qed.
  
  (** (m1 + m2) * m3 = m1 * m3 + m2 * m3 *)
  Lemma mmul_add_distr_r : forall {r c s : nat} (m1 m2 : mat r c) (m3 : mat c s),
      (m1 + m2) * m3 == m1 * m3 + m2 * m3.
  Proof.
    lma. unfold mmul,mnth,madd.
    rewrite <- seqsum_add. apply seqsum_eq; intros. ring.
    apply agroupComm.
  Qed.

  (** mat0 * m = mat0 *)
  Lemma mmul_0_l : forall {r c s} (m : mat c s), (mat0 A0 r c) * m == mat0 A0 r s.
  Proof.
    lma. unfold mmul,mat0. apply seqsum_seq0. intros. ring.
  Qed.

  (** m * mat0 = mat0 *)
  Lemma mmul_0_r : forall {r c s} (m : mat r c), m * (mat0 A0 c s) == mat0 A0 r s.
  Proof.
    lma. unfold mmul,mat0. apply seqsum_seq0. intros. ring.
  Qed.

  (** mat1 * m = m *)
  Lemma mmul_1_l : forall {r c : nat} (m : mat r c), mat1 A0 A1 r * m == m.
  Proof.
    lma.
    apply (seqsum_unique _ _ _ i); auto.
    - rewrite Nat.eqb_refl. ring.
    - intros. bdestruct (i =? j0). lia. ring.
  Qed.

  (** m * mat1 = m *)
  Lemma mmul_1_r : forall {r c : nat} (m : mat r c), m * mat1 A0 A1 c == m.
  Proof.
    lma. unfold mmul,mat1.
    apply (seqsum_unique _ _ _ j); auto.
    - rewrite Nat.eqb_refl. ring.
    - intros. bdestruct (j0 =? j). lia. ring.
  Qed.
  
  (* a c* (m1 * m2) = (a c* m1) * m2. *)
  Lemma mcmul_mul_assoc : forall {r c s} (a : A) (m1 : mat r c) (m2 : mat c s), 
      a c* (m1 * m2) == (a c* m1) * m2.
  Proof.
    lma. unfold mcmul,mmul.
    rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
  Qed.
  
  (** m1 * (a c* m2) = a c* (m1 * m2). *)
  Lemma mcmul_mul_perm : forall {r c s} (a : A) (m1 : mat r c) (m2 : mat c s), 
      a c* (m1 * m2) == m1 * (a c* m2).
  Proof.
    lma. unfold mcmul,mmul.
    rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
  Qed.
  
End malg.

Global Hint Unfold
  madd mopp msub mcmul mmulc mmul
  : mat.

(** Notes, these notations need to be re-declare with suitable arguments,
    Thus, we shouldn't declare them here. *)
(* Infix "+" := madd : mat_scope. *)
(* Notation "- a" := (mopp a) : mat_scope. *)
(* Infix "-" := msub : mat_scope. *)
(* Infix "*" := mmul : mat_scope. *)
(* Infix "c*" := mcmul : mat_scope. *)
(* Infix "*c" := mmulc : mat_scope. *)


(* ==================================== *)
(** ** Other OPs and PROPs *)

(** Convert between tuples and matrix *)
Section t2m_m2t.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0:A}.
  
  (** Tuples 3x3 -> mat_3x3 *)
  Definition t2m_3x3 (t : @T_3x3 A) : @mat A 3 3.
  Proof.
    destruct t as ((t1,t2),t3).
    destruct t1 as ((a11,a12),a13).
    destruct t2 as ((a21,a22),a23).
    destruct t3 as ((a31,a32),a33).
    exact (mk_mat_3_3 (A0:=A0) a11 a12 a13 a21 a22 a23 a31 a32 a33).
  Defined.

  (** mat_3x3 -> tuple 3x3. That is: ((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) *)
  Definition m2t_3x3 (m : mat 3 3) : @T_3x3 A :=
    ((m!0!0, m!0!1, m!0!2),
      (m!1!0, m!1!1, m!1!2),
      (m!2!0, m!2!1, m!2!2)).

  (** m[0,0]: mat_1x1 -> A *)
  Definition scalar_of_mat (m : @mat A 1 1) := m!0!0.

End t2m_m2t.


(* ==================================== *)
(** ** trace *)
Section trace.

  Context {A : Type} {Aadd: A -> A -> A} {A0 : A}.

  (** Trace *)
  Definition trace {n : nat} (m : smat n) := 
    seqsum (Aadd:=Aadd)(A0:=A0) (fun i => m!i!i) n.

End trace.


(* ==================================== *)
(** ** Matrix Inversion with the help of determinant and adjoint matrix. *)
Section matrix_inversion.

  (** *** We need a ring structure *)
  Context `{R:Ring}.
  Add Ring ring_thy_inst : make_ring_theory.

  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Infix "==" := Aeq : A_scope.

  Infix "*" := (@mmul A Aadd A0 Amul _ _ _) : mat_scope.
  Infix "c*" := (@mcmul A Amul _ _) : mat_scope.
  Infix "==" := (@meq _ Aeq _ _) : mat_scope.
  Notation mat1 := (mat1 A0 A1).
  Notation l2m := (@l2m A A0 _ _).

  
  (** *** Definition of determinant *)
  Section det_def.
    
    (** Get the sub square matrix which remove r-th row and c-th column
        from a square matrix. *)
    Definition submat {n} (m : @smat A (S n)) (r c : nat) : smat n :=
      mk_mat
        (fun i j =>
           let i' := (if ltb i r then i else S i) in
           let j' := (if ltb j c then j else S j) in
           m!i'!j').

    (** Determinant of a square matrix (original definition) *)
    (* Variable a b c : A. *)
    (* Compute perm 0 (seq 0 3). *)
    (* Let dl := perm 0 (seq 0 3). *)
    (* Let l := [1;2;3]. *)
    (* Compute nth 1 l 0. *)
    (* Compute map (fun i => (i, nth i l 0)) (seq 0 3). *)
    (* Compute map (fun l => map (fun i => (i, nth i l 0)) (seq 0 3)) dl. *)
    (* Let dl1 := map (fun l => map (fun i => (i, nth i l 0)) (seq 0 3)) dl. *)
    (* Variable a00 a01 a02 a10 a11 a12 a20 a21 a22 : A. *)
    (* Definition m : smat 3 := mk_mat_3_3 a00 a01 a02 a10 a11 a12 a20 a21 a22. *)
    (* Compute map (fun l => map (fun (ij:nat * nat) => let (i,j) := ij in m!i!j) l) dl1. *)

    (* (** all items in a determinant *) *)
    (* Let dl2 := map (fun l => map (fun (ij:nat * nat) => let (i,j) := ij in m!i!j) l) dl1. *)
    (* Compute dl2. *)

    (* Definition n := 3. *)
    (* Compute perm 0 (seq 0 n). (* *)
     (*  = [[0; 1; 2]; [0; 2; 1]; [1; 0; 2]; [1; 2; 0]; [2; 0; 1]; [2; 1; 0]] *)
     (*  : list (list nat) *) *)

    (* Definition item_of_det {n : nat} (m : smat n) (l : list nat) : A := *)
    (*   fold_left Amul (map (fun i => m!i!(nth i l 0)) l) A1. *)

    (* (** Definition of determinant *) *)
    (* Definition det_def {n : nat} (m : smat n) : A := *)
    (*   fold_left Aadd (map (fun l => item_of_det m l) (perm 0 (seq 0 n))) A0. *)

    (* Compute det_orig m. *)
    
    (* Compute fold_left Amul [a00;a01;a02]. *)
    (* Compute fold_left Aadd. *)

    (* Check perm. ? *)
    (* Fixpoint det_orig {n} : smat n -> A := *)
    (*   match n with *)
    (*   | 0 => fun _ => A1 *)
    (*   | S n' => *)
    (*       fun m => *)
    
    (** Determinant of a square matrix.
        The idea: by expanding the first row *)
    Fixpoint det {n} : smat n -> A :=
      match n with
      | 0 => fun _ => A1
      | S n' =>
          fun m =>
            fold_left Aadd
              (map (fun i =>
                      let a := if Nat.even i then (m!0!i)%nat else (-(m!0!i)%nat)%A in
                      let d := det (submat m 0 i) in
                      (a * d)%A) (seq 0 n)) A0
      end.

  End det_def.

  (** Prove a proposition such as:
      "~(det m == 0) -> ~(xxx = 0)"
      or
      "~(xxx = 0) -> ~(det m == 0)"
   *)
  Ltac det_neq0_imply_neq0 :=
    match goal with
    | H : ~(det ?m == A0)%A |- ~(_ == A0)%A =>
        let H1 := fresh "H1" in
        intro H1; destruct H; cbv; ring_simplify; ring_simplify in H1; auto
    | H : ~(_ == A0)%A |- ~(det ?m == A0)%A =>
        let H1 := fresh "H1" in
        intro H1; cbv in H1; destruct H; ring_simplify; ring_simplify in H1; auto
    end.

  (** *** Properties of determinant *)
  Section det_props.

    (** Determinant of a matrix of dimension-1 *)
    Definition det_1_1 (m : @smat A 1) := m!0!0.

    (** det_1_1 m = det m *)
    Lemma det_1_1_eq_det : forall m, (det_1_1 m == det m)%A.
    Proof.
      intros. cbv. ring.
    Qed.
    
    (** det m <> 0 <-> det_exp <> 0 *)
    Lemma det_1_1_neq0_iff : forall (m : smat 1),
        ~ (det m == A0)%A <->  ~ (m!0!0 == A0)%A.
    Proof.
      intros. split; intros; det_neq0_imply_neq0.
    Qed.

    (** Determinant of a matrix of dimension-2 *)
    Definition det_2_2 (m : smat 2) := (m!0!0 * m!1!1 - m!0!1 * m!1!0)%A.

    (** det_2_2 m = det m *)
    Lemma det_2_2_eq_det : forall m, (det_2_2 m == det m)%A.
    Proof.
      intros. cbv. ring.
    Qed.

    (** det m <> 0 <-> det_exp <> 0 *)
    Lemma det_2_2_neq0_iff : forall (m : smat 2),
        ~ (det m == A0)%A <->  ~ (m!0!0 * m!1!1 - m!0!1 * m!1!0 == A0)%A.
    Proof.
      intros. split; intros; det_neq0_imply_neq0.
    Qed.

    (** Determinant of a matrix of dimension-3 *)
    Definition det_3_3 (m : smat 3) :=
      (m!0!0 * m!1!1 * m!2!2 - m!0!0 * m!1!2 * m!2!1 - 
         m!0!1 * m!1!0 * m!2!2 + m!0!1 * m!1!2 * m!2!0 + 
         m!0!2 * m!1!0 * m!2!1 - m!0!2 * m!1!1 * m!2!0)%A.

    (** det_3_3 m = det m *)
    Lemma det_3_3_eq_det : forall m, (det_3_3 m == det m)%A.
    Proof.
      intros. cbv. ring.
    Qed.
    
    (** det m <> 0 <-> det_exp <> 0 *)
    Lemma det_3_3_neq0_iff : forall (m : smat 3),
        ~ (det m == A0)%A <->
          ~(m!0!0 * m!1!1 * m!2!2 - m!0!0 * m!1!2 * m!2!1 - 
              m!0!1 * m!1!0 * m!2!2 + m!0!1 * m!1!2 * m!2!0 + 
              m!0!2 * m!1!0 * m!2!1 - m!0!2 * m!1!1 * m!2!0 == A0)%A.
    Proof.
      intros. split; intros; det_neq0_imply_neq0.
    Qed.

  End det_props.


  (** *** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  (** That is: adj(A)[i,j] = algebraic remainder of A[j,i]. *)
  Section adj.

    Definition madj {n} : smat n -> smat n := 
      match n with
      | O => fun m => m 
      | S n' =>
          fun m =>
            mk_mat (fun i j =>
                      let s := if Nat.even (i + j) then A1 else (-A1)%A in
                      let d := det (submat m j i) in 
                      (s * d)%A)
      end.

  End adj.

  (** *** We need a field structure *)
  Context `{F:@Field A Aadd A0 Aopp Amul A1 Ainv Aeq}.
  Add Field field_thy_inst : make_field_theory.

  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv := (fun x y => Amul x (Ainv y)).
  Infix "/" := Adiv : A_scope.


  (** *** Cramer rule *)
  Section cramer_rule.
    
    (** Exchange one column of a square matrix *)
    Definition mchgcol {n} (m : @smat A n) (k : nat) (v : mat n 1) : smat n :=
      mk_mat (fun i j => if (Nat.eqb j k) then (v!i!0)%nat else m!i!j).
    
    (** Cramer rule, which can slving the equation with form of A*x=b.
      Note, the result is valid only when D is not zero *)
    Definition cramerRule {n} (A : smat n) (b : mat n 1) : mat n 1 :=
      let D := det A in
      mk_mat (fun i j => let Di := det (mchgcol A i b) in (Di / D)).
    
  End cramer_rule.

  
  (** *** Matrix Inversion *)
  Section inv.

    (** Prove a proposition such as:
      "~(det m == 0) -> ~(xxx = 0)"
      or
      "~(xxx = 0) -> ~(det m == 0)"
     *)
    Definition minv {n} (m : smat n) := (A1 / det m) c* (madj m).

    Lemma minv_correct_r : forall n (m : smat n), m * (minv m) == mat1 n.
    Proof.
      induction n; intros.
      - lma.
        (* - unfold minv in *. *)
    Abort.

    
    (* ======================================================================= *)
    (** ** Inversion matrix of dimension-1 *)
    Definition inv_1_1 (m : smat 1) : smat 1 := l2m [[A1/(m!0!0)]].


    (** det m <> 0 -> inv_1_1 m = inv m *)
    Lemma inv_1_1_eq_inv : forall m, ~(det m == A0)%A -> inv_1_1 m == minv m.
    Proof.
      lma. det_neq0_imply_neq0.
    Qed.

    (** inv_1_1 m * m = mat1 *)
    Lemma inv_1_1_correct_l : forall (m : smat 1),
        ~(det m == A0)%A -> (inv_1_1 m) * m == mat1 1.
    Proof.
      lma. det_neq0_imply_neq0.
    Qed.

    (** m * inv_1_1 m = mat1 *)
    Lemma inv_1_1_correct_r : forall (m : smat 1),
        ~(det m == A0)%A -> m * (inv_1_1 m) == mat1 1.
    Proof.
      lma. det_neq0_imply_neq0.
    Qed.

    (* ======================================================================= *)
    (** ** Inversion matrix of dimension-2 *)
    Definition inv_2_2 (m : smat 2) : smat 2 :=
      let a00 := m!0!0 in
      let a01 := m!0!1 in
      let a10 := m!1!0 in
      let a11 := m!1!1 in
      let d := det_2_2 m in
      (l2m [[a11/d; -a01/d]; [-a10/d; a00/d]])%A.

    (** det m <> 0 -> inv_2_2 m = inv m *)
    Lemma inv_2_2_eq_inv : forall m, ~(det m == A0)%A -> inv_2_2 m == minv m.
    Proof.
      lma; det_neq0_imply_neq0.
    Qed.
    
    (** inv_2_2 m * m = mat1 *)
    Lemma inv_2_2_correct_l : forall (m : smat 2),
        ~(det m == A0)%A -> (inv_2_2 m) * m == mat1 2.
    Proof.
      lma; det_neq0_imply_neq0.
    Qed.
    
    (** m * inv_2_2 m = mat1 *)
    Lemma inv_2_2_correct_r : forall (m : smat 2),
        ~(det m == A0)%A -> m * (inv_2_2 m) == mat1 2.
    Proof.
      lma; det_neq0_imply_neq0.
    Qed.
    
    (* ======================================================================= *)
    (** ** Inversion matrix of dimension-3 *)
    (* Note, this formula could be provided from matlab, thus avoiding manual work *)
    Definition inv_3_3 (m : smat 3) : smat 3 :=
      let a00 := m!0!0 in
      let a01 := m!0!1 in
      let a02 := m!0!2 in
      let a10 := m!1!0 in
      let a11 := m!1!1 in
      let a12 := m!1!2 in
      let a20 := m!2!0 in
      let a21 := m!2!1 in
      let a22 := m!2!2 in
      let d := det_3_3 m in
      (l2m
         [[(a11*a22 - a12*a21)/d; -(a01*a22 - a02*a21)/d; (a01*a12 - a02*a11)/d];
          [-(a10*a22 - a12*a20)/d; (a00*a22 - a02*a20)/d; -(a00*a12 - a02*a10)/d];
          [(a10*a21 - a11*a20)/d; -(a00*a21 - a01*a20)/d; (a00*a11 - a01*a10)/d]])%A.
    
    (** det m <> 0 -> inv_3_3 m = inv m *)
    Lemma inv_3_3_eq_inv : forall m, ~(det m == A0)%A -> inv_3_3 m == minv m.
    Proof.
      lma; det_neq0_imply_neq0.
    Qed.
    
    (** inv_3_3 m * m = mat1 *)
    Lemma inv_3_3_correct_l : forall (m : smat 3),
        ~(det m == A0)%A -> (inv_3_3 m) * m == mat1 3.
    Proof.
      lma; det_neq0_imply_neq0.
    Qed.
    
    (** m * inv_3_3 m = mat1 *)
    Lemma inv_3_3_correct_r : forall (m : smat 3),
        ~(det m == A0)%A -> m * (inv_3_3 m) == mat1 3.
    Proof.
      lma; det_neq0_imply_neq0.
    Qed.
    
    (* ======================================================================= *)
    (** ** Direct compute inversion of a symbol matrix of 1/2/3rd order. *)
    Section FindFormula.
      Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.
      Let m1 := mk_mat_1_1 (A0:=A0) a11.
      Let m2 := mk_mat_2_2 (A0:=A0) a11 a12 a21 a22.
      Let m3 := mk_mat_3_3 (A0:=A0) a11 a12 a13 a21 a22 a23 a31 a32 a33.

      (* Compute (m2l (minv m1)). *)
      (* Compute (m2l (minv m2)). *)
      (* Compute (m2l (minv m3)). *)
      (* Although this is correct, but the expression is too long. *)
      (* We want to simplify it with RAST *)
      
    End FindFormula.

  End inv.

End matrix_inversion.

(* ==================================== *)
(** ** Gauss Elimination *)
Section gauss_elimination.

  Context `{F:Field}.

  Notation mat := (@mat A).

  (** *** 初等行变换 (brt: Basic Row Transform) *)
  
  (** 交换两行 *)
  Definition brt_swap {r c} (ri rj : nat) : mat r c :=
    mk_mat (fun i j =>
              if i =? ri
              then (if j =? rj then A1 else A0)
              else (if i =? rj
                    then (if j =? ri then A1 else A0)
                    else (if i =? j then A1 else A0))).

  (** 数乘某一行 *)
  Definition brt_cmul {r c} (ri : nat) (k : A) : mat r c :=
    mk_mat (fun i j =>
              if i =? ri
              then (if j =? ri then k else A0)
              else (if i =? j then A1 else A0)).

  (** 第i行的k倍加到第j行 *)
  Definition brt_add {r c} (ri rj : nat) (k : A) : mat r c :=
    mk_mat (fun i j =>
              if (i =? ri) && (j =? rj)
              then k
              else (if i =? j then A1 else A0)).

  (* Definition find_pivot *)
  (* Fixpoint  *)

End gauss_elimination.

Import QArith.
(* Compute m2l (@brt_swap Q 0 1 4 4 0 2). *)
(* Compute m2l (@brt_cmul Q 0 1 4 4 1 2). *)
(* Compute m2l (@brt_add  Q 0 1 4 4 0 2 5). *)



(** Test *)
Module Test.
  Import QArith Qcanon.
  Open Scope Q.
  Open Scope Qc_scope.

  Coercion Q2Qc : Q >-> Qc.

  Definition m1 := (mk_mat_3_3 (A0:=0) 1 2 3 4 5 6 7 8 9)%Qc.
  (* Compute trace (Aadd:=Qcplus)(A0:=0)(n:=3) m1. *)

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : Qc.
  Definition m2 := mk_mat_3_3 (A0:=0) a11 a12 a13 a21 a22 a23 a31 a32 a33.
  (* Compute mrow 1 m2. *)

End Test.


(*   
  (* ==================================== *)
  (** ** Matrix Simplification *)

  Ltac unify_matrix_dims tac := 
    try reflexivity; 
    repeat (apply f_equal_gen; try reflexivity; 
            try (is_nat_equality; tac)).

  Ltac restore_dims_rec A :=
     match A with
  (* special cases *)
    | ?X * I _          => let A' := restore_dims_rec A in 
                          match type of A' with 
                          | mat ?m' ?n' => 
                            constr:(@mmul m' n' n' A' (mat1 n'))
                          end
    | I _ * ?B          => let B' := restore_dims_rec B in 
                          match type of B' with 
                          | mat ?n' ?o' => 
                            constr:(@mmul n' n' o' (mat1 n')  B')
                          end
    | ?X * @mat0 ?n ?n  => let A' := restore_dims_rec A in 
                          match type of A' with 
                          | mat ?m' ?n' => 
                            constr:(@mmul m' n' n' A' (@mat0 n' n'))
                          end
    | @mat0 ?n ?n * ?B  => let B' := restore_dims_rec B in 
                          match type of B' with 
                          | mat ?n' ?o' => 
                            constr:(@mmul n' n' o' (@mat0 n' n') B')
                          end
    | ?X * @mat0 ?n ?o  => let A' := restore_dims_rec A in 
                          match type of A' with 
                          | mat ?m' ?n' => 
                            constr:(@mmul m' n' o A' (@mat0 n' o))
                          end
    | @mat0 ?m ?n * ?B  => let B' := restore_dims_rec B in 
                          match type of B' with 
                          | mat ?n' ?o' => 
                            constr:(@mmul n' n' o' (@mat0 m n') B')
                          end
    | ?X + @mat0 ?m ?n => let A' := restore_dims_rec A in 
                          match type of A' with 
                          | mat ?m' ?n' => 
                            constr:(@madd m' n' A' (@mat0 m' n'))
                          end
    | @mat0 ?m ?n + ?B => let B' := restore_dims_rec B in 
                          match type of B' with 
                          | mat ?m' ?n' => 
                            constr:(@madd m' n' (@mat0 m' n') B')
                          end
  (* general cases *)
    | ?X = ?B  => let A' := restore_dims_rec A in 
                  let B' := restore_dims_rec B in 
                  match type of A' with 
                  | mat ?m' ?n' => constr:(@meq m' n' A' B')
                    end
    | ?X * ?B   => let A' := restore_dims_rec A in 
                  let B' := restore_dims_rec B in 
                  match type of A' with 
                  | mat ?m' ?n' =>
                    match type of B' with 
                    | mat ?n'' ?o' => constr:(@mmul m' n' o' A' B')
                    end
                  end 
    | ?X + ?B => let A' := restore_dims_rec A in 
                 let B' := restore_dims_rec B in 
                 match type of A' with 
                 | mat ?m' ?n' =>
                   match type of B' with 
                   | mat ?m'' ?n'' => constr:(@madd m' n' A' B')
                   end
                 end
    | ?c * ?X => let A' := restore_dims_rec A in 
                 match type of A' with
                 | mat ?m' ?n' => constr:(@mcmul m' n' c A')
                 end
    (* Handle functions applied to matrices *)
    | ?f ?X    => let f' := restore_dims_rec f in 
                 let A' := restore_dims_rec A in 
                 constr:(f' A')
    (* default *)
    | ?X       => A
     end.

  Ltac restore_dims tac := 
    match goal with
    | |- ?X      => let A' := restore_dims_rec A in 
                  replace A with A' by unify_matrix_dims tac
    end.

  Tactic Notation "restore_dims" tactic(tac) := restore_dims tac.

  Tactic Notation "restore_dims" := 
    restore_dims (try ring; unify_pows_two; simpl; lia).

  (* Why this name? U_db : User database *)
  Global Hint Unfold madd mmul mcmul mat1 : U_db. 

  Hint Rewrite @mmul_1_l @mmul_1_r @mcmul_1_l @mat1_trans_eq : M_db_light.
  Hint Rewrite @mmul_0_l @mmul_0_r @madd_0_l @madd_0_r
    @mcmul_0_l @mcmul_0_r @mat0_trans_eq : M_db_light.

  (* I don't like always doing restore_dims first, but otherwise sometimes leaves 
     unsolvable WF_Matrix goals. *)
  Ltac Msimpl_light := restore_dims; autorewrite with M_db_light.

  Ltac Msimpl := restore_dims; autorewrite with M_db_light.
 *)

