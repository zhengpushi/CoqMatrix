(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector implmented with Recursive Pair
  author    : ZhengPu Shi
  date      : 2021.01
  
  remark    :
  1. the definition of vec inspired by Coquelicot.
  2. all definitions are polymorphism.
  
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Lia.
Require Export BasicConfig SetoidListExt HierarchySetoid.

Open Scope A_scope.
Open Scope vec_scope.

Generalizable Variable A B C Aeq Beq Ceq Aadd Aopp Amul Ainv.


(** ** Definition of vector *)
Section vec.

  Context {A : Type}.
  
  Fixpoint vec (n : nat) : Type :=
    match n with
    | O => unit
    | S n => prod A (vec n)
    end.
  
  (** all vec 0 are same *)
  Lemma vec_0 (v : vec 0) : v = tt.
  Proof.
    destruct v. auto.
  Qed.
  
  (** vec (S n) must be a prod type *)
  Lemma vec_S (n : nat) (v : vec (S n)) : {x & { v' | v = (x, v')}}.
  Proof.
    refine (match v with (x,v') => _ end). eauto.
  Qed.

End vec.

Bind Scope vec_scope with vec.

Notation "[ x ]" := (prod x (vec 0)) : vec_scope.
Notation "[ x1 ; .. ; xn ]" := (pair x1 .. (pair xn tt) .. ) : vec_scope.

(** Simplify a vector expression in hypothesis *)
Ltac vsimp :=
  repeat match goal with
    | v : vec 0 |- _ => rewrite (vec_0 v)
    | v : vec (S ?n) |- _ => destruct v
    | H : ?P (?a1,?v1) (?a2,?v2) |- _ => try destruct H
    end.


(** ** Equality of vec *)
Section veq.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  
  Fixpoint veq {n} : vec n -> vec n -> Prop :=
    match n with
    | O => fun _ _ => True
    | S n' => fun (v1 v2 : vec (S n')) =>
               let (a1,v1') := v1 in
               let (a2,v2') := v2 in
               (a1 == a2) /\ veq v1' v2'
    end.
  Infix "==" := veq : vec_scope.

  Lemma veq_refl : forall n, Reflexive (veq (n:=n)).
  Proof.
    unfold Reflexive. induction n; intros; simpl; auto.
    destruct x. split; auto. easy.
  Qed.

  Lemma veq_sym : forall n, Symmetric (veq (n:=n)).
  Proof.
    unfold Symmetric. induction n; intros; simpl; auto.
    destruct x,y. inv H. split; auto. easy.
  Qed.

  Lemma veq_trans : forall n, Transitive (veq (n:=n)).
  Proof.
    unfold Transitive. induction n; intros; simpl; auto.
    destruct x,y,z. inv H. inv H0. split; auto.
    rewrite H1; auto. apply IHn with v0; auto.
  Qed.

  Lemma veq_equiv : forall n : nat, Equivalence (veq (n:=n)).
  Proof.
    constructor. apply veq_refl. apply veq_sym. apply veq_trans.
  Qed.

  Global Existing Instance veq_equiv.

  (** veq is decidable *)
  Lemma veq_dec : forall n (Dec_Aeq : Decidable Aeq), Decidable (veq (n:=n)).
  Proof.
    induction n; constructor; intros.
    - rewrite (vec_0 a), (vec_0 b). left. easy.
    - destruct a,b.
      destruct (decidable a a0), (decidable v v0).
      + left. split; auto.
      + right. intro. inv H. easy.
      + right. intro. inv H. easy.
      + right. intro. inv H. easy.
  Qed.
  
  (** Bool equality of vec *)
  Fixpoint veqb {n : nat} (Aeqb : A -> A -> bool) : vec n -> vec n -> bool := 
    match n with
    | O => fun (v1 v2 : vec 0) => true
    | S n' => fun (v1 v2 : vec (S n')) => 
               andb (Aeqb (fst v1) (fst v2)) (veqb Aeqb (snd v1) (snd v2))
    end.

End veq.


(** ** pair, fst, snd *)
Section pair_fst_snd.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : A_scope.

  (** pair is a proper morphism *)
  Lemma pair_aeq_mor : forall n, 
      Proper (Aeq ==> veq (Aeq:=Aeq)(n:=n) ==> veq (Aeq:=Aeq)(n:=S n)) (pair).
  Proof.
    unfold Proper, respectful. induction n; intros; vsimp; simpl; auto.
  Qed.

  Global Existing Instance pair_aeq_mor.

  (** fst is a proper morphism *)
  Lemma fst_aeq_mor : forall n,
      Proper (veq (Aeq:=Aeq)(n:=S n) ==> Aeq) (fst).
  Proof.
    unfold Proper, respectful. induction n; intros; vsimp; simpl; auto.
  Qed.

  Global Existing Instance fst_aeq_mor.

  (** snd is a proper morphism *)
  Lemma snd_aeq_mor : forall n,
      Proper (veq (Aeq:=Aeq)(n:=S n) ==> veq (Aeq:=Aeq)(n:=n)) (snd).
  Proof.
    unfold Proper, respectful. induction n; intros; vsimp; simpl; auto.
  Qed.

  Global Existing Instance snd_aeq_mor.

End pair_fst_snd.


(** ** Construct a vector with same element *)
Section vconst.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : A_scope.

  Fixpoint vconst (n : nat) (val : A) : vec n :=
    match n with
    | O => tt
    | S n' => (val, vconst n' val)
    end.

  Lemma vconst_aeq_mor : forall n, Proper (Aeq ==> veq (Aeq:=Aeq)(n:=n)) (vconst n).
  Proof.
    unfold Proper, respectful. induction n; intros; simpl; auto.
  Qed.

  Global Existing Instance vconst_aeq_mor.

End vconst.

Arguments vconst {A}.


(** ** vec0, its elements is 0 *)
Section vec0.

  Context `{Equiv_Aeq : Equivalence A Aeq} (A0 : A).
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : A_scope.
  
  Definition vec0 (n : nat) := vconst n A0.
  
  Lemma vec0_S : forall n, vec0 (S n) == (A0, vec0 n).
  Proof.
    intros; simpl. easy.
  Qed.
  
  Lemma vec0_eq_vconst0 : forall n, vec0 n = vconst n A0.
  Proof. auto. Qed.
  
End vec0.

(** ** head and tail of a vector *)
Section vhd_vtl.

  Context `{Equiv_Aeq : Equivalence A Aeq} (A0 : A).
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : A_scope.

  Definition vhd {n} : vec n -> A :=
    match n with
    | O => fun (_ : vec O) => A0
    | S n' => fun (v : vec (S n')) => fst v
    end.

  Definition vtl {n} (v : @vec A (S n)) : vec n := snd v.
  
End vhd_vtl.


(** ** Get last element *)
Section vlast.

  Context `{Equiv_Aeq : Equivalence A Aeq} (A0 : A).
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : A_scope.

  (* why fail? *)
  Fail Fixpoint vlast {n : nat} : vec n -> A :=
    match n with
    | O => fun (_ : vec O) => A0
    | 1 => fun (v : vec 1) => fst v
    | S n' => fun (v : vec (S n')) => @vlast n' (snd v)
    end.

  Fixpoint vlast {n} : vec (S n) -> A :=
    match n with
    | O => fun (v : vec 1) => fst v
    | S n' => fun (v : vec (S (S n'))) => vlast (snd v)
    end.
  
End vlast.


(** Construct a vector with a function *)
Section vmake.

  Context `{Equiv_Aeq : Equivalence A Aeq} (A0 : A).
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : A_scope.

  (* it is wrong direction, we need (f 0, f 1 ..), but got (f n, f (n-1) ..) *)
  Fixpoint vmake_old (n : nat) (f : nat  -> A) : vec n :=
    match n with
    | O => tt
    | S n' => (f n', vmake_old n' f)
    end.

  (** Generate vector with an offset, that is : f i, f (i+1), ... *)
  Fixpoint vmakeAux (n : nat) (i : nat) (f : nat  -> A) : vec n :=
    match n with
    | O => tt
    | S n' => (f i, vmakeAux n' (S i) f)
    end.

  (** vmakeAux is proper morphism *)
  Lemma vmakeAux_aeq_mor : forall n : nat,
      Proper (eq ==> (eq ==> Aeq) ==> veq (Aeq:=Aeq)(n:=n)) (vmakeAux n).
  Proof.
    unfold Proper, respectful.
    induction n; intros; simpl; auto.
  Qed.

  Global Existing Instance vmakeAux_aeq_mor.

  Lemma vmakeAux_S : forall (n : nat) (i : nat) (f : nat  -> A),
      vmakeAux n (S i) f == vmakeAux n i (fun j => f (S j)).
  Proof.
    induction n; intros; simpl; auto. split; auto. easy.
  Qed.
  
  Lemma vmakeAux_const_eq_vconst : forall n i a,
      (vmakeAux n i (fun _ : nat => a) == vconst n a).
  Proof.
    induction n; intros; simpl; easy.
  Qed.
  
  Definition vmake (n : nat) (f : nat  -> A) : vec n := vmakeAux n 0 f.
  
  Lemma vmake_0 : forall (f : nat  -> A), vmake 0 f = tt.
  Proof.
    auto.
  Qed.

  Lemma vmake_S : forall n (f : nat  -> A), vmake (S n) f == (f 0, vmake n (fun i => f (S i))).
  Proof.
    intros. simpl. split; try easy. apply vmakeAux_S.
  Qed.

  Lemma vmake_const_eq_vconst : forall n a, (vmake n (fun _ : nat => a) == vconst n a).
  Proof.
    intros. apply vmakeAux_const_eq_vconst.
  Qed.

End vmake.


(** ** Append two vectors *)
Section vapp.

  Context {A : Type}.

  Fixpoint vapp {n1 n2} : @vec A n1 -> vec n2 -> vec (n1 + n2) := 
    match n1 with
    | 0 => fun (v1 : vec 0) (v2 : vec n2) => v2
    | S n1' => fun (v1 : vec (S n1')) (v2 : vec n2) =>
                (fst v1, vapp (snd v1) v2)
    end.

End vapp.


(** Reverse a vector *)
Section vrev.
  
  Variable A : Type.

  Fail Fixpoint vrev {n : nat} : @vec A n -> @vec A n :=
    match n with
    | O => fun _ => let v : @vec A 0 := tt in v
    | S n' => fun (v : @vec A (S n')) => let (x, v') := v in
                                      @vapp A n' 1 (vrev v') [x]
    end.

End vrev.


(** Get n-th element of a vector *)
Section vnth.

  Context `{Equiv_Aeq : Equivalence A Aeq} {A0 : A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.
  
  Fixpoint vnth {n} (i : nat) : (vec n) -> A :=
    match n with
    | O => fun (_ : vec O) => A0
    | S n' => fun (v : vec (S n')) =>
               match i with
               | O => (fst v)
               | S i' => vnth i' (snd v)
               end
    end.

  (** vnth is a proper morphism *)
  Lemma vnth_aeq_mor : forall n, Proper (eq ==> veq (Aeq:=Aeq) (n:=n) ==> Aeq) vnth.
  Proof.
    unfold Proper, respectful.
    induction n; intros; vsimp; try easy.
    simpl. destruct x,y; auto; try easy.
  Qed.

  Global Existing Instance vnth_aeq_mor.
  
  Lemma vnth_0 {n} (v : vec (S n)) : (vnth 0 v == fst v)%A.
  Proof.
    destruct v. simpl. easy.
  Qed.

  Lemma vnth_S {n} i (v : vec (S n)) :
    (* let (_, v') := v in (vnth (S i) v == vnth i v')%A. *)
    (vnth (S i) v == vnth i (snd v))%A.
  Proof.
    simpl. easy.
  Qed.
  
  (** Every element pair of two vectors are same iff the two vectors same *)
  Lemma veq_iff_vnth : forall {n} (v1 v2 : vec n),
      v1 == v2 <-> (forall i, i < n -> (vnth i v1 == vnth i v2)%A).
  Proof.
    induction n; intros; vsimp; split; intros; try easy; vsimp.
    - destruct i; simpl; auto. apply IHn; auto. lia.
    - split.
      + apply (H 0). lia.
      + apply IHn. intros. apply (H (S i)). lia.
  Qed.

  Lemma vnth_const : forall n i (a : A), i < n -> (vnth i (vconst n a) == a)%A.
  Proof.
    induction n; intros; simpl. lia. destruct i. easy. apply IHn. lia.
  Qed.
  
  Lemma vnth_vec0 : forall n i, (vnth i (vec0 A0 n) == A0)%A.
  Proof.
    induction n; intros; simpl. easy. destruct i; auto. easy.
  Qed.
  
  Lemma vnth_vmake_valid : forall {n} f i, i < n -> (vnth i (vmake n f) == f i)%A.
  Proof.
    induction n; intros; simpl. lia. destruct i. easy.
    rewrite vmakeAux_S. unfold vmake in *. rewrite IHn. easy. lia.
  Qed.
  
  Lemma vnth_vmake_invalid : forall {n} f i, i >= n -> (vnth i (vmake n f) == A0)%A.
  Proof. 
    induction n; intros; simpl. easy. destruct i. easy. unfold vmake in *.
    rewrite vmakeAux_S. rewrite IHn. easy. lia.
  Qed.

  Lemma vnth_vmakeAux_valid : forall {n} f i j,
      i+j < n -> (vnth i (vmakeAux n j f) == f (i + j))%A.
  Proof.
    induction n; intros; simpl. lia. destruct i. easy.
    rewrite vmakeAux_S. rewrite IHn. easy. lia.
  Qed.
  
  Lemma vnth_vmakeAux_invalid : forall {n} f i j,
      i >= n -> (vnth i (vmakeAux n j f) == A0)%A.
  Proof. 
    induction n; intros; simpl. easy. destruct i. easy.
    rewrite vmakeAux_S. rewrite IHn. easy. lia.
  Qed.

End vnth.

(** ** Get top or remain element of a vector *)
Section vfirstn_vskipn.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0 : A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.

  (** Get top k elements of a vector *)
  Fixpoint vfirstn {n} (k : nat) : (vec n) -> (vec k) := 
    match n,k with
    | O, O => fun (v : vec O) => tt
    | O, S k' => fun (v : vec O) => (A0, vfirstn k' v)
    | S n', O => fun (v : vec (S n')) => tt
    | S n', S k' => fun (v : vec (S n')) => (fst v, vfirstn k' (snd v))
    end.

  (** Get remain (n-k) elements of a vector *)
  Fixpoint vskipn {n} (k : nat) : @vec A n -> vec (n-k) := 
    match n,k with
    | O, O => fun (v : vec 0) => let v1 : vec (0-0) := tt in v1
    | O, S k' => fun (v : vec O) => let v1 : vec (0 - (S k')) := tt in v1
    | S n', O => fun (v : vec (S n')) => let v1 : vec (S n' - 0) := v in v1
    | S n', S k' => fun (v : vec (S n')) => let v1 : vec (S n' - S k') :=
                                              vskipn k' (snd v) in v1
    end.

End vfirstn_vskipn.


(** ** Maping of a vector *)
Section vmap.
  (* Context `{Equiv_Aeq : Equivalence A Aeq} {A0 : A}. *)
  (* Context `{Equiv_Beq : Equivalence B Beq} {B0 : A}. *)
  Context `{Aeq : relation A} `{Beq : relation B}.
  (* Infix "==" := Aeq : A_scope. *)
  (* Infix "==" := (veq (Aeq:=Aeq)) : vec_scope. *)

  (** Maping of a vector *)
  Fixpoint vmap {n} (f : A -> B) : @vec A n -> @vec B n :=
    match n with
    | O => fun (v : vec 0) => tt
    | S n' => fun (v : vec (S n')) => (f (fst v), vmap f (snd v))
    end.

  (** vmap is proper morphism *)
  Lemma vmap_aeq_mor : forall n : nat,
      Proper ((Aeq ==> Beq) ==> veq (Aeq:=Aeq) ==> veq (Aeq:=Beq)) (vmap (n:=n)).
  Proof.
    unfold Proper, respectful.
    induction n; intros; simpl; auto; vsimp.
    split; auto.
  Qed.

  Global Existing Instance vmap_aeq_mor.

End vmap.


(** ** Maping of two vectors *)
Section vmap2.
  Context `{Aeq : relation A} `{Beq : relation B}.
  Context `{Equiv_Ceq : Equivalence C Ceq}.
  Infix "==" := (veq (Aeq:=Ceq)) : vec_scope.

  (** Maping of two vectors *)
  Fixpoint vmap2 {n} (f : A -> B -> C) : @vec A n -> @vec B n -> @vec C n :=
    match n with
    | O => fun (v1 : vec 0) (v2 : vec 0) => tt
    | S n' => fun (v1 : vec (S n')) (v2 : vec (S n')) => 
                (f (fst v1) (fst v2), vmap2 f (snd v1) (snd v2))
    end.
  
  (** vmap2 is proper morphism *)
  Lemma vmap2_aeq_mor : forall n,
      Proper ((Aeq ==> Beq ==> Ceq) ==>
                veq (Aeq:=Aeq) ==>
                veq (Aeq:=Beq) ==>
                veq (Aeq:=Ceq)) (vmap2 (n:=n)).
  Proof.
    unfold Proper, respectful.
    induction n; intros; simpl; auto; vsimp; simpl.
    split; auto.
  Qed.

  Global Existing Instance vmap2_aeq_mor.

  Lemma vmap2_S : forall {n} f t1 t2 (v1 v2 : vec n),
      vmap2 f ((t1, v1):vec (S n)) (t2, v2) == (f t1 t2, vmap2 f v1 v2).
  Proof.
    intros. simpl. easy.
  Qed.

End vmap2.


(** Properties of vmap2 with same type *)
Section vmap2_sametype.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.
  
  Lemma vmap2_comm {n} f (fComm : Commutative f Aeq)
      (v1 v2 : vec n): vmap2 f v1 v2 == vmap2 f v2 v1.
  Proof.
    induction n; intros; destruct v1,v2; simpl; try easy. split; auto.
    apply commutative.
  Qed.

  Lemma vmap2_assoc {n} f (fAssoc : Associative f Aeq)
    (v1 v2 v3 : vec n) :
    vmap2 f (vmap2 f v1 v2) v3 == vmap2 f v1 (vmap2 f v2 v3).
  Proof.
    induction n; intros; destruct v1,v2; simpl; try easy. split; auto.
    apply associative.
  Qed.

End vmap2_sametype.


(** ** Fold a vector to an element *)
Section vfold.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.
  
  (** Fold a vector to an element from left to right *)
  Fixpoint vfoldl {n} (Aadd : A -> A -> A) (A0 : A) : (vec n) -> A := 
    match n with
    | O => fun (v : vec 0) => A0
    | S n' => fun (v : vec (S n')) => Aadd (fst v) (vfoldl Aadd A0 (snd v))
    end.

  (** Fold a vector to an element from right to left *)
  Fixpoint vfoldr {n} (Aadd : A -> A -> A) (A0 : A) : (vec n) -> A := 
    match n with
    | O => fun (v : vec 0) => A0
    | S n' => fun (v : vec (S n')) => Aadd (vfoldr Aadd A0 (snd v)) (fst v)
    end.

  (** vfoldl is proper morphism *)
  Lemma vfoldl_aeq_mor : forall (n : nat) (f : A -> A -> A)
                           {fProper : Proper (Aeq ==> Aeq ==> Aeq) f},
      Proper (Aeq ==> veq (Aeq:=Aeq) (n:=n) ==> Aeq) (vfoldl f).
  Proof.
    unfold Proper, respectful.
    induction n; intros; vsimp; simpl. easy. f_equiv; auto.
  Qed.

  Global Existing Instance vfoldl_aeq_mor.


  (** ToDo: A problem *)
  Section a_problem.
    
    Variable (Aadd Amul : A -> A -> A) (A0 A1 : A).
    Variable (AaddProper : Proper (Aeq ==> Aeq ==> Aeq) Aadd).

    Goal forall n (v1 v2 : vec n),
        v1 == v2 ->
        (vfoldl Aadd A0 v1 == vfoldl Aadd A0 v2)%A.
    Proof.
      intros.
      (** why f_equiv here cannot reduce to a "==" relation, but a "=" relation ? *)
      (* f_equiv. *)
      rewrite H. easy.
    Abort.

  End a_problem.

End vfold.


(** ** Concatenation a nested vector to a plain vector *)
Section vvflat.
  Context {A : Type}.
  
  Fixpoint vvflat {r c} : (@vec (@vec A c) r) -> @vec A (r * c) :=
    match r with
    | O => fun (m : @vec (vec c) 0) => tt
    | S r' => fun (m : @vec (vec c) (S r')) =>
                vapp (fst m) (vvflat (snd m))
    end.

End vvflat.


(** ** Convert between vector and list *)
Section v2l_l2v.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0 : A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.
  
  Fixpoint v2l {n} : @vec A n -> list A :=
    match n with
    | 0 => fun (v : @vec A 0) => nil
    | S n' => fun (v : @vec A (S n')) => cons (fst v) (v2l (snd v))
    end.
  
  Lemma v2l_length : forall n (v : @vec A n), length (v2l v) = n.
  Proof.
    induction n; intros; destruct v; simpl; auto.
  Qed.
  
  Fixpoint l2v (l : list A) (n : nat) {struct n} : vec n :=
    match n as n0 return (vec n0) with
    | 0 => tt
    | S n' => (hd A0 l, l2v (tl l) n')
    end.
  
  Lemma v2l_l2v_id : forall (n : nat) (l : list A),
      length l = n -> (v2l (l2v l n) == l)%list.
  Proof.
    induction n; intros; simpl.
    - apply length_zero_iff_nil in H. subst. easy.
    - destruct l. easy. apply cons_aeq_mor; auto. simpl. easy.
  Qed.
  
  Lemma l2v_v2l_id : forall (n : nat) (v : vec n), l2v (v2l v) n == v.
  Proof.
    induction n; destruct v; simpl; auto. split; auto. easy.
  Qed.
  
End v2l_l2v.

(* Check ([1;2;3] : vec 3). *)
(* Compute v2l ([1;2;3] : vec 3). *)
(* Compute l2v (cons 1 (cons 2 nil)) 2. *)


(** ** Vector algebric *)
Section vec_alg.
  
  (* Variable A : Type. *)
  (* Variable A0 : A. *)
  (* Variable fadd : A -> A -> A. *)
  (* Variable fadd_comm : forall a b, fadd a b = fadd b a. *)
  (* Variable fadd_assoc : forall a b c, fadd (fadd a b) c = fadd a (fadd b c). *)
  (* Variable fadd_0_l : forall t, fadd A0 t = t. *)
  (* Variable fmul : A -> A -> A. *)
  (* Variable fmul_add_distr_l : forall a b1 b2, *)
  (*     fmul a (fadd b1 b2) = fadd (fmul a b1) (fmul a b2). *)
  (* Variable fmul_add_distr_r : forall a1 a2 b, *)
  (*     fmul (fadd a1 a2) b = fadd (fmul a1 b) (fmul a2 b). *)

  Context `{AG : AGroup}.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := (fun a b => a + (-b)) : A_scope.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.

  
  (** *** vector addition *)
  
  Definition vadd {n} (v1 v2 : vec n) : vec n := vmap2 Aadd v1 v2.
  Infix "+" := vadd : vec_scope.
  
  (** vadd is proper morphism *)
  Lemma vadd_aeq_mor : forall n,
      Proper (veq (Aeq:=Aeq) ==> veq (Aeq:=Aeq) ==> veq (Aeq:=Aeq)) (vadd (n:=n)).
  Proof.
    unfold Proper, respectful.
    induction n; intros; vsimp; simpl; auto. split.
    - apply monoidAaddProper; auto.
    - apply IHn; auto.
  Qed.

  Global Existing Instance vadd_aeq_mor.

  (** v1 + v2 = v2 + v1 *)
  Lemma vadd_comm {n} (v1 v2 : vec n): v1 + v2 == v2 + v1.
  Proof.
    apply vmap2_comm. apply amonoidComm.
  Qed.

  (** (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma vadd_assoc {n} (v1 v2 v3 : vec n): (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof.
    apply vmap2_assoc. apply monoidAssoc.
  Qed.

  (** (t1,v1) + (t2,v2) = (t1 + t2, v1 + v2) *)
  Lemma vadd_S : forall {n} t1 t2 (v1 v2 : vec n),
      ((t1, v1) : vec (S n)) + (t2, v2) == (Aadd t1 t2, v1 + v2).
  Proof.
    intros; simpl. easy.
  Qed.

  (** vec0 + v = v *)
  Lemma vadd_0_l : forall {n} (v : vec n), (vec0 A0 n) + v == v.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [group_simpl|apply IHn].
  Qed.

  (** v + vec0 = v *)
  Lemma vadd_0_r : forall {n} (v : vec n), v + (vec0 A0 n) == v.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [group_simpl|apply IHn].
  Qed.


  (** *** vector opposition *)
  
  Definition vopp {n} (v : vec n) : vec n := vmap Aopp v.
  Notation "- v" := (vopp v) : vec_scope.

  (** vopp is proper morphism *)
  Lemma vopp_aeq_mor : forall n,
      Proper (veq (Aeq:=Aeq) ==> veq (Aeq:=Aeq)) (vopp (n:=n)).
  Proof.
    unfold Proper, respectful.
    induction n; intros; vsimp; simpl; auto. split.
    - apply groupAoppProper; auto.
    - apply IHn; auto.
  Qed.

  Global Existing Instance vopp_aeq_mor.

  (** - (a,v) = (-a, -v) *)
  Lemma vopp_S : forall {n} a (v : vec n), - ((a, v) : vec (S n)) == ((-a)%A, - v).
  Proof.
    intros. easy.
  Qed.

  (** - (- v) = v *)
  Lemma vopp_vopp : forall {n} (v : vec n), - (- v) == v.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [apply group_inv_inv| apply IHn].
  Qed.

  (** (-v) + v = vec0 *)
  Lemma vadd_vopp_l : forall {n} (v : vec n), (-v) + v == vec0 A0 n.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [group_simpl|apply IHn].
  Qed.

  (** v + (-v) = vec0 *)
  Lemma vadd_vopp_r : forall {n} (v : vec n), v + (-v) == vec0 A0 n.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [group_simpl|apply IHn].
  Qed.
  
  
  (** *** vector subtraction *)
  
  Definition vsub {n} (v1 v2 : vec n) : vec n := v1 + (- v2).
  Infix "-" := vsub : vec_scope.

  (** vsub is proper morphism *)
  Lemma vsub_aeq_mor : forall n,
      Proper (veq (Aeq:=Aeq) ==> veq (Aeq:=Aeq) ==> veq (Aeq:=Aeq)) (vsub (n:=n)).
  Proof.
    unfold Proper, respectful.
    induction n; intros; vsimp; simpl; auto. split.
    - apply monoidAaddProper; auto. apply groupAoppProper; auto.
    - apply IHn; auto.
  Qed.

  Global Existing Instance vsub_aeq_mor.

  (** v1 - v2 = - (v2 - v1) *)
  Lemma vsub_comm : forall {n} (v1 v2 : vec n), v1 - v2 == - (v2 - v1).
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [ | apply IHn].
    rewrite group_inv_distr. rewrite group_inv_inv. easy.
  Qed.

  (** (v1 - v2) - v3 = v1 - (v2 + v3) *)
  Lemma vsub_assoc {n} (v1 v2 v3 : vec n): (v1 - v2) - v3 == v1 - (v2 + v3).
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [| apply IHn].
    group_simpl. f_equiv. rewrite group_inv_distr. apply commutative.
  Qed.

  (** (a1,v1) - (a2,v2) = (a1-a2, v1-v2) *)
  Lemma vsub_S : forall {n} a1 a2 (v1 v2 : vec n),
      ((a1,v1):vec (S n)) - (a2,v2) == ((a1-a2)%A, v1-v2).
  Proof.
    intros. easy.
  Qed.

  (** vec0 - v = - v *)
  Lemma vsub_0_l : forall {n} (v : vec n), (vec0 A0 n) - v == - v.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [group_simpl|apply IHn].
  Qed.

  (** v - vec0 = v *)
  Lemma vsub_0_r : forall {n} (v : vec n), v - (vec0 A0 n) == v.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [|apply IHn].
    rewrite group_opp_zero_eq_zero. group_simpl.
  Qed.

  (** v - v = vec0 *)
  Lemma vsub_self : forall {n} (v : vec n), v - v == vec0 A0 n.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [group_simpl| apply IHn].
  Qed.

  
  (** *** Vector Group *)
  
  (** vec operation has a group structure *)
  Lemma vec_AG : forall n, @AGroup (vec (A:=A) n) vadd (vec0 A0 n) vopp (veq (Aeq:=Aeq)).
  Proof.
    intros. repeat constructor;
      try apply veq_equiv;
      auto using vadd_aeq_mor, vopp_aeq_mor, vadd_assoc, vadd_comm;
      auto using vadd_0_l, vadd_0_r, vopp_aeq_mor, vadd_vopp_l, vadd_vopp_r.
  Qed.


  (** *** Below, need Ring structure *)

  Context `{R : Ring A Aadd A0 Aopp Amul A1 Aeq}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : make_ring_theory.

  
  (** *** vector scalar multiplication *)
  
  Definition vcmul {n} a v : vec n := vmap (fun x => a * x) v.
  Infix "c*" := vcmul : vec_scope.
  
  Definition vmulc {n} v a : vec n := vmap (fun x => x * a) v.
  Infix "*c" := vmulc : vec_scope.

  (** vcmul is proper morphism *)
  Lemma vcmul_aeq_mor : forall n,
      Proper (Aeq ==> veq (Aeq:=Aeq) ==> veq (Aeq:=Aeq)) (vcmul (n:=n)).
  Proof.
    unfold Proper, respectful.
    induction n; intros; vsimp; simpl; auto. split; auto.
    - rewrite H,H0. easy.
    - apply IHn; auto. 
  Qed.

  Global Existing Instance vcmul_aeq_mor.
  
  (** a c* v = v *c a *)
  Lemma vmulc_eq_vcmul : forall {n} a (v : vec n), v *c a == a c* v.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [ring | apply IHn].
  Qed.

  (** a c* (b,v) = (a*b, a c* v) *)
  Lemma vcmul_S : forall {n} a b (v : vec n), a c* ((b,v):vec (S n)) == (a*b, a c* v).
  Proof.
    intros; simpl. easy.
  Qed.

  (** (b,v) *c a = (b*a, v *c a) *)
  Lemma vmulc_S : forall {n} a b (v : vec n), ((b,v):vec (S n)) *c a == (b*a, v *c a).
  Proof.
    intros; simpl. easy.
  Qed.
  
  (** 0 c* v = vec0 *)
  Lemma vcmul_0_l : forall {n} (v : vec n), A0 c* v == vec0 A0 n.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [ring | apply IHn].
  Qed.
  
  (** a c* vec0 = vec0 *)
  Lemma vcmul_0_r : forall {n} a, a c* (vec0 A0 n) == vec0 A0 n.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [ring | apply IHn].
  Qed.
  
  (** 1 c* v = v *)
  Lemma vcmul_1_l : forall {n} (v : vec n), A1 c* v == v.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [ring | apply IHn].
  Qed.
  
  (** a c* (v1 + v2) = a c* v1 + a c* v2 *)
  Lemma vcmul_add_distr_l : forall {n} a (v1 v2 : vec n),
      a c* (v1 + v2) == a c* v1 + a c* v2.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [ring | apply IHn].
  Qed.

  (** (a + b) c* v = a c* v + b c* v *)
  Lemma vcmul_add_distr_r : forall {n} a b (v : vec n),
      (a + b)%A c* v == a c* v + b c* v.
  Proof.
    induction n; intros; vsimp; simpl; auto. split; [ring | apply IHn].
  Qed.

  
  (* Variable fmul : A -> A -> A. *)
  (* Variable fmul_comm : forall a b, fmul a b = fmul b a. *)
  (* Variable fmul_assoc : forall a b c, fmul (fmul a b) c = fmul a (fmul b c). *)

  (** a c* (b c* v) = (a * b) c* v *)
  Lemma vcmul_assoc : forall {n:nat} a b (v : vec n), a c* (b c* v) == (a * b) c* v.
  Proof.
    induction n; intros; simpl; auto. split; try apply IHn. ring.
  Qed.

  (** a c* (b c* v) = b c* (a c* v) *)
  Lemma vcmul_perm : forall {n} a b (v : vec n), a c* (b c* v) == b c* (a c* v).
  Proof.
    induction n; intros; simpl; auto. split; try apply IHn. ring.
  Qed.

  
  (** *** Vector Dot Product *)
  
  Definition vdot {n} (v1 v2 : vec n) := vfoldl Aadd A0 (vmap2 Amul v1 v2).
  Infix "\o" := vdot : vec_scope.

  (** vdot is proper morphism *)
  Lemma vdot_aeq_mor : forall n,
      Proper (veq (Aeq:=Aeq) ==> veq (Aeq:=Aeq) ==> Aeq) (vdot (n:=n)).
  Proof.
    unfold Proper, respectful.
    intros. apply vfoldl_aeq_mor; try easy.
    apply monoidAaddProper.
    rewrite H,H0. easy.
  Qed.

  Global Existing Instance vdot_aeq_mor.
  
  (** (a1,v1) \o (a2,v2) = (a1*a2) + (v1 \o v2) *)
  Lemma vdot_S : forall {n} (a1 a2 : A) (v1 v2 : vec n),
       (((a1,v1):vec (S n)) \o (a2,v2) == (a1*a2) + (v1 \o v2))%A.
  Proof.
    unfold vdot. intros. simpl. easy.
  Qed.

  (** v1 \o v2 = v2 \o v1 *)
  Lemma vdot_comm {n} (v1 v2 : vec n) : (v1 \o v2 == v2 \o v1)%A.
  Proof.
    unfold vdot. apply vfoldl_aeq_mor.
    apply groupAaddProper. easy.  apply vmap2_comm. apply amonoidComm.
  Qed.

  (* (** vec0 \o vec0 = 0 *) *)
  (* Lemma vdot_vec0 (v : vec 0) : (v \o v == A0)%A. *)
  (* Proof. unfold vdot. simpl. easy. Qed. *)

  (** vec0 \o v = 0 *)
  Lemma vdot_0_l : forall {n} (v : vec n), ((vec0 A0 n) \o v == A0)%A.
  Proof.
    unfold vdot. induction n; intros; simpl; auto. easy. rewrite IHn. ring.
  Qed.

  (** v \o vec0 = 0 *)
  Lemma vdot_0_r : forall {n} (v : vec n), (v \o (vec0 A0 n) == A0)%A.
  Proof.
    unfold vdot. induction n; intros; simpl; auto. easy. rewrite IHn. ring.
  Qed.

  (** (a c* v1) \o v2 = a * (v1 \o v2) *)
  Lemma vdot_vcmul_l : forall {n} a (v1 v2 : vec n), ((a c* v1) \o v2 == a * (v1 \o v2))%A.
  Proof.
    unfold vdot,vcmul. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
  Qed.

  (** v1 \o (a c* v2) = a * (v1 \o v2) *)
  Lemma vdot_vcmul_r : forall {n} a (v1 v2 : vec n), (v1 \o (a c* v2) == a * (v1 \o v2))%A.
  Proof.
    unfold vdot,vcmul. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
  Qed.

  (** (v1 *c a) \o v2 = a * (v1 \o v2) *)
  Lemma vdot_vmulc_l : forall {n} a (v1 v2 : vec n), ((v1 *c a) \o v2 == a * (v1 \o v2))%A.
  Proof.
    unfold vdot,vmulc. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
  Qed.
  
  (** v1 \o (v2 *c a) = a * (v1 \o v2) *)
  Lemma vdot_vmulc_r : forall {n} a (v1 v2 : vec n), (v1 \o (v2 *c a) == a * (v1 \o v2))%A.
  Proof.
    unfold vdot,vmulc. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
  Qed.

  (** v1 \o (v2 + v3) = (v1 \o v2) + (v1 \o v3) *)
  Lemma vdot_vadd_l : forall {n} (v1 v2 v3 : vec n),
      (v1 \o (v2 + v3) == (v1 \o v2) + (v1 \o v3))%A.
  Proof.
    unfold vdot,vadd. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
  Qed.

  (** (v1 + v2) \o v3 = (v1 \o v3) + (v2 \o v3) *)
  Lemma vdot_vadd_r : forall {n} (v1 v2 v3 : vec n),
      ((v1 + v2) \o v3 == (v1 \o v3) + (v2 \o v3))%A.
  Proof.
    unfold vdot,vadd. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
  Qed.

  (** *** Vector multiplication *)

  (** vector multiplication: vec n1 -> vec n2 -> vec n2.
      Def: (a1 a2) * (b1 b2 b3) = (a1*b1+a2*b1  a1*b2+a2*b2  a1*b3+a2*b3
      (1) = (a1+a2+..) c* (b1 b2 b3)
      (2) = a1 c* (b1 b2 b3) + a2 c* (b1 b2 b3) + ...
   *)

  (* Context `{Equiv_Aeq : Equivalence A Aeq}. *)
  (* Context {Aadd Amul : A -> A -> A} {A0 : A}. *)

  (** Vector multiplication implemented with method (1) *)
  Definition vmul {n1 n2} (v1 : vec n1) (v2 : vec n2) : vec n2 :=
    vcmul (vfoldl Aadd A0 v1) v2.

  (** Vector multiplication implemented with method (2) *)
  Definition vmul' {n1 n2} (v1 : vec n1) (v2 : vec n2) : vec n2 :=
    let v' : vec n1 := vmap (fun (a:A) => (vcmul a v2)) v1 in 
    vfoldl vadd (vec0 A0 n2) v'.

  (** vmul and vmul' are equivalent *)
  Lemma vmul_eq_vmul' : forall n1 n2 (v1 : vec n1) (v2 : vec n2), vmul v1 v2 == vmul' v1 v2.
  Proof.
    unfold vmul, vmul'.
    induction n1; intros; vsimp; simpl.
    - rewrite vcmul_0_l. easy.
    - rewrite vcmul_add_distr_r. f_equiv. auto.
  Qed.
  
End vec_alg.


(** ** Linear Space. These code is for test *)
Section LinearSpace.
  
  (** definition of Linear Space:
  V ~~ vec
  P ~~ A
  + ~~ vadd
  . ~~ vcmul/vmulc
   *)

  Open Scope A_scope.
  Open Scope vec_scope.
  
  (* dimension *)
  Variable n : nat.
  
  (* P *)
  Context `{R : Ring}.
  Add Ring ring_inst : make_ring_theory.
  
  Notation "- t" := (Aopp t) : A_scope.
  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.

  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.
  Infix "+" := (vadd (Aadd:=Aadd)) : vec_scope.
  Infix "c*" := (vcmul (Amul:=Amul)) : vec_scope.
  Infix "*c" := vmulc : vec_scope.
  
  (* (1), v1 + v2 = v2 + v1 *)
  Lemma Vadd_comm : forall (v1 v2 : vec n), v1 + v2 == v2 + v1.
  Proof.
    intros. apply vadd_comm.
  Qed.
  
  (* (2), (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma Vadd_assoc : forall (v1 v2 v3 : vec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof.
    intros. apply vmap2_assoc. apply monoidAssoc.
  Qed.
  
  (* (3), v + 0 = v *)
  Lemma Vadd_0_r : forall (v : vec n), v + (vec0 A0 n) == v.
  Proof.
    intros. apply vadd_0_r.
  Qed.
  
  (* (4), forall v1 in V, (exist v2, (v1 + v2 = 0)) *)
  Lemma Vopp_exist : forall (v1 : vec n), {v2 | v1 + v2 == vec0 A0 n}.
  Proof.
    destruct n; intros; vsimp; simpl. exists tt; auto.
    exists (-a, vmap Aopp v). simpl. split. ring.
    induction n0; vsimp; simpl; auto. split; auto. ring.
  Qed.
  
  (* (5) 1 . v = v *)
  Lemma Vcmul_1_l : forall (v : vec n), A1 c* v == v.
  Proof.
    intros. apply vcmul_1_l.
  Qed.
  
  (* (6) k . (m . v) = (km) . v *)
  Lemma Vcmul_assoc : forall (k m : A) (v : vec n), k c* (m c* v) == (k*m) c* v.
  Proof.
    unfold vcmul. induction n; intros; vsimp; simpl; auto. split; auto. ring.
  Qed.
  
  (* (7) (k + m) . v = k.v + m.v *)
  Lemma Vcmul_dist_c : forall (k m : A) (v : vec n),
      (k + m)%A c* v == (k c* v) + (m c* v).
  Proof.
    intros. apply vcmul_add_distr_r.
  Qed.
  
  (* (8) k . (v1 + v2) = k.v1 + k.v2 *)
  Lemma Vcmul_dist_v : forall (k : A) (v1 v2 : vec n),
      k c* (v1 + v2) == (k c* v1) + (k c* v2).
  Proof.
    intros. apply vcmul_add_distr_l.
  Qed.
  
End LinearSpace.
