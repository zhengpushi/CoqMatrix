(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Dependent List
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. use Coq.Vectors.Vector
  2. given more functions and properties
  3. some design ideas com from CoLoR

  rewrite command:
  rewrite !A: rewriting A as long as possible (at least once)
  rewrite ?A: rewriting A as long as possible (possibly never)
  rewrite 3?A: rewriting A at most three times
  rewrite 3 A or rewrite 3!A: rewriting A exact 3 times
  
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From CoqExt Require Export SetoidListListExt.
Require Export Coq.Vectors.Fin.
Require Export Coq.Vectors.Vector.
Require Import Extraction.
Require Import Relations.
Require Import FunctionalExtensionality.
Require Import Lia.

Import ListNotations.   (* list_scope, delimiting with list *)
Export VectorNotations. (* vector_scope, delimiting with vector *)

Open Scope nat_scope.
Open Scope A_scope.
Open Scope vector_scope.
Open Scope mat_scope.

Generalizable Variable A B C Aeq Beq Ceq Aadd Aopp Amul Ainv.

(** Example shows the definition of matrix *)
Module Demo_matrix_def.

  (* The definition of vector in Coq.Vectors.Vector *)
  Inductive vec (A : Type) : nat -> Type :=
  | nil : vec A 0 
  | cons : A -> forall n : nat, vec A n -> vec A (S n).
  
  (* The definition of matrix *)
  Definition matrix (A : Type) (r c : nat) := @vec (@vec A c) r.

End Demo_matrix_def.

(** Tips: an improvement for the definition of vec. It is a bit different to 
    the definition in standard library, and a convenient attribute it have. *)
Module Demo_matrix_def_improve.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.

  (** Vectors.Vector *)
  Module Standard.

    (** Definition of vector type *)
    Inductive vec {A : Type} : nat -> Type :=
    | nil : vec 0 
    | cons : A -> forall n : nat, vec n -> vec (S n).

    (** Notations *)
    Notation "[]" := nil.
    Notation "a :: v" := (cons a v).

    (** Inductive property on two vectors *)
    Inductive Forall2 (A B : Type) (P : A -> B -> Prop)
      : forall n : nat, @vec A n -> @vec B n -> Prop :=
    | Forall2_nil : Forall2 P nil nil
    | Forall2_cons :
      forall (m : nat) (x1 : A) (x2 : B) (v1 : vec m) (v2 : vec m),
        P x1 x2 -> Forall2 P v1 v2 -> Forall2 P (x1 :: v1) (x2 :: v2).

    (** Equality of vector *)
    Definition veq {n} (v1 v2 : vec n) : Prop := Forall2 Aeq v1 v2.

    (* Tips: we cann't write out the Proper morphism of cons *)
    (* Fail Check forall n, Proper (Aeq ==> veq (n:=n) ==> veq (n:=S n)) (cons). *)
    
  End Standard.

  (** Vectors.Vector (modified) *)
  Module Modified.

    (** Definition of vector type *)
    Inductive vec {A : Type} : nat -> Type :=
    | nil : vec 0 
    | cons : forall n : nat, A -> vec n -> vec (S n).

    (** Notations *)
    Notation "[]" := nil.
    Notation "a :: v" := (cons a v).

    (** all vec 0 are same *)
    Lemma vec_0 (v : @vec A 0) : v = nil.
    Proof.
      refine (match v with nil => _ end). auto.
    Qed.

    (** vec (S n) could be decomposed, exist: x:A, v':vec n *)
    Lemma vec_S {n : nat} (v : @vec A (S n)) :
      {x & {v' | v = cons x v'}}.  (* sig T *)
    Proof.
      refine (match v with | cons x v' => _ end); eauto.
    Qed.

    (** Inductive property on two vectors *)
    Inductive Forall2 (A B : Type) (P : A -> B -> Prop)
      : forall n : nat, @vec A n -> @vec B n -> Prop :=
    | Forall2_nil : Forall2 P nil nil
    | Forall2_cons :
      forall (m : nat) (x1 : A) (x2 : B) (v1 : vec m) (v2 : vec m),
        P x1 x2 -> Forall2 P v1 v2 -> Forall2 P (x1 :: v1) (x2 :: v2).

    (** Equality of vector *)
    Definition veq {n} (v1 v2 : vec n) : Prop := Forall2 Aeq v1 v2.

    Infix "==" := veq : vector_scope.

    (* Now. we can write out the Proper morphism of cons *)
    (* Check forall n, Proper (Aeq ==> veq (n:=n) ==> veq (n:=S n)) (cons (n:=n)). *)
    
    Lemma cons_aeq_mor : forall n,
        Proper (Aeq ==> veq (n:=n) ==> veq (n:=S n)) (cons (n:=n)).
    Proof.
      unfold Proper, respectful.
      induction n; intros; constructor; auto.
    Qed.

    Global Existing Instance cons_aeq_mor.

    Goal forall n (a1 a2 : A) (v1 v2 : vec n), (a1 == a2)%A -> v1 == v2 -> a1::v1 == a2::v2.
      intros.
      Fail rewrite H.
      (* But, we still cannot rewrite. *)
      constructor; auto.
      (* In fact, constructor tactor can easily handle this job *)
    Qed.
    
  End Modified.

End Demo_matrix_def_improve.


(** * Matrix Multiplication (from CoLoR) *)
(* Module MatMultCoLoR. *)

(*   Notation fin := Fin.t. *)

(*   Notation vec := Vector.t. *)
(*   Notation vnil := Vector.nil. *)

(*   Notation vcons := Vector.cons. *)

(*   (* Notation vhd := Vector.hd. *) *)
(*   (* Notation vtl := Vector.tl. *) *)
(*   (* Notation vconst := Vector.const. *) *)

(*   Notation vnth := Vector.nth. *)
(*   (* Notation vfoldl := fold_left. *) *)
(*   (* Notation vfoldr := fold_right. *) *)
(*   (* Notation vmap := map. *) *)
(*   (* Notation vmap2 := map2. *) *)

(*   Arguments vec {A}. *)
(*   Arguments vnil {A}. *)
(*   Arguments vcons [A] _ [n] _. *)
(*   (* Arguments vhd [A n] _. *) *)
(*   (* Arguments vtl [A n] _. *) *)
(*   (* Arguments vconst [A] _ _. *) *)

(*   Section fin. *)
(* Lemma fin_0 (i : fin 0) : False. *)
(* Proof.  *)
(*   refine (match i with end).  *)
(* Qed. *)
    
(*     (** Decompose "fin (S n)" object *) *)
    (* Lemma fin_S (n : nat) (i : fin (S n)) : *)
    (*   (i = Fin.F1) + { i' | i = Fin.FS i' }. *)
    (* Proof. *)
    (*   refine (match i with | F1 => _ | FS _ => _ end); eauto. *)
    (* Qed. *)
(*   End fin. *)

(*   Section vec. *)
(*     Context {A : Type}. *)
    
(*     (** all vec 0 are same *) *)
(*     Lemma vec_0 (v : @vec A 0) : v = vnil. *)
(*     Proof. refine (match v with vnil => _ end). auto. Qed. *)

(*     (** vec (S n) could be decomposed, exist: x:A, v':vec n *) *)
(*     Lemma vec_S {n : nat} (v : @vec A (S n)) : *)
(*       {x & {v' | v = vcons x v'}}.  (* sig T *) *)
(*     Proof. refine (match v with | vcons x v' => _ end); eauto. Qed. *)

(*     Lemma veq_iff_nth : forall n (v1 v2 : @vec A n), *)
(*         (forall f1 f2 : fin n, f1 = f2 -> vnth v1 f1 = vnth v2 f2) <-> v1 = v2. *)
(*     Proof. *)
(*       induction n; intros. *)
(*       - rewrite (vec_0 v1), (vec_0 v2). split; intros; auto. subst; auto. *)
(*       - pose proof vec_S v1 as [x1 [v1' ->]]. *)
(*         pose proof vec_S v2 as [x2 [v2' ->]]. split; intros. *)
(*         + f_equal. *)
(*           * specialize (H F1 F1 eq_refl); simpl in H. auto. *)
(*           * apply IHn; intros. subst. *)
(*             specialize (H (FS f2) (FS f2) eq_refl). simpl in H. auto. *)
(*         + inv H. apply inj_pair2 in H3. subst. auto. *)
(*     Qed. *)
    
(*   End vec. *)

(*   Section mat_mul. *)
(*     Variable A : Type. *)
(*     Variable A0 A1 : A. *)
(*     Variable fopp : A -> A. *)
(*     Variable fadd fmul : A -> A -> A. *)
(*     Variable fadd_comm : forall x y, fadd x y = fadd y x. *)
(*     Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z). *)
(*     Variable fmul_comm : forall x y, fmul x y = fmul y x. *)
(*     Variable fmul_assoc : forall x y z, fmul (fmul x y) z = fmul x (fmul y z). *)
(*     Variable fadd_0_l : forall x, fadd A0 x = x. *)
(*     Variable fadd_0_r : forall x, fadd x A0 = x. *)
(*     Variable fmul_0_r : forall x, fmul x A0 = A0. *)
(*     Variable fmul_0_l : forall x, fmul A0 x = A0. *)
(*     Variable fmul_add_distl : forall x y z, *)
(*         fmul x (fadd y z) = fadd (fmul x y) (fmul x z). *)
(*     Variable fmul_add_distr : forall x y z, *)
(*         fmul (fadd x y) z = fadd (fmul x z) (fmul y z). *)
    
(*     Infix "+" := fadd. *)
(*     Infix "*" := fmul. *)

(*     Definition mat r c := @vec (@vec A c) r. *)

(*     Definition mnth {r c} (m : mat r c) fr fc := vnth (vnth m fr) fc. *)

(*     (** Build vector with a function [gen: fin n -> A] *) *)
(*     Fixpoint vmake {n} : (fin n -> A) -> vec n := *)
(*       match n with *)
(*       | O => fun _ => [] *)
(*       | S n' => fun (gen : fin (S n') -> A) => *)
(*                  (gen F1) :: (vmake (fun (fn':fin n') => gen (FS fn')))  *)
(*       end. *)

(*     (** nth element of a vector generated by vmake, equal to [gen i] *) *)
(*     Lemma vmake_nth : forall n gen (fn : fin n), nth (vmake gen) fn = gen fn. *)
(*     Proof. *)
(*       induction n; intros gen fn. *)
(*       - exfalso. apply (fin_0 fn). *)
(*       - pose proof (fin_S fn) as [-> | (fr' & ->)]; simpl; auto. rewrite IHn. auto. *)
(*     Qed. *)

(*     Definition mrow {r c} (m : mat r c) (fr : fin r) := vnth m fr. *)
    
(*     Definition mcol {r c} (m : mat r c) := *)
(*       fun fc : fin c => vmake (fun fr : fin r => nth (nth m fr) fc). *)

(*     Definition vdot {n} (v1 v2 : vec n) := fold_left fadd A0 (map2 fmul v1 v2). *)

    
(*     Lemma mat_build_spec : forall {r c}  *)
(*                              (gen : forall (fr : fin r) (fc : fin c), A),  *)
(*         { m : mat r c | forall (fr : fin r) (fc : fin c),  *)
(*             mnth m fr fc = gen fr fc }. *)
(*     Proof. *)
(*       induction r; intros c gen. *)
(*       - (* case r = 0 *) *)
(*         exists (vnil). intros. inversion fr. *)
(*       - (* case m > 0 *) *)
(*         set (gen' := fun (fr : fin r) (fc : fin c) => gen (FS fr) fc). *)
(*         destruct (IHr c gen') as [Mtl Mtl_spec]. *)
(*         set (gen_1 := fun (fc:fin c) => gen F1 fc). *)
(*         set (Mhd := vmake gen_1). *)
(*         set (Mhd_spec := vmake_nth gen_1). *)
(*         exists (vcons Mhd Mtl). *)
(*         intros fr fc. *)
(*         unfold mnth in *. *)
(*         pose proof fin_S fr as [-> | (fr' & ->)]. *)
(*         + simpl. auto. *)
(*         + simpl. rewrite Mtl_spec. auto. *)
(*     Defined. *)

(*     Definition mat_build {r c} gen : mat r c := proj1_sig (mat_build_spec gen). *)

(*     Lemma meq_iff_nth : forall r c (m1 m2 : mat r c), *)
(*         (forall (fr : fin r) (fc : fin c), mnth m1 fr fc = mnth m2 fr fc) -> m1 = m2. *)
(*     Proof. *)
(*       induction r; intros. *)
(*       - rewrite (vec_0 m1), (vec_0 m2). easy. *)
(*       - pose proof vec_S m1 as [v1 [m1' ->]]. *)
(*         pose proof vec_S m2 as [v2 [m2' ->]]. *)
(*         f_equal; auto. *)
(*         + apply eq_nth_iff. intros. subst. *)
(*           unfold mnth in H. specialize (H F1). simpl in *. auto. *)
(*         + apply IHr. intros. apply (H (FS fr)). *)
(*     Qed. *)

(*     Lemma mat_build_elem : forall r c gen (fr : fin r) (fc : fin c),  *)
(*         mnth (mat_build gen) fr fc = gen fr fc. *)
(*     Proof. *)
(*       intros. unfold mat_build. destruct (mat_build_spec gen). simpl. apply e. *)
(*     Qed. *)

(*     Lemma mat_build_nth : forall r c gen (fr : fin r) (fc : fin c), *)
(*         vnth (vnth (mat_build gen) fr) fc = gen fr fc. *)
(*     Proof. *)
(*       intros. fold (mrow (mat_build gen) fr). *)
(*       fold (mnth (mat_build gen) fr fc). *)
(*       apply mat_build_elem. *)
(*     Qed. *)
    
(*     Definition mat_transpose {r c} (m : mat r c) :=  *)
(*       mat_build (fun fr fc => mnth m fc fr). *)

(*     Lemma mat_transpose_idem : forall m n (m : mat m n), *)
(*         mat_transpose (mat_transpose m) = m. *)
(*     Proof. *)
(*       intros. apply meq_iff_nth. intros. *)
(*       unfold mat_transpose. rewrite !mat_build_elem. auto. *)
(*     Qed. *)

(*     Definition mat_mult {m n p} (L : mat m n) (R : mat n p) := *)
(*       mat_build (fun fr fc => vdot (mrow L fr) (mcol R fc)). *)
(*     Infix "<*>" := mat_mult (at level 40). *)

(*     Lemma mat_mult_elem : forall r c s (m : mat r c) (n : mat c s) *)
(*                             (fr : fin r) (fs : fin s),   *)
(*         vnth (vnth (mat_mult m n) fr) fs = vdot (mrow m fr) (mcol n fs). *)
(*     Proof. intros. unfold mat_mult. rewrite ?mat_build_nth. auto. Qed. *)

(*     Lemma mat_mult_spec : forall r c s (m : mat r c) (n : mat c s) *)
(*                             (fr : fin r) (fs : fin s), *)
(*         mnth (mat_mult m n) fr fs =  vdot (mrow m fr) (mcol n fs). *)
(*     Proof. *)
(*       intros. unfold mnth,mcol,mrow. *)
(*       rewrite mat_mult_elem. unfold mrow, mcol. auto. *)
(*     Qed. *)
    
(*     Lemma mat_mult_row : forall r c s (m : mat r c) (n : mat c s) (fr : fin r), *)
(*         mrow (m <*> n) fr = vmake (fun fc => vdot (mrow m fr) (mcol n fc)). *)
(*     Proof. *)
(*       intros. *)
(*       apply veq_iff_nth. intros ? fp ->. *)
(*       unfold mrow, mcol. rewrite vmake_nth. *)
(*       rewrite mat_mult_elem. auto. *)
(*     Qed. *)

(*     Lemma mat_mult_col : forall r c s (m : mat r c) (n : mat c s) (fs : fin s), *)
(*         mcol (m <*> n) fs = *)
(*           vmake (fun fc => vdot (mrow m fc) (mcol n fs)). *)
(*     Proof. *)
(*       intros. *)
(*       apply veq_iff_nth. intros ? fm ->. *)
(*       unfold mrow, mcol. rewrite ?vmake_nth. *)
(*       rewrite mat_mult_elem. auto. *)
(*     Qed. *)

(*     Lemma mat_mult_assoc : forall r c s t (m : mat r c) (n : mat c s) (p : mat s t), *)
(*         m <*> (n <*> p) = (m <*> n) <*> p. *)
(*     Proof. *)
(*       intros. apply meq_iff_nth. intros. unfold mnth. *)
(*       rewrite !mat_mult_elem, mat_mult_row, mat_mult_col. *)
(*       (* apply vdot_vec_mat_vec_assoc; auto. *) *)
(*       Abort. *)
    
(*   End mat_mul. *)

(* End MatMultCoLoR. *)




(** * Additional properties for operations of Vector.t *)

(** ** Global Notations for familiar naming style *)

Notation fin := Fin.t.

Notation vec := Vector.t.
Notation vnil := Vector.nil.

Notation vcons := Vector.cons.

Notation vhd := Vector.hd.
Notation vtl := Vector.tl.
Notation vconst := Vector.const.

Notation vnth := Vector.nth.
Notation vfoldl := fold_left.
Notation vfoldr := fold_right.
Notation vmap := map.
Notation vmap2 := map2.

Arguments vec {A}.
Arguments vnil {A}.
Arguments vcons [A] _ [n] _.
Arguments vhd [A n] _.
Arguments vtl [A n] _.
Arguments vconst [A] _ _.

(** ** fin decompose *)
Section fin_decompose.

  (** There isn't fin 0 *)
  Lemma fin_0 (i : fin 0) : False.
  Proof. 
    (* refine tactic:
       1. behaves like exact,
       2. the user can leave some holes in the term.
       3. generate as many subgoals as there are remaining holes in the
          elaborated term.
    *)
    refine (match i with end). 
  Qed.
  
  (** Decompose "fin (S n)" object *)
  Lemma fin_S (n : nat) (i : fin (S n)) :
    (i = Fin.F1) + { i' | i = Fin.FS i' }.
  Proof.
    (* eauto tactic:
       1. generalizes auto.
       2. it internally use a tactic close to [simple eapply]
    *)
    refine (match i with 
            | F1 => _
            | FS _ => _ 
            end); eauto.
  Qed.
  
  (** Construct a "fin n" object which equal to i *)

  Fixpoint fin_gen (n i : nat) : option (fin n) :=
    match n,i with
    | O, _ => @None (Fin.t 0)
    | S n', O => Some F1
    | S n', S i' => 
      let a := fin_gen n' i' in
        match a with
        | None => None
        | Some x => Some (FS x)
        end
    end.

  Lemma fin_gen_S : forall n i f,
      fin_gen n i = Some f -> fin_gen (S n) (S i) = Some (FS f).
  Proof.
    intros. simpl. rewrite H. auto.
  Qed.

  Lemma fin_gen_exist : forall (n ni : nat), ni < n -> exists fi, fin_gen n ni = Some fi.
  Proof.
    induction n. easy.
    - induction ni; intros.
      + simpl. exists F1. auto.
      + assert (ni < n) by lia. apply IHn in H0. destruct H0.
        exists (FS x). simpl. destruct (fin_gen n ni).
        * inv H0. auto.
        * inv H0.
  Qed.
  
End fin_decompose.

Arguments fin_S {n}.

(** Simplify the fin expression *)
Ltac finsimp :=
  repeat match goal with
  | f : fin 0 |- _ => exfalso; apply (fin_0 f)
  | f : fin (S ?n) |- _ => pose proof fin_S f as [-> | (fi & ->)]
  end.

(** ** vec decompose *)
Section vec_decompose.

  Context {A:Type}.
  (* Context `{Equiv_Aeq:Equivalence A Aeq}. *)
  (* Infix "==" := Aeq : A_scope. *)
  (* Print vec. *)
  (* Print t. ? *)
  
  (** all vec 0 are same *)
  Lemma vec_0 (v : @vec A 0) : v = vnil.
  Proof.
    refine (match v with vnil => _ end). auto.
  Qed.

  (** vec (S n) could be decomposed, exist: x:A, v':vec n *)
  Lemma vec_S {n : nat} (v : @vec A (S n)) :
    {x & {v' | v = vcons x v'}}.  (* sig T *)
  Proof.
    refine (match v with
            | vcons x v' =>  _
            end); eauto.
  Qed.
 
End vec_decompose.

Arguments vec_0 {A}.
Arguments vec_S {A n}.


(** Simplify the vec expression *)
Ltac vsimp :=
  repeat match goal with
  | v : vec 0 |- _ => rewrite (vec_0 v) in *
  | v : vec (S ?n) |- _ => pose proof vec_S v as [? [? ->]]
  end.


(** ** Forall2 *)
Global Hint Constructors Forall2 : core.
Section Forall2.

  Lemma Forall2_cons_iff : forall {A} {P:relation A} {n} (a1 a2 : A) (v1 v2 : @vec A n),
      Forall2 P (a1 :: v1) (a2 :: v2) <-> (P a1 a2 /\ Forall2 P v1 v2).
  Proof.
    intros. split; intros.
    - inv H. apply inj_pair2 in H2,H5. subst. auto.
    - inv H. constructor; auto.  
  Qed.

End Forall2.


(** ** Equality of vec *)
Section veq.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.

  Definition veq {n} (v1 v2 : @vec A n) : Prop :=
    Forall2 Aeq v1 v2.
  Infix "==" := (veq) : vector_scope.

  (** veq is an equivalence relation *)

  Lemma veq_refl : forall n, Reflexive (veq (n:=n)).
  Proof.
    unfold Reflexive.
    intros. cbv. induction x; constructor; auto. easy.
  Qed.

  Lemma veq_sym : forall n, Symmetric (veq (n:=n)).
  Proof.
    unfold Symmetric.
    unfold veq in *. induction n; intros; vsimp. easy.
    apply Forall2_cons_iff in H as []. constructor; auto. easy.
  Qed. 

  Lemma veq_trans : forall n, Transitive (veq (n:=n)).
  Proof.
    unfold Transitive.
    unfold veq in *. induction n; intros; vsimp. easy.
    apply Forall2_cons_iff in H as [], H0 as [].
    apply Forall2_cons_iff. split.
    rewrite H; auto. apply IHn with x3; auto.
  Qed.

  (** veq is equivalence relation *)
  Lemma Equiv_veq : forall {n}, Equivalence (veq (n:=n)).
  Proof.
    constructor. apply veq_refl. apply veq_sym. apply veq_trans.
  Qed.

  Global Existing Instance Equiv_veq.

  
  (** Equality is decidable *)
  Context {Dec_Aeq : Decidable Aeq}.
  Lemma veq_dec : forall {n} (v1 v2 : @vec A n), {v1 == v2} + {~(v1 == v2)}.
  Proof.
    unfold veq in *. induction n; intros; vsimp. auto.
    destruct (decidable x1 x), (IHn x2 x0); auto.
    - right. intro. apply Forall2_cons_iff in H as []. easy.
    - right. intro. apply Forall2_cons_iff in H as []. easy.
    - right. intro. apply Forall2_cons_iff in H as []. easy.
  Qed.

End veq.

(* Arguments veq {A} {n}. *)
Arguments veq_dec {A} _ _ {n}.



(** ** vec0 *)
Section vec0.

  Context {A:Type} (A0:A).

  Definition vec0 n : vec n := vconst A0 n.

End vec0.
(* Hint Unfold vec0 : core. *)


(** ** Cons *)
Section vcons.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  (** Method 1 : only could solving the form of "vcons a v1 == vcons a v2" *)
  (* Lemma vcons_aeq_mor : forall (a : A) (n : nat), *)
  (*     Proper (veq (Aeq:=Aeq) ==> veq (Aeq:=Aeq)) (vcons a (n:=n)). *)
  (* Proof. *)
  (*   unfold Proper, respectful. *)
  (*   intros a n. induction n; intros; vsimp. easy. *)
  (*   constructor; auto. easy. *)
  (* Qed. *)

  (** Method 2: Though method 1 is useful, but it still cannot rewrite now.
      We can apply this lemma.
      By the way, "apply cons_aeq_mor" couled be instead with "constructor".
      Another purpose of this lemma, we can deal with hypothese, meanwhile,
      the "constructor" tactic can not do it. *)
  Lemma vcons_aeq_mor : forall (n:nat),
      Proper (Aeq ==> veq (Aeq:=Aeq) (n:=n) ==> veq (Aeq:=Aeq) (n:=S n))
        (fun (a:A) (v:vec n) => vcons a v).
  Proof.
    unfold Proper, respectful.
    intros n x y H v1 v2. revert v1 v2.
    induction n; intros; vsimp; constructor; auto.
  Qed.

  (** This is not useful yet, even we declare the instance. *)
  Global Existing Instance vcons_aeq_mor.

  (** a1 == a2 -> a1 :: v == a2 :: v *)
  Lemma vcons_aeq_mor_part1 : forall (n : nat) (v : vec n),
      Proper (Aeq ==> veq (Aeq:=Aeq)(n:=S n)) (fun a => vcons a v).
  Proof.
    unfold Proper, respectful.
    intros. unfold veq in *. constructor; auto. f_equiv.
  Qed.

  (** This is not useful yet. *)
  Global Existing Instance vcons_aeq_mor_part1.

  (** v1 == v2 -> a :: v1 == a :: v2 *)
  Lemma vcons_aeq_mor_part2 : forall (a : A) (n : nat),
      Proper (veq (Aeq:=Aeq)(n:=n) ==> veq (Aeq:=Aeq)(n:=S n)) (vcons a (n:=n)).
  Proof.
    unfold Proper, respectful.
    intros. unfold veq in *. constructor; auto. easy.
  Qed.

  Global Existing Instance vcons_aeq_mor_part2.

  (** Equality of cons, iff both parts are equal *)
  Lemma vcons_eq_iff : forall n (a1 a2 : A) (v1 v2 : @vec A n),
      a1 :: v1 == a2 :: v2 <-> (a1 == a2)%A /\ v1 == v2.
  Proof.
    intros. split; intros H.
    - inv H. apply inj_pair2 in H2,H5. subst. easy.
    - constructor; easy.
  Qed.

  (** Inequality of cons, iff at least one parts are not equal *)
  Lemma vcons_neq_iff : forall n (a1 a2 : A) (v1 v2 : @vec A n),
      ~(a1 :: v1 == a2 :: v2) <-> (~(a1 == a2)%A \/ ~(v1 == v2)).
  Proof.
    intros n. destruct n; intros; split; intros; vsimp;
      rewrite ?vcons_eq_iff in *.
    - apply not_and_or; auto.
    - apply or_not_and; auto.
    - apply not_and_or in H. destruct H; auto.
    - apply or_not_and. destruct H; auto.
  Qed.

End vcons.

(** Properties for vhd and vtl *)
Section vhd_vtl.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  (** hd is a proper morphism *)
  Lemma vhd_aeq_mor : forall n, Proper (veq (Aeq:=Aeq)(n:=S n) ==> Aeq) (vhd (n:=n)).
  Proof.
    unfold Proper, respectful.
    induction n; intros; vsimp; simpl; apply vcons_eq_iff in H as []; auto.
  Qed.
  Global Existing Instance vhd_aeq_mor.

  (** tl is a proper morphism *)
  Lemma vtl_aeq_mor : forall n,
      Proper (veq (Aeq:=Aeq)(n:=S n) ==> veq (Aeq:=Aeq)(n:=n)) (vtl (n:=n)).
  Proof.
    unfold Proper, respectful.
    induction n; intros; vsimp; simpl; apply vcons_eq_iff in H as []; auto.
  Qed.
  Global Existing Instance vtl_aeq_mor.

End vhd_vtl.


(** ** Get n-th element with index of fin type *)
Section vnth.

  Context `{Equiv_Aeq : Equivalence A Aeq} {A0:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  Lemma vnth_aeq_mor : forall n, Proper (veq (Aeq:=Aeq) (n:=n) ==> eq ==> Aeq) vnth.
  Proof.
    unfold Proper, respectful.
    induction n; intros v1 v2 H fi fj; vsimp. finsimp.
    apply vcons_eq_iff in H as [].
    intros. subst. finsimp; simpl; auto.
  Qed.

  Global Existing Instance vnth_aeq_mor.

  Lemma veq_iff_nth : forall {n} (v1 v2 : @vec A n),
      v1 == v2 <->
      (forall f1 f2 : fin n, f1 = f2 -> (vnth v1 f1 == vnth v2 f2)%A).
  Proof.
    induction n; intros; split; intros; vsimp; subst; try easy; try finsimp; simpl.
    - apply vcons_eq_iff in H as []; auto.
    - apply vcons_eq_iff in H as []; auto. apply IHn; auto.
    - constructor.
      + specialize (H F1 F1 eq_refl). simpl in H. auto.
      + apply IHn. intros. subst. specialize (H (FS f2) (FS f2) eq_refl).
        simpl in H. auto.
  Qed. 

  Lemma vnth_head : forall n (v : @vec A (S n)), (vhd v == vnth v F1)%A.
  Proof.
    intros. vsimp. simpl. easy.
  Qed.

  Lemma vnth_tail : forall n (v : @vec A (S n)) (fn : fin n),
    (vnth (vtl v) fn == vnth v (FS fn))%A.
  Proof.
    intros. vsimp. simpl. easy.
  Qed.
  
  Lemma vnth_nil : forall (fn : fin 0), vnth vnil fn -> False.
  Proof.
    intros. finsimp.
  Qed.

End vnth.


(** Get i-th element with index of nat type *)
Section vnthNat.

  Context `{Equiv_Aeq : Equivalence A Aeq} {A0:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  (** Get i-th element of a vector *)  
  Definition vnthNat {n} (v : vec n) (i : nat) :=
    match (fin_gen n i) with
    | Some fi => vnth v fi
    | _ => A0
    end.

  (** vnthNat is a proper morphism *)
  Lemma vnthNat_aeq_mor : forall (n:nat),
      Proper (veq (Aeq:=Aeq)(n:=n) ==> eq ==> Aeq) vnthNat.
  Proof.
    unfold Proper, respectful, vnthNat.
    induction n; intros; subst. easy.
    destruct (fin_gen (S n) y0); try easy.
    rewrite H. easy.
  Qed.
  
  Lemma vnthNat_cons : forall n a (v : vec n) i,
      (vnthNat (vcons a v) (S i) == vnthNat v i)%A.
  Proof.
    unfold vnthNat.
    induction n; intros; vsimp; simpl. easy.
    destruct i; simpl. easy.
    destruct (fin_gen n i); try easy.
  Qed.
  
  (** veq and vnthNat should satisfy this constraint *)
  Lemma veq_iff_vnthNat : forall {n : nat} (v1 v2 : vec n),
      v1 == v2 <-> (forall i, i < n -> (vnthNat v1 i == vnthNat v2 i)%A).
  Proof.
    induction n; intros; split; intros; try lia; vsimp; try easy.
    - apply vcons_eq_iff in H as [].
      apply vnthNat_aeq_mor; auto. apply vcons_eq_iff; split; auto.
    - apply vcons_eq_iff; split.
      + specialize (H 0 (Nat.lt_0_succ n)).
        unfold vnthNat in H; simpl in H. easy.
      + apply IHn. intros.
        assert (S i < S n) by lia.
        apply H in H1. rewrite ?vnthNat_cons in H1. auto.
  Qed.

  (** vnthNat is equivalent to vnth *)
  Lemma vnthNat_eq_vnth : forall {n : nat} (v1 v2 : vec n),
      (forall i : nat, i < n -> (vnthNat v1 i == vnthNat v2 i)%A) <->
        (forall (fi : fin n), (vnth v1 fi == vnth v2 fi)%A).
  Proof.
    intros. split; intros.
    - apply veq_iff_nth; auto. apply veq_iff_vnthNat. auto.
    - apply veq_iff_vnthNat; auto. apply veq_iff_nth.
      intros. subst. auto.
  Qed.

End vnthNat.

(** ** vmap *)
Section vmap.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.
  
  Lemma vmap_cons : forall n a (v : vec n) (f : A -> A), 
    vmap f (a :: v) == (f a) :: (vmap f v).
  Proof.
    intros. simpl. easy.
  Qed.

End vmap.


(** ** vmap2 *)
Section vmap2.
  
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  Lemma vmap2_cons : forall n a1 a2 (v1 v2 : vec n) (f : A -> A -> A), 
    vmap2 f (a1 :: v1) (a2 :: v2) == (f a1 a2) :: (vmap2 f v1 v2).
  Proof.
    intros. simpl. easy.
  Qed.

  (** vmap2 is respect veq *)
  Context (Aadd : A -> A -> A).
  Context {AaddProper : Proper (Aeq ==> Aeq ==> Aeq) Aadd}.
  Lemma vmap2_aeq_mor : forall n,
      Proper (veq (Aeq:=Aeq) ==> veq (Aeq:=Aeq) ==> veq (Aeq:=Aeq)) (vmap2 Aadd (n:=n)).
  Proof.
    unfold Proper, respectful.
    induction n; intros v1 v2 H12 v3 v4 H34; vsimp. easy.
    simpl. rewrite vcons_eq_iff in *. destruct H12,H34. split.
    - apply AaddProper; auto.
    - apply IHn; auto.
  Qed.

  Global Existing Instance vmap2_aeq_mor.

  Context {Comm_Aadd : Commutative Aadd Aeq}.
  Lemma vmap2_comm : forall n (v1 v2 : @vec A n),
    vmap2 Aadd v1 v2 == vmap2 Aadd v2 v1.
  Proof.
    induction n; intros; simpl; vsimp. easy.
    simpl. rewrite vcons_eq_iff; split; auto. apply commutative.
  Qed.
  
End vmap2.


(** ** Build vector with a function *)
Section vmake.

  Context `{Equiv_Aeq : Equivalence A Aeq} {A0:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  (** Build vector with a function [gen: fin n -> A] *)
  Fixpoint vmake {n} : (fin n -> A) -> vec n :=
    match n with
    | O => fun _ => []
    | S n' => fun (gen : fin (S n') -> A) =>
       (gen F1) :: (vmake (fun (fn':fin n') => gen (FS fn'))) 
    end.
    
  (** nth element of a vector generated by vmake, equal to [gen i] *)
  Lemma vmake_nth : forall n gen (fn : fin n), (nth (vmake gen) fn == gen fn)%A.
  Proof.
    induction n; intros gen fn.
    - finsimp.
    - finsimp; simpl. easy. apply IHn.
  Qed.
  
  (** head element of a vector generated by vmake, equal to [gen F1] *)
  Lemma vmake_head : forall n (gen : fin (S n) -> A) ,
    (vhd (vmake gen) == gen F1)%A.
  Proof.
    intros. rewrite vnth_head, vmake_nth. easy.
  Qed.
  
  (** tail element of a vector generated by vmake, equal to a vector with 
    generated by vmake with the next position. eg, tail [1;2;3;4] = [2;3;4] *)
  Lemma vmake_tail n (gen : fin (S n) -> A) :
    vtl (vmake gen) == vmake (fun (fn : fin n) => gen (FS fn)).
  Proof.
    apply veq_iff_nth. intros; subst. rewrite vnth_tail, !vmake_nth. easy.
  Qed.

  (** A vector build with A0 equal to vec0 *)
  Lemma vmake_0_eq_vec0 : forall n, vmake (fun _ : fin n => A0) == vec0 A0 n.
  Proof.
    intros. apply veq_iff_nth. intros ? p ->. rewrite vmake_nth, const_nth. easy.
  Qed.

  (** vmap2 f {gen} v = vmake {f (gen[i]) v[i]} *)
  Lemma vmap2_vmake_l : forall (f : A -> A -> A) n gen (v : vec n),
    vmap2 f (vmake (fun fn : fin n => gen fn)) v == 
    vmake (fun fn : fin n => f (gen fn) (vnth v fn)).
  Proof.
    intros f n. induction n; intros; vsimp; simpl. easy.
    apply vcons_eq_iff; split; auto. easy.
  Qed.

  (* vmap2 f v {gen} = vmake {f v[i] (gen[i])} *)
  Lemma vmap2_vmake_r : forall (f : A -> A -> A) n gen (v : vec n),
    vmap2 f v (vmake (fun fn : fin n => gen fn)) == 
    vmake (fun fn : fin n => f (vnth v fn) (gen fn)).
  Proof.
    intros f n. induction n; intros; vsimp; simpl. easy.
    apply vcons_eq_iff; split; auto. easy.
  Qed.

End vmake.

Arguments vmake {A n}.
Arguments vmake_nth {A Aeq} _ {n}.
(* Arguments vmake_0_eq_vconst_0 {A}. *)
Arguments vmake_0_eq_vec0 {A}.


Section vmake_vec_vec.
  
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := (veq (Aeq:=veq (Aeq:=Aeq))) : vector_scope.

  (** If a matrix have r rows and its elements are vnil, then it is equal to vec0 *)
  Lemma vmake_nil_eq_vec0 : forall r, 
      vmake (fun _ : fin r => @vnil A) == vec0 vnil r.
  Proof.
    intros. 
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth.
    rewrite const_nth; easy. apply Equiv_veq.
  Qed.

End vmake_vec_vec.

(* Arguments vmake_nil_eq_vconstnil {A}. *)
Arguments vmake_nil_eq_vec0 {A}.


(** Extensional propertity of vmake *)
Section vmake_ext.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  (** vmake extensional equality *)
  Lemma vmake_ext : forall n (f g : fin n -> A),
      (forall (fi : fin n), (f fi == g fi)%A) -> (vmake f == vmake g)%vector.
  Proof.
    induction n; simpl; intros. easy.
    apply vcons_eq_iff; split; auto.
  Qed.

End vmake_ext.


(** ** Properties of vfold on element with basic structure *)

Section vfold_props_basic.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  (** extensional equality of vfoldl *)
  Lemma vfoldl_ext : forall {n} f1 f2 (a1 a2 : A) (v1 v2 : vec n),
      (forall (a1 a2 b1 b2 : A), (a1 == a2 -> b1 == b2 -> f1 a1 b1 == f2 a2 b2)%A) ->
      (a1 == a2)%A ->
      (v1 == v2) ->
      (vfoldl f1 a1 v1 == vfoldl f2 a2 v2)%A.
  Proof.
    induction n; intros; vsimp; simpl in *; auto.
    apply vcons_eq_iff in H1 as []; auto.
  Qed.

  (** extensional equality of vfoldl, with same function *)
  Lemma vfoldl_ext_samef : forall {n} f (a1 a2 : A) (v1 v2 : vec n),
      (Proper (Aeq ==> Aeq ==> Aeq) f) ->
      (a1 == a2)%A ->
      (v1 == v2) ->
      (vfoldl f a1 v1 == vfoldl f a2 v2)%A.
  Proof. intros. apply vfoldl_ext; try easy. intros. apply H; auto. Qed.

  (** extensional equality of vfoldr *)
  Lemma vfoldr_ext : forall {n} f1 f2 (a1 a2 : A) (v1 v2 : vec n),
      (forall (a1 a2 b1 b2 : A), (a1 == a2 -> b1 == b2 -> f1 a1 b1 == f2 a2 b2)%A) ->
      (a1 == a2)%A ->
      v1 == v2 ->
      (vfoldr f1 v1 a1 == vfoldr f2 v2 a2)%A.
  Proof.
    induction n; intros; vsimp; simpl in *; auto.
    apply vcons_eq_iff in H1 as []; auto.
  Qed.

  (** extensional equality of vfoldr, with same function *)
  Lemma vfoldr_ext_samef : forall {n} f (a1 a2 : A) (v1 v2 : vec n),
      (Proper (Aeq ==> Aeq ==> Aeq) f) ->
      (a1 == a2)%A ->
      v1 == v2 ->
      (vfoldr f v1 a1 == vfoldr f v2 a2)%A.
  Proof.
    intros. apply vfoldr_ext; try easy. intros. apply H; auto.
  Qed.

End vfold_props_basic.


(** ** Properties of vfold on element with more strict structure. *)
Section vfold_props_advanced.

  (** *** Properties on Monoid *)
  Context `{M:Monoid}.
  Infix "+" := Aadd : A_scope.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  (** vfoldl (a + b) v = a + (vfoldl b v) *)
  Lemma vfoldl_Aadd : forall n (a b : A) (v : @vec A n),
    (vfoldl Aadd (a + b) v == a + (vfoldl Aadd b v))%A.
  Proof.
    induction n; intros; vsimp; simpl in *. easy.
    rewrite IHn. rewrite associative. f_equiv. easy.
  Qed.

  (** vfoldl a vec0 = a *)
  Lemma vfoldl_vec0 : forall n (a : A), (vfoldl Aadd a (vec0 A0 n) == a)%A.
  Proof.
    intros. induction n; simpl. easy.
    rewrite vfoldl_ext_samef with (a2:=a) (v2:=vec0 A0 n); try easy.
    apply monoidAaddProper. monoid_simpl.
  Qed.

  (** *** Properties on AMonoid *)
  Context `{AM:AMonoid A Aadd A0 Aeq}.
  (* Context `{AG:AGroup}. *)
  (* Variable A : Type. *)
  (* Variable A0 : A. *)
  (* Variable fadd : A -> A -> A. *)
  (* Variable fadd_comm : forall x y, fadd x y = fadd y x. *)
  (* Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z). *)
  (* Variable fadd_0_r : forall x, fadd x A0 = x. *)

  (** vfoldr v (a + b) v = a + (vfoldr b v) *)
  Lemma vfoldr_Aadd : forall n (a b : A) (v : @vec A n),
    (vfoldr Aadd v (a + b) == a + (vfoldr Aadd v b))%A.
  Proof.
    induction n; intros; vsimp. simpl. easy.
    simpl. rewrite <- IHn.
    rewrite vfoldr_ext_samef with (a2:=a+(x+b)) (v2:=x0); try easy.
    - rewrite ?IHn. easy.
    - apply monoidAaddProper.
    - rewrite <- ?associative. f_equiv. apply commutative. 
  Qed.

  (** vfoldr vec0 a = a *)
  Lemma vfoldr_vec0 : forall n (a : A), (vfoldr Aadd (vec0 A0 n) a == a)%A.
  Proof.
    intros. induction n; simpl. easy. monoid_simpl.
  Qed.
  
  (** foldl a0 v = foldr a0 v*)
  Lemma vfoldl_eq_vfoldr : forall {n} (a : A) (v : @vec A n), 
    (vfoldl Aadd a v == vfoldr Aadd v a)%A.
  Proof.
    induction n; intros; vsimp; simpl in *. easy.
    rewrite vfoldl_ext with (f2:=Aadd) (a2:=x+a) (v2:=x0); try easy.
    - rewrite vfoldl_Aadd. f_equiv; auto.
    - intros. rewrite H,H0; easy.
    - apply commutative. 
  Qed.
  
End vfold_props_advanced.

Notation vfold := vfoldl.
Arguments vfoldl_Aadd {A}.


(** get / set an element of a vector *)
Section vget_vset.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0:A}.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  Fixpoint vget {n} (v:vec n) (i:nat) : A :=
    match v, i with
    | [], _ => A0
    | a :: v', 0 => a
    | a :: v', S i' => vget v' i'
    end.

  (** Note, this is not tail recursion *)
  Fixpoint vset {n} (v:vec n) (i:nat) (x:A) : vec n :=
    match v, i with
    | [], _ => []
    | a :: v', 0 => x :: v'
    | a :: v', S i' => a :: (vset v' i' x)
    end.

End vget_vset.


(** ** Arithmatic of vector *)

(** Addition, Opposition, Subtraction of vectors *)
Section varith.

  (* Variable A : Type. *)
  (* Variable A0 A1 : A. *)
  (* Variable fopp : A -> A. *)
  (* Variable fadd : A -> A -> A. *)
  (* Variable fadd_comm : forall x y, fadd x y = fadd y x. *)
  (* Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z). *)
  (* Variable fadd_0_l : forall x, fadd A0 x = x. *)
  (* Variable fadd_0_r : forall x, fadd x A0 = x. *)

  Context `{G:AGroup}.
  Infix "+" := Aadd : A_scope.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  (** *** Properties of vfold *)
  
  (** vfold (a + b) v = a + (fold b v) *)
  Lemma vfold_Aadd : forall n a b (v : @vec A n),
    (vfold Aadd (a + b) v == a + (vfold Aadd b v))%A.
  Proof.
    apply vfoldl_Aadd with (A0:=A0). apply groupMonoid.
  Qed.
  
  (** vfold (a + b) v = b + (fold a v) *)
  Lemma vfold_Aadd_rev : forall n a b (v : @vec A n),
    (vfold Aadd (a + b) v == b + (vfold Aadd a v))%A.
  Proof.
    intros. rewrite vfoldl_ext with (f2:=Aadd) (a2:=(b+a)%A) (v2:=v);
      try easy; try apply commutative.
    apply vfold_Aadd.
    intros. f_equiv; auto.
  Qed.
  
  (** vfold a (b::v) = vfold (a + b) v *)
  Lemma vfold_cons : forall n (a b : A) (v : @vec A n),
    (vfold Aadd a (b :: v) == vfold Aadd (a + b) v)%A.
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** vfold a (b::v) = a + (vfold b v) *)
  Lemma vfold_cons_eq_add : forall n (a b : A) (v : @vec A n),
    (vfold Aadd a (b :: v) == a + (vfold Aadd b v))%A.
  Proof.
    intros. simpl. rewrite vfold_Aadd. easy.
  Qed.
  
  (* vfold a (b::v) = b + (vfold a v) *)
  Lemma vfold_cons_eq_add_rev : forall n (a b : A) (v : @vec A n),
    (vfold Aadd a (b :: v) == b + (vfold Aadd a v))%A.
  Proof.
    intros. simpl. rewrite vfold_Aadd_rev. easy.
  Qed.

  (** vfold a vec0 = a *)
  Lemma vfold_vec0 : forall n (a : A), (vfold Aadd a (vec0 A0 n) == a)%A.
  Proof.
    apply vfoldl_vec0.
  Qed.

  (** vfold (a + b) (vmap2 f v1 v2) = f (vfold a v1) (vfold b v2) *)
  Lemma vfold_Aadd_vmap2 : forall n a b (v1 v2 : @vec A n),
    (vfold Aadd (a + b) (vmap2 Aadd v1 v2) == (vfold Aadd a v1) + (vfold Aadd b v2))%A.
  Proof.
    induction n; intros; vsimp; simpl. easy.
    rewrite <- IHn. apply vfoldl_ext; try easy.
    intros; f_equiv; easy.
    rewrite ?associative; f_equiv.
    rewrite <- ?associative; f_equiv. apply commutative.
  Qed.
  
  (** vfold a (vmap2 f v1 v2) = f (vfold a v1) (vfold A0 v2) *)
  Lemma vfold_vmap2_eq_left : forall n (a : A) (v1 v2 : @vec A n),
    (vfold Aadd a (vmap2 Aadd v1 v2) == (vfold Aadd a v1) + (vfold Aadd A0 v2))%A.
  Proof.
    intros. rewrite <- vfold_Aadd_vmap2. apply vfoldl_ext; try easy.
    intros; f_equiv; easy. monoid_simpl.
  Qed.

  (** vfold a (vmap2 f v1 v2) = f (vfold A0 v1) (vfold a v2) *)
  Lemma vfold_vmap2_eq_right : forall n (a : A) (v1 v2 : @vec A n),
    (vfold Aadd a (vmap2 Aadd v1 v2) == (vfold Aadd A0 v1) + (vfold Aadd a v2))%A.
  Proof.
    intros. rewrite <- vfold_Aadd_vmap2. apply vfoldl_ext; try easy.
    intros; f_equiv; easy. monoid_simpl.
  Qed.

  (** *** Addition, opposition, subtraction of vector *)
  
  (** Addition of vectors *)
  Definition vadd {n} (v1 v2 : vec n) := map2 Aadd v1 v2.
  Infix "+" := vadd : vector_scope.

  (** vadd is proper morphism *)
  Lemma vadd_aeq_mor : forall n,
      let r := veq (Aeq:=Aeq) (n:=n) in Proper (r ==> r ==> r) vadd.
  Proof.
    unfold Proper, respectful.
    induction n; intros v1 v2 H12 v3 v4 H34; vsimp; simpl. easy.
    apply vcons_eq_iff in H12 as [], H34 as [].
    apply vcons_eq_iff; split; auto. rewrite H,H1. easy.
  Qed.

  Global Existing Instance vadd_aeq_mor.

  (** Opposition of vector *)
  Definition vopp {n} (v : vec n) := map Aopp v.
  Notation "- v" := (vopp v) : vector_scope.
  
  (** vopp is proper morphism *)
  Lemma vopp_aeq_mor : forall n,
      let r := veq (Aeq:=Aeq) (n:=n) in Proper (r ==> r) vopp.
  Proof.
    unfold Proper, respectful.
    induction n; intros v1 v2 H12; vsimp; simpl. easy.
    apply vcons_eq_iff in H12 as [].
    apply vcons_eq_iff; split; auto. rewrite H. easy.
  Qed.

  Global Existing Instance vopp_aeq_mor.

  
  (** v1 + v2 = v2 + v1 *)
  Lemma vadd_comm (n : nat) (v1 v2 : vec n) : v1 + v2 == v2 + v1.
  Proof.
    unfold vadd.
    apply veq_iff_nth; intros; subst.
    (* nth_map2: vnth (map2 f v1 v2) p1 = f (nth v1 p) (nth v2 p) *)
    rewrite ?nth_map2 with (p2:=f2) (p3:=f2); auto. apply commutative.
  Qed.
  
  (** (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma vadd_assoc (n : nat) (v1 v2 v3 : vec n) : (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof.
    unfold vadd.
    apply veq_iff_nth; intros; subst.
    rewrite ?nth_map2 with (p2:=f2) (p3:=f2); auto.
    rewrite associative. easy.
  Qed.
  
  (* (** [] + v = v *) *)
  (* Lemma vadd_nil_l : forall (v : vec 0), vnil + v == v. *)
  (* Proof. intros. rewrite (vec_0 v). simpl. easy. Qed. *)

  (* (** v + [] = v *) *)
  (* Lemma vadd_nil_r : forall (v : vec 0), v + vnil == v. *)
  (* Proof. intros. rewrite (vec_0 v). simpl. easy. Qed. *)
  
  (** vec0 + v = v *)
  Lemma vadd_vec0_l : forall {n} (v : vec n), (vec0 A0 n) + v == v.
  Proof.
    induction n; intros; vsimp; simpl. easy.
    apply vcons_eq_iff; split; auto. monoid_simpl.
  Qed.

  (** v + vec0 = v *)
  Lemma vadd_vec0_r : forall {n} (v : vec n), v + (vec0 A0 n) == v.
  Proof.
    induction n; intros; vsimp; simpl. easy.
    apply vcons_eq_iff; split; auto. monoid_simpl.
  Qed.

  (** (-v) + v = vec0 *)
  Lemma vadd_vopp_l : forall {n} (v : vec n), (-v) + v == vec0 A0 n.
  Proof.
    induction n; intros; vsimp; simpl. easy.
    apply vcons_eq_iff; split; auto. group_simpl.
  Qed.

  (** v + (-v) = vec0 *)
  Lemma vadd_vopp_r : forall {n} (v : vec n), v + (-v) == vec0 A0 n.
  Proof.
    induction n; intros; vsimp; simpl. easy.
    apply vcons_eq_iff; split; auto. group_simpl.
  Qed.
  
  
  (** (v1 + v2)[n] = v1[n] + v2[n] *)
  Lemma vadd_nth : forall n (v1 v2 : @vec A n) (fn : fin n),
    (vnth (v1 + v2)%vector fn == (vnth v1 fn) + (vnth v2 fn))%A.
  Proof. 
    intros. unfold vadd.
    rewrite nth_map2 with (p2:=fn) (p3:=fn); auto. easy.
  Qed.
  
  (** (vmake gen1) + (vmake gen2) = vmake (gen1 + gen2) *)
  Lemma vadd_vmake_vmake : forall n gen1 gen2,
    (vmake gen1) + (vmake gen2) ==
    vmake (fun fn : fin n => ((gen1 fn) + (gen2 fn))%A).
  Proof.
    induction n; intros; simpl. easy. apply vcons_eq_iff; split; auto. easy.
  Qed.

  (** vfold (a + b) (v1 + v2) = (vfold a v1) + (vfold b v2) *)
  Lemma vfold_vadd : forall n (a b : A) (v1 v2 : @vec A n),
    (vfold Aadd (a + b) (v1 + v2)%vector == (vfold Aadd a v1) + (vfold Aadd b v2))%A.
  Proof.
    induction n; intros; vsimp; simpl. easy.
    rewrite vfoldl_ext with (f2:=Aadd) (a2:=((a+x1)+(b+x))%A) (v2:=x2+x0); try easy.
    intros; f_equiv; auto.
    rewrite ?associative; f_equiv.
    rewrite <- ?associative; f_equiv. apply commutative.
  Qed.
  
End varith.

Arguments vopp {A} Aopp {n}.
Arguments vadd {A} Aadd {n}.
Arguments vfold_vec0 {A}.


(* =============================================================== *)
(** ** (vec, vadd, vopp, veq) is a AGroup *)
Section vec_AG.

  Context `{G:AGroup}.
  Infix "+" := Aadd : A_scope.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  Lemma vec_AG : forall n, @AGroup (vec n) (vadd Aadd) (vconst A0 n) (vopp Aopp)
                    (veq (Aeq:=Aeq)).
  Proof.
    induction n; repeat constructor; intros
    ; try (apply vadd_aeq_mor; easy)
    ; try (apply vopp_aeq_mor; easy)
    ; try apply Equiv_veq
    ; try (rewrite vadd_assoc; easy)
    ; try apply vadd_comm
    ; try (rewrite vadd_vec0_l; easy)
    ; try (rewrite vadd_vec0_r; easy)
    ; try (rewrite vadd_vopp_l; easy)
    ; try (rewrite vadd_vopp_r; easy)
    .
  Qed.
  
  Global Existing Instance vec_AG.

End vec_AG.


(* =============================================================== *)
(** ** sum of vector *)
Section vsum.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Context (A0:A) (Aadd : A -> A -> A). 

  Definition vsum {n} (v : @vec A n) := vfold Aadd A0 v.
  
End vsum.


(** ** Matrix Definitions *)

Section MatrixDefinition.

  Context `{Equiv_Aeq : Equivalence A Aeq} {A0:A}.
  Infix "==" := Aeq : A_scope.

  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  (** Definition of matrix with r rows and c colums  *)
  Definition mat r c := @vec (@vec A c) r.
  
  (** *** Matrix equality *)
  
  (** Definition of matrix equality *)
  Definition meq {r c} (m1 m2 : mat r c) : Prop := veq (Aeq:=veq (Aeq:=Aeq)) m1 m2.
  Infix "==" := meq : mat_scope.
    
  (** meq is a equivalence relation *)
  Lemma meq_equiv : forall {r c : nat}, Equivalence (meq (r:=r) (c:=c)).
  Proof.
    intros. apply Equiv_veq.
  Defined.

  Global Existing Instance meq_equiv.

  (** meq is decidable *)
  Context (Dec_Aeq : Decidable Aeq).
  Lemma meq_dec : forall {r c}, Decidable (meq (r:=r) (c:=c)).
  Proof.
    intros. constructor. intros. apply veq_dec.
    constructor. apply veq_dec. auto.
  Qed.

  
  (** *** Get element *)

  (** Get an element *)
  Definition mnth {r c} (m : mat r c) (fr : fin r) (fc : fin c) := 
    vnth (vnth m fr) fc.

  (** mnth is a proper morphism *)
  Lemma mnth_aeq_mor : forall r c,
      Proper (meq (r:=r)(c:=c) ==> eq ==> eq ==> Aeq) mnth.
  Proof.
    unfold Proper, respectful.
    intros. subst. unfold mnth,meq in *. rewrite H. easy.
  Qed.

  Global Existing Instance mnth_aeq_mor.

  (** Two matrices are equal, iff its corresponding elements are equal *)
  Lemma meq_iff_nth : forall r c (m n : mat r c), 
      m == n <->
        (forall (fr : fin r) (fc : fin c), (mnth m fr fc == mnth n fr fc)%A).
  Proof.
    unfold mnth, mat, meq.
    intros; split; intros.
    - rewrite H. easy.
    - apply veq_iff_nth; intros; subst.
      apply veq_iff_nth; intros; subst. auto.
  Qed.

  (** mnth implemented with index of natural number *)
  Section mnthNat.
    
    (** Get n-th element of a matrix *)  
    Definition mnthNat {r c} (m : mat r c) (ri ci : nat) :=
      vnthNat (vnthNat m ri (A0:=vec0 A0 c)) ci (A0:=A0).
    
    (** meq and mnthNat should satisfy this constraint *)
    Lemma meq_iff_mnthNat : forall {r c : nat} (m1 m2 : mat r c),
        m1 == m2 <->
          (forall ri ci, ri < r -> ci < c -> (mnthNat m1 ri ci == mnthNat m2 ri ci)%A).
    Proof.
      intros. split; intros.
      - apply veq_iff_vnthNat; auto.
        apply (veq_iff_vnthNat (A0:=vec0 A0 c)); auto.
      - apply (veq_iff_vnthNat (A0:=vec0 A0 c)).
        intros. specialize (H i).
        unfold mnthNat in H.
        assert (forall ci, ci < c ->
                      (vnthNat (vnthNat m1 i (A0:=vec0 A0 c)) ci (A0:=A0) ==
                         vnthNat (vnthNat m2 i (A0:=vec0 A0 c)) ci (A0:=A0))%A).
        { intros. apply H; auto. }
        apply (veq_iff_vnthNat) in H1. auto.
    Qed.

    (** mnthNat is equivalent to mnth *)
    Lemma mnthNat_eq_mnth : forall {r c : nat} (m1 m2 : mat r c),
        (forall ri ci : nat, ri < r -> ci < c ->
                      (mnthNat m1 ri ci == mnthNat m2 ri ci)%A) <->
          (forall (fr : fin r) (fc : fin c), (mnth m1 fr fc == mnth m2 fr fc)%A).
    Proof.
      intros. split; intros.
      - apply meq_iff_nth. apply meq_iff_mnthNat. auto.
      - apply meq_iff_mnthNat; auto. apply meq_iff_nth. auto.
    Qed.

  End mnthNat.

  (** (mmake f)[i,j] = f(i,j) *)
  Lemma mnth_gen_iff : forall {r c} fr fc (gen : fin r -> fin c -> A),
    (mnth (vmake (fun fr0 : fin r => vmake (fun fc0 : fin c => gen fr0 fc0))) 
      fr fc == gen fr fc)%A.
  Proof.
    intros. unfold mnth. rewrite vmake_nth; auto. rewrite vmake_nth; auto. easy.
    apply Equiv_veq.
  Qed.

  (** get / set an element of a matrix *)
  Definition mget {r c} (m:mat r c) (i j:nat) : A :=
    vget (A0:=A0) (vget (A0:=vec0 A0 c) m i) j.
  Definition mset {r c} (m:mat r c) (i j : nat) (x:A) : mat r c :=
    @vset _ r m i (@vset _ c (@vget _ (vec0 A0 c) _ m i) j x).
  
End MatrixDefinition.

(* Arguments mat {A}. *)
(* (* Arguments meq {A r c}. *) *)
(* Arguments mrow {A r c}. *)
(* Arguments mcol {A r c}. *)
(* Arguments mnth {A r c}. *)
(* Arguments mget {A} A0 {r c}. *)
(* Arguments mset {A} A0 {r c}. *)



(** ** sum of matrix *)
Section msum.

  (* Context `{Equiv_Aeq : Equivalence A Aeq}. *)
  (* Context (A0:A) (Aadd : A -> A -> A).  *)
  Context `{G:AGroup}.
  Infix "+" := Aadd : A_scope.
  Infix "==" := Aeq : A_scope.

  Infix "+" := (vadd Aadd) : vector_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  (* Variable A : Type. *)
  (* Variable A0 : A. *)
  (* Variable fadd : A -> A -> A. *)
  (* Variable fadd_comm : forall x y, fadd x y = fadd y x. *)
  (* Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z). *)
  (* Variable fadd_0_r : forall x, fadd x A0 = x. *)
  
  (** Sum of a matrix: sum the result of sums of every row *)
  Definition msum {r c} (m : @mat A r c) : A :=
    vsum A0 Aadd (vsum (vec0 A0 c) (fun v1 v2 => v1 + v2) m).
  
  (** Sum of matrix generated by the generating function first column then row *)
  Definition msumrc {r c} (gen : fin r -> fin c -> A) :=
    vsum A0 Aadd (vsum (vec0 A0 c) (vadd Aadd) 
      (vmake (fun fr : fin r => (vmake (fun fc : fin c => gen fr fc))))).
  
  (** Sum of matrix generated by the generating function first row then column *)
  Definition msumcr {r c} (gen : fin r -> fin c -> A) :=
    vsum A0 Aadd (vsum (vec0 A0 r) (vadd Aadd) 
      (vmake (fun fc : fin c => (vmake (fun fr : fin r => gen fr fc))))).
  
  (** The matrices generated by the generating function first row then
      column or first column then row have same sum *)
  (** This two methods generate same result *)
  Lemma msumrc_eq_msumcr : forall {r c : nat} f, (@msumrc r c f == @msumcr r c f)%A.
  Proof.
    unfold msumrc, msumcr, msum, vsum.
    induction r.
    - induction c; intros.
      + simpl. easy.
      + simpl. rewrite vfold_vec0.
        * group_simpl.
          clear -G. induction c; simpl; easy.
        * apply G.
    - induction c; intros.
      + simpl.
        rewrite (vec_0 (vfold (vadd Aadd) vnil (vmake (fun _ : fin r => vnil)))).
        rewrite ?vfoldl_vec0. monoid_simpl.
      + simpl.
        Abort.

  (* translated matrix won't change the sum *)
(*   Lemma msum_trans : forall r c (m : @mat A r c), *)
(*     msum m == msum (mtrans m). *)
(*   Proof. *)
(*     intros. unfold sumsum. unfold sum. unfold mtrans. *)
(*     (* generalize dependent m. *)
(*     generalize dependent c. *) *)
(*     induction r; intros. *)
(*     - simpl. rewrite (vec_0 m). simpl. *)
(*       rewrite vmake_nil_eq_vconstnil. *)
(*       rewrite ?vfold_constA0; auto. *)
(*       apply vadd_nil_r. *)
(*     - pose proof vec_S m as [x [v ->]]. simpl. *)
(*       Check (fun v1 v2 : vec c => vadd fadd v1 v2). *)
(*       Check (@vadd A fadd c). *)
(*       replace (fun v1 v2 : vec c => vadd fadd v1 v2) with (@vadd A fadd c) in *. *)
(*       2:{ unfold vadd. auto. } *)
(* (*       rewrite vfold_cons_eq_add. *) *)
(*       rewrite vfold_vadd. *)
(*       Search vfold. f_equal. *)
(*       Check vfold_cons. *)
(*       rewrite vmap2_vmake_l. *)
(*       rewrite vfold_vadd; auto. rewrite IHr. *)
(*     Abort. *)

End msum.

(* Arguments msum {A} A0 fadd {r c}. *)
(* Arguments msumrc {A} A0 fadd {r c}. *)
(* Arguments msumcr {A} A0 fadd {r c}. *)



(** ** Get row or column of a matrix *)
Section mrow_mcol.

  Context `{Equiv_Aeq : Equivalence A Aeq} (A0:A).
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.
  
  (** *** Get row *)
  
  (** Get a row *)
  Definition mrow {r c} (m : @mat A r c) (fr : fin r) := vnth m fr.

  (** mrow is a proper morphism *)
  Lemma mrow_aeq_mor : forall r c,
      Proper (meq (Aeq:=Aeq)(r:=r)(c:=c) ==> eq ==> veq (Aeq:=Aeq)) mrow.
  Proof.
    unfold Proper, respectful.
    intros. subst. unfold mrow,meq in *. rewrite H. easy.
  Qed.

  Global Existing Instance mrow_aeq_mor.

  (** *** Get column *)
  
  (** Get a column *)
  (* First definition: use make + nth *)
  Definition mcol {r c} (m : @mat A r c) :=
    fun fc : fin c => vmake (fun fr : fin r => nth (nth m fr) fc).

  (* deprecated *)
  (* Second definition: use map + nth *)
  Definition mcol_deprecated r c (m : @mat A r c) (fc : fin c) := 
    map (fun v => vnth v fc) m.
  
  (** mcol is a proper morphism *)
  Lemma mcol_aeq_mor : forall r c,
      Proper (meq (Aeq:=Aeq)(r:=r)(c:=c) ==> eq ==> veq (Aeq:=Aeq)) mcol.
  Proof.
    unfold Proper, respectful.
    intros. subst. unfold mcol,meq in *.
    apply vmake_ext. intros.
    rewrite H. easy.
  Qed.

  Global Existing Instance mcol_aeq_mor.

  (** mcol (vcons v m) n = vcons (vnth v n) (mcol m n) *)
  Lemma mcol_vcons : forall (r c : nat) (fc : fin c) (v : @vec A c) 
    (m : mat r c),
    (mcol (vcons v m) fc == vcons (vnth v fc) (mcol m fc))%vector.
  Proof.
    destruct r; intros; simpl; easy.
  Qed.
  
  (** mcol vec0 i = vec0 *)
  Lemma mcol_vec0_eq_vec0 : forall r c fr,
    (mcol (vec0 (vec0 A0 c) r) fr == vec0 A0 r)%vector.
  Proof.
    intros. unfold mcol.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    rewrite ?const_nth. easy.
  Qed.

End mrow_mcol.


(** ** mat0, mat1 *)
Section mat0_mat1.
  Context {A:Type} (A0 A1 : A).

  (** mat0 *)
  Definition mat0 {r c} : @mat A r c :=
    vmake (fun (fr : fin r) => (vmake (fun (fc : fin c) => A0))).

  (** mat1 *)
  Definition mat1 {n} : @mat A n n :=
    vmake (fun (fr : fin n) => (vmake (fun (fc : fin n) =>
      if Fin.eq_dec fr fc then A1 else A0))).
    
End mat0_mat1.

Arguments mat0 {A A0}.
Arguments mat1 {A A0 A1}.


(* =============================================================== *)
(** ** Matrix transpose *)

Section MatTrans.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.

  (** Transpose a matrix : m[i][j] -> m[j][i]  *)
  Definition mtrans {r c : nat} (m : @mat A r c) : mat c r :=
    vmake (fun fc : fin c =>
             vmake (fun fr : fin r =>
                      vnth (vnth m fr) fc)).
  
  Notation "m \T" := (mtrans m).

  (** transpose is a proper morphism *)
  Lemma mtrans_aeq_mor : forall r c : nat,
      Proper (meq (Aeq:=Aeq)(r:=r)(c:=c) ==> meq (Aeq:=Aeq)(r:=c)(c:=r)) mtrans.
  Proof.
    unfold Proper, respectful.
    intros. unfold mtrans, meq in *.
    apply vmake_ext; intros.
    apply vmake_ext; intros. rewrite H. easy.
  Qed.

  Global Existing Instance mtrans_aeq_mor.

  (** The matrices generated by the generating function first row then
      column or first column then row are mutual transpose *)
  Lemma vmake_rc_eq_cr {r c} (gen : fin r -> fin c -> A) :
    let m1 := vmake (fun fr : fin r => (vmake (fun fc : fin c => gen fr fc))) in
    let m2 := vmake (fun fc : fin c => (vmake (fun fr : fin r => gen fr fc))) in
      m1 == m2\T.
  Proof.
    intros. unfold m1,m2,mtrans.
    apply vmake_ext. intros.
    apply vmake_ext. intros.
    rewrite ?vmake_nth; auto. easy. apply Equiv_veq.
  Qed.

  (* i-th column of transposed mat equal to i-th row of original mat. *)
  Lemma mcol_of_transed_eq_mrow (r c : nat) (m : @mat A r c) :
    forall (i : Fin.t r), (mcol (m\T) i == nth m i)%vector.
  Proof.
    intros i. unfold mcol,mtrans.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto. easy.
    apply Equiv_veq.
  Qed.
  
  (* i-th row of transposed mat equal to i-th column of original mat *)
  Lemma mrow_of_transed_eq_mcol (r c : nat) (m : @mat A r c) :
    forall (i : Fin.t c), (nth (m\T) i == mcol m i)%vector.
  Proof.
    intros i. unfold mcol,mtrans.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto. easy.
    apply Equiv_veq.
  Qed.
  
  (** m\T\T = m *)
  Theorem mtrans_trans (r c : nat) (m : @mat A r c) : m\T\T == m.
  Proof.
    unfold mtrans.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    easy. apply Equiv_veq. apply Equiv_veq.
  Qed.
  
  (* m[i,j] = (m^T)[j,i] *)
  Lemma mtrans_elem_inv (r c : nat) (m : @mat A r c) :
    forall (fr : fin r) (fc : fin c), 
    (vnth (vnth m fr) fc == vnth (vnth (m\T) fc) fr)%A.
  Proof.
    intros. unfold mtrans. rewrite ?vmake_nth; auto. easy. apply Equiv_veq.
  Qed.

End MatTrans.

(* Arguments mtrans {A r c}. *)
(* Arguments mtrans_trans {A r c}. *)
(* Arguments mtrans_elem_inv {A r c}. *)


(** ** Mapping matrix to matrix *)
Section mmap.

  Context {A:Type}.
  
  Definition mmap {r c} (m : mat r c) (f : A -> A) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => f (mnth m fr fc))).

  Fixpoint mmap_old {r c} (m : mat r c) (f : A -> A) : mat r c :=
    match m with
    | vnil => vnil
    | vcons x t => cons (vmap f x) (mmap_old t f)
    end.
    
End mmap.


(** ** Mapping two matrices to another matrix *)
Section mmap2.
  
  Context `{Equiv_Aeq : Equivalence A Aeq} (Aadd : A -> A -> A).
  Infix "+" := Aadd : A_scope.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.

  (* Variable A : Type. *)
  (* Variable f : A -> A -> A. *)
  (* Variable f_comm : forall a b, f a b = f b a. *)
  (* Variable f_assoc : forall a b c, f (f a b) c = f a (f b c).  *)

  Definition mmap2 {r c} (m1 m2 : mat r c) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => (mnth m1 fr fc) + (mnth m2 fr fc))).

  Lemma mmap2_comm {r c} (m1 m2 : mat r c) (Comm : Commutative Aadd Aeq) :
    mmap2 m1 m2 == mmap2 m2 m1.
  Proof.
    unfold mmap2, mnth.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply commutative.
    apply Equiv_veq. apply Equiv_veq.
  Qed.
  
  Lemma mmap2_assoc {r c} (m1 m2 m3 : mat r c) (Assoc : Associative Aadd Aeq) :
    mmap2 (mmap2 m1 m2) m3 == mmap2 m1 (mmap2 m2 m3).
  Proof.
    unfold mmap2, mnth.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    rewrite associative. easy.
    all: try apply Equiv_veq; try apply eq_equivalence.
  Qed.

End mmap2.

(** Arithmatic of matrix *)
Section MatArith.

  (* Variable A : Type. *)
  (* Variable A0 A1 : A. *)
  (* Variable fopp : A -> A. *)
  (* Variable fadd fsub fmul : A -> A -> A. *)
  (* Variable fadd_comm : forall x y, fadd x y = fadd y x. *)
  (* Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z). *)
  (* Variable fmul_comm : forall x y, fmul x y = fmul y x. *)
  (* Variable fmul_assoc : forall x y z, fmul (fmul x y) z = fmul x (fmul y z). *)
  (* Variable fadd_0_l : forall x, fadd A0 x = x. *)
  (* Variable fadd_0_r : forall x, fadd x A0 = x. *)
  (* Variable fmul_0_l : forall x, fmul A0 x = A0. *)
  (* Variable fmul_0_r : forall x, fmul x A0 = A0. *)
  (* Variable fmul_add_distl : forall x y z, *)
  (*   fmul x (fadd y z) = fadd (fmul xnnn y) (fmul x z). *)
  (* Variable fmul_add_distr : forall x y z, *)
  (*   fmul (fadd x y) z = fadd (fmul x z) (fmul y z). *)
  (* Variable fopp_opp : forall a, fopp (fopp a) = a. *)
  (* Variable fadd_opp : forall a, fadd a (fopp a) = A0. *)
  (* Variable fsub_comm : forall a b, fsub a b = fopp (fsub b a). *)
  (* Variable fsub_assoc : forall a b c, fsub (fsub a b) c = fsub a (fadd b c). *)
  (* Variable fsub_0_l : forall t, fsub A0 t = fopp t. *)
  (* Variable fsub_0_r : forall t, fsub t A0 = t. *)
  (* Variable fsub_self : forall t, fsub t t = A0. *)
  (* Variable fmul_1_l : forall a, fmul A1 a = a. *)

  Context `{R:Ring}.
  Add Ring ring_inst : make_ring_theory.

  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := (fun a b => a + (-b)) : A_scope.
  Infix "*" := Amul : A_scope.
  Infix "==" := Aeq : A_scope.
  
  Infix "+" := (vadd Aadd) : vector_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.

  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  Notation "m \T" := (mtrans m) : mat_scope.

  
  (** *** Operations *)
  
  (** vdot : vec n -> vec n -> A *)
  Definition vdot {n} (v1 v2 : vec n) := vfold Aadd A0 (map2 Amul v1 v2).

  (** vdotm : vec r -> mat r c -> vec c *)
  Definition vdotm {r c} (v : vec r) (m : mat r c) : vec c :=
    vmake (fun fc : fin c => vdot v (mcol m fc)). 
  
  (** mdotv : mat r c -> vec c -> vec r *)
  Definition mdotv {r c} (m : mat r c) (v : vec c) : vec r :=
    vmake (fun fr : fin r => vdot (mrow m fr) v).
  
  (** matrix addition *)
  Definition madd {r c} (m1 m2 : mat r c) : mat r c :=
    vmake (fun fr : fin r =>
             vmake (fun fc : fin c =>
                      ((mnth m1 fr fc) + (mnth m2 fr fc))%A
               )).
  Infix "+" := madd : mat_scope.

  (** matrix opposition *)
  Definition mopp {r c} (m : mat r c) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => - (mnth m fr fc))).
  Notation "- a" := (mopp a) : mat_scope.

  (** subtraction *)
  Definition msub {r c} (m1 m2 : mat r c) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => (mnth m1 fr fc) - (mnth m2 fr fc))).
  Infix "-" := msub : mat_scope.
  
  (** matrix left scalar multiplication *)
  Definition mcmul {r c} (a : A) (m : mat r c) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => a * (mnth m fr fc))).
  Infix "c*" := mcmul : mat_scope.
  
  (** matrix right scalar multiplication *)
  Definition mmulc {r c} (m : mat r c) (a : A) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => (mnth m fr fc) * a)).
  Infix "*c" := mmulc : mat_scope.

  (** multiplication *)
  Definition mmul {r s c} (m1 : mat r s) (m2 : mat s c) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => vdot (nth m1 fr) (mcol m2 fc) )).
  Infix "*" := mmul : mat_scope.

  
  (** *** Properties of mnth *)
    
  (** (vnth m1 fr) + (vnth m2 fr) = gen (m1[fr] + m2[fr]) *)
  Lemma vadd_eq_vmake_mnth : forall r c fr (m1 m2 : mat r c),
    (vnth m1 fr + vnth m2 fr ==
      vmake (fun fc : fin c => (mnth m1 fr fc + mnth m2 fr fc)%A))%vector.
  Proof.
    intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    rewrite vadd_nth. easy. apply monoidEquiv.
  Qed.


  (** *** Properties of vdot *)

  (** [a1;v1] . [a2;v2] = (a1 * a2) + (v1 . v2) *)
  Lemma vdot_cons : forall n a1 a2 (v1 v2 : vec n),
    (vdot (a1::v1) (a2::v2) == (a1 * a2) + (vdot v1 v2))%A.
  Proof.
    unfold vdot. 
    destruct n; intros a1 a2 v1 v2; vsimp; simpl in *. apply commutative.
    rewrite vfold_Aadd. group_simpl. f_equiv.
    apply vfoldl_ext_samef; try easy; try apply monoidAaddProper.
    group_simpl.
  Qed.

  (** vdot is a proper morphism *)
  Lemma vdot_aeq_mor : forall {n : nat},
      let r := veq (Aeq:=Aeq) in Proper (r ==> r ==> Aeq) (vdot (n:=n)).
  Proof.
    unfold Proper, respectful.
    induction n; intros; vsimp; simpl. cbv. easy.
    simpl. rewrite ?vdot_cons.
    apply vcons_eq_iff in H as [], H0 as [].
    f_equiv; auto. f_equiv; easy.
  Qed.

  Global Existing Instance vdot_aeq_mor.

  (** v1 . v2 = v2 . v1 *)
  Lemma vdot_comm (n : nat) (v1 v2 : vec n) : (vdot v1 v2 == vdot v2 v1)%A.
  Proof.
    unfold vdot. destruct n; vsimp; simpl. easy.
    apply vfoldl_ext_samef.
    - apply monoidAaddProper.
    - group_simpl. apply commutative.
    - apply vmap2_comm. apply amonoidComm.
  Qed.

  (** [] . v = 0 *)
  Lemma vdot_nil_l : forall (v : vec 0), (vdot nil v == A0)%A.
  Proof.
    intros. rewrite (vec_0 v). unfold vdot. simpl. easy.
  Qed.

  (** v . [] = 0 *)
  Lemma vdot_nil_r : forall (v : vec 0), (vdot v nil == A0)%A.
  Proof.
    intros. rewrite (vec_0 v). unfold vdot. simpl. easy.
  Qed.

  (** vec0 . v = 0 *)
  Lemma vdot_vec0_l : forall {n} (v : vec n), (vdot (vec0 A0 n) v == A0)%A.
  Proof.
    induction n; intros; vsimp; simpl. cbv. easy.
    rewrite vdot_cons. rewrite IHn. ring.
  Qed.

  (** v . vec0 = 0 *)
  Lemma vdot_vec0_r : forall {n} (v : vec n), (vdot v (vec0 A0 n) == A0)%A.
  Proof.
    induction n; intros; vsimp; simpl. cbv. easy.
    rewrite vdot_cons. rewrite IHn. ring.
  Qed.

  (** v1 + v2) . v = v1 . v + v2 . v*)
  Lemma vdot_vadd_distr_l n (v v1 v2 : vec n) :
    (vdot (v1 + v2)%vector v == (vdot v1 v) + (vdot v2 v))%A.
  Proof.
    induction n; intros; vsimp; simpl. cbv. ring.
    rewrite ?vdot_cons. rewrite IHn. ring.
  Qed.
  
  (** v . (v1 + v2) = v . v1 + v . v2 *)
  Lemma vdot_vadd_distr_r : forall n (v v1 v2 : vec n),
    (vdot v (v1 + v2)%vector == (vdot v v1) + (vdot v v2))%A.
  Proof.
    induction n; intros; vsimp; simpl. cbv. ring.
    rewrite ?vdot_cons. rewrite IHn. ring.
  Qed.

  (** a * (v1 . v2) = (a c* v1) . v2 *)
  Lemma vdot_mult_distr_l : forall n a (v1 v2 : vec n),
    (a * (vdot v1 v2) == vdot (vmake (fun fi => a * (vnth v1 fi))) v2)%A.
  Proof.
    induction n; intros; vsimp; simpl. cbv. ring.
    rewrite ?vdot_cons.
    rewrite <- IHn. ring.
    (* Tips: the proof is simple than the proof of dot_product_distr_mult in 
       CoLoR Utils.Vecotr.VecArith.v *)
  Qed.

  (** v1 . (m . v2) = (v1 . m) . v2 *)
  Lemma vdot_vec_mat_vec_assoc : forall r c (v1 : @vec A r) (m : mat r c) (v2 : vec c),
    (vdot v1 (vmake (fun fr : fin r => vdot (mrow m fr) v2)) ==
    vdot (vmake (fun fc : fin c => vdot v1 (mcol m fc))) v2)%A.
  Proof.
    unfold mat. induction r; intros.
    - (* base case *)
      vsimp. simpl. rewrite vdot_nil_l.
      assert (vmake (fun fc : fin c => vdot vnil (mcol m fc)) == vec0 A0 c)%vector.
      { apply veq_iff_nth. intros; subst. rewrite vmake_nth.
        rewrite vdot_nil_l. rewrite const_nth. easy. apply monoidEquiv. }
      rewrite H. rewrite vdot_vec0_l. easy.
    - (* induction case *)
      (* use "eta, hd, tl, nth, cons" to eliminate "vec (S n)" *)
      rewrite (eta v1).
      rewrite (eta (vmake (fun fr => vdot (mrow m fr) v2))).
      rewrite vdot_cons; auto. rewrite !vnth_head.
      rewrite vmake_nth. 2:{ apply monoidEquiv. } 
      rewrite vmake_tail. rewrite (eta m). simpl.
      rewrite (IHr).
      (* tail elements *)
      set (va := (vmake (fun fc : fin c => vdot (vtl v1) (mcol (vtl m) fc)))).
      (* head element *)
      set (vb := vmake (fun (fc : fin c) => (vnth v1 F1 * (vnth (vhd m) fc))%A)).
      (* whole *)
      set (vc := (vmake (fun fc : fin c => vdot (vcons (vhd v1) (vtl v1))
                                           (mcol (vcons (vhd m) (vtl m)) fc)))).
      (* Tips: an importante relation: the dot product of vector and matrix are 
         splited to two parts *)
      assert (vc == va + vb)%vector.
      + apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
        unfold va,vb,vc. rewrite vadd_vmake_vmake. f_equiv.
        apply vmake_ext; intros. rewrite mcol_vcons.
        rewrite vdot_cons. rewrite vnth_head. apply commutative.
      + rewrite H.
        rewrite vdot_vadd_distr_l; auto. rewrite commutative. f_equiv.
        unfold vb. rewrite vdot_mult_distr_l. easy.
  Qed.
    
  (** *** Properties of madd,mopp,msub *)

  (** - (- m) = m *)
  Lemma mopp_mopp : forall {r c} (m : mat r c), - (- m) == m.
  Proof.
    intros.
    unfold mopp, mnth.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** m1 + m2 = m2 + m1 *)
  Lemma madd_comm {r c} (m1 m2 : mat r c) : m1 + m2 == m2 + m1.
  Proof.
    unfold madd, mnth.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** (m1 + m2) + m3 == m1 + (m2 + m3) *)
  Lemma madd_assoc {r c} (m1 m2 m3 : mat r c) : (m1 + m2) + m3 == m1 + (m2 + m3).
  Proof.
    unfold madd, mnth.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** mat0 + m = m *)
  Lemma madd_0_l : forall {r c} (m : @mat A r c), mat0 (A0:=A0) r c + m == m.
  Proof.
    unfold madd, mnth, mat0. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** m + mat0 = m *)
  Lemma madd_0_r : forall {r c} (m : @mat A r c), m + mat0 (A0:=A0) r c == m.
  Proof.
    unfold madd, mnth, mat0. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** m1 - m2 = - (m2 - m1) *)
  Lemma msub_comm : forall {r c} (m1 m2 : mat r c), m1 - m2 == - (m2 - m1).
  Proof.
    unfold msub, mopp, mnth. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** (m1 - m2) - m3 == m1 - (m2 + m3) *)
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 - m2) - m3 == m1 - (m2 + m3).
  Proof.
    unfold msub, madd, mnth. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** mat0 - m = - m *)
  Lemma msub_0_l : forall {r c} (m : mat r c), mat0 (A0:=A0) r c - m == - m.
  Proof.
    unfold msub, mopp, mat0, mnth. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** m - mat0 = m *)
  Lemma msub_0_r : forall {r c} (m : mat r c), m - mat0 (A0:=A0) r c == m.
  Proof.
    unfold msub, mat0, mnth. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** m - m = mat0 *)
  Lemma msub_self : forall {r c} (m : mat r c), m - m == mat0 (A0:=A0) r c.
  Proof.
    unfold msub, mat0, mnth. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** m + (- m) = mat0 *)
  Lemma madd_mopp : forall {r c} (m : mat r c), m + (- m) == mat0 (A0:=A0) r c.
  Proof.
    unfold madd, mopp, mat0, mnth. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** *** Properties of mcmul, mmulc. *)

  (** mcmul is a proper morphism *)
  Lemma mcmul_aeq_mor : forall r c: nat,
      Proper (Aeq ==>
                meq (Aeq:=Aeq)(r:=r)(c:=c) ==>
                meq (Aeq:=Aeq)(r:=r)(c:=c)) mcmul.
  Proof.
    unfold Proper, respectful.
    intros. unfold mcmul, meq in *.
    apply vmake_ext; intros.
    apply vmake_ext; intros. rewrite H,H0. easy.
  Qed.

  Global Existing Instance mcmul_aeq_mor.

  (** mmulc is a proper morphism *)
  Lemma mmulc_aeq_mor : forall r c: nat,
      Proper (meq (Aeq:=Aeq)(r:=r)(c:=c) ==>
                Aeq ==>
                meq (Aeq:=Aeq)(r:=r)(c:=c)) mmulc.
  Proof.
    unfold Proper, respectful.
    intros. unfold mmulc, meq in *.
    apply vmake_ext; intros.
    apply vmake_ext; intros. rewrite H,H0. easy.
  Qed.

  Global Existing Instance mmulc_aeq_mor.

  (** m *c a = a c* m *)
  Lemma mmulc_eq_mcmul : forall {r c} (a : A) (m : mat r c), m *c a == a c* m.
  Proof.
    unfold mcmul, mmulc, mnth. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** a c* (b c* m) = (a * b) c* m *)
  Lemma mcmul_assoc : forall {r c} (a b : A) (m : mat r c),
      a c* (b c* m) == (a * b)%A c* m.
  Proof.
    unfold mcmul, mmulc, mnth. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** a c* (b c* m) = b c* (a c* m) *)
  Lemma mcmul_perm : forall {r c} (a b : A) (m : mat r c), a c* (b c* m) == b c* (a c* m).
  Proof.
    unfold mcmul, mmulc, mnth. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** a c* (m1 + m2) = (a c* m1) + (a c* m2) *)
  Lemma mcmul_distr_l : forall {r c} (a : A) (m1 m2 : mat r c),
      a c* (m1 + m2) == (a c* m1) + (a c* m2).
  Proof.
    unfold mcmul, madd, mnth. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.
  
  (** (a + b) c* m = (a c* m) + (b c* m) *)
  Lemma mcmul_distr_r : forall {r c} (a b : A) (m : mat r c),
      (a + b)%A c* m == (a c* m) + (b c* m).
  Proof.
    unfold mcmul, madd, mnth. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** 1 c* m = m *)
  Lemma mcmul_1_l : forall {r c} (m : mat r c), A1 c* m == m.
  Proof.
    unfold mcmul, mnth. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** 0 c* m = mat0 *)
  Lemma mcmul_0_l : forall {r c} (m : mat r c), A0 c* m == mat0 (A0:=A0) r c.
  Proof.
    unfold mcmul, mnth, mat0. intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    ring. all: try apply monoidEquiv.
  Qed.

  (** *** Properties of mmul. *)

  (** (A * B)\T = B\T * A\T *)
  Lemma mmul_mtrans (r s c : nat) (m1 : mat r s) (m2 : mat s c) :
    (m1 * m2)\T == (m2\T) * (m1\T).
  Proof.
    unfold mmul.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    rewrite <- mtrans_elem_inv.    (* m[i][j] = (m\T)[j][i] *)
    rewrite ?vmake_nth.
    rewrite mcol_of_transed_eq_mrow.
    rewrite <- mrow_of_transed_eq_mcol. apply vdot_comm.
    all: apply monoidEquiv.
  Qed.

  (** mmul is a proper morphism *)
  Lemma mmul_aeq_mor : forall r c s: nat,
      Proper (meq (Aeq:=Aeq)(r:=r)(c:=c) ==>
                meq (Aeq:=Aeq)(r:=c)(c:=s) ==>
                meq (Aeq:=Aeq)(r:=r)(c:=s)) mmul.
  Proof.
    unfold Proper, respectful.
    intros. unfold mmul, meq in *.
    apply vmake_ext; intros.
    apply vmake_ext; intros.
    rewrite H,H0. easy.
  Qed.

  Global Existing Instance mmul_aeq_mor.

  (** (m1 * m2) * m3 == m1 * (m2 * m3) *)
  Lemma mmul_assoc r s c t  (m1 : mat r s) (m2 : mat s c) (m3 : mat c t) :
    (m1 * m2) * m3 == m1 * (m2 * m3).
  Proof.
    unfold mmul. unfold mat in *.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    rewrite <- vdot_vec_mat_vec_assoc; auto. f_equiv.
    unfold mcol, mrow.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    easy. all: apply monoidEquiv.
  Qed.

  (** m1 * (m2 + m3) = m1 * m2 + m1 * m3 *)
  Lemma mmul_madd_distr_l : forall {r c t} (m1 : mat r c) (m2 m3 : mat c t), 
      m1 * (m2 + m3) == m1 * m2 + m1 * m3.
  Proof.
    intros. unfold mmul, madd, mnth, mcol.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    rewrite <- vdot_vadd_distr_r; auto.
    rewrite vadd_vmake_vmake. f_equiv.
    apply vmake_ext; intros. rewrite ?vmake_nth.
    easy. all: apply monoidEquiv.
  Qed.
  
  (** (m1 + m2) * m3 = m1 * m3 + m2 * m3 *)
  Lemma mmul_madd_distr_r : forall {r c s} (m1 m2 : mat r c) (m3 : mat c s), 
      (m1 + m2) * m3 == m1 * m3 + m2 * m3.
  Proof.
    intros. unfold mmul, madd, mnth, mcol.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth; auto.
    rewrite <- vdot_vadd_distr_l; auto.
    rewrite vadd_eq_vmake_mnth. unfold mnth.
    easy. all: apply monoidEquiv.
  Qed.
  
  (** mat0 * m = mat0 *)
  Lemma mmul_0_l : forall {r c t} (m : mat c t), 
    (mat0 (A0:=A0) r c) * m == mat0 (A0:=A0) r t.
  Proof.
    intros. unfold mmul. unfold mat0. 
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth.
    rewrite vmake_0_eq_vec0. rewrite vdot_vec0_l.
    easy. all: apply monoidEquiv.
  Qed.
  
  (** m * mat0 = mat0 *)
  Lemma mmul_0_r : forall {r c t} (m : mat r c),
      m * (mat0 (A0:=A0) c t) == mat0 (A0:=A0) r t.
  Proof.
    intros. unfold mmul. unfold mat0. 
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth.
    rewrite vdot_aeq_mor. 2: reflexivity. apply vdot_vec0_r.
    unfold mcol.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth.
    rewrite const_nth. easy.
    all: apply monoidEquiv.
  Qed.
  
  (**  mcol of a generated matrix get exact column *)
  Lemma mcol_vmake : forall r c fc0 (gen : fin r -> fin c -> A),
    (mcol (vmake (fun fr : fin r => vmake (fun fc : fin c => gen fr fc))) fc0
     == vmake (fun fr : fin r => gen fr fc0))%vector.
  Proof.
    intros.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth.
    generalize dependent c.
    generalize dependent f2.
    destruct r; intros; vsimp; unfold mcol.
    rewrite ?vmake_nth; try easy.
    rewrite ?vmake_nth; try easy.
    all: apply monoidEquiv.
  Qed.

  (** v . (col_of_mat1 fc) = v[fc] *)
  Lemma vdot_mat1col_r : forall n (fn : fin n) v,
    (vdot v 
      (vmake (fun fn' : fin n => if Fin.eq_dec fn' fn then A1 else A0)) == 
    vnth v fn)%A.
  Proof.
    induction n; intros; finsimp; vsimp; simpl.
    - rewrite vdot_cons.
      destruct (Fin.eq_dec); try easy.
      rewrite vmake_0_eq_vec0. rewrite vdot_vec0_r. ring. apply monoidEquiv.
    - rewrite vdot_cons. rewrite <- IHn.
      ring_simplify. apply vdot_aeq_mor; try easy.
      apply veq_iff_nth; intros; subst. rewrite ?vmake_nth.
      destruct (Fin.eq_dec), Fin.eq_dec; try easy.
      apply FS_inj in e. easy. subst. easy.
      all: apply monoidEquiv.
  Qed.
  
  (** mat1\T = mat1 *)  
  Lemma mtrans_mat1 : forall n, (@mat1 A A0 A1 n)\T == (@mat1 A A0 A1 n).
  Proof.
    intros. unfold mtrans, mat1.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth.
    destruct Fin.eq_dec; subst; destruct Fin.eq_dec; try easy. subst. easy.
    all: apply monoidEquiv.
  Qed.
  
  (** m * mat1 = m *)
  Lemma mmul_1_r : forall {r c} (m : mat r c), m * (@mat1 A A0 A1 c) == m.
  Proof.
    intros. unfold mmul,mat1.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth.
    apply veq_iff_nth; intros; subst; rewrite ?vmake_nth.
    rewrite mcol_vmake. rewrite vdot_mat1col_r. easy.
    all: apply monoidEquiv.
  Qed.
  
  (** mat1 * m = m *)
  Lemma mmul_1_l : forall {r c} (m : mat r c), (@mat1 A A0 A1 r) * m == m.
  Proof.
    (** mat1 * m = m
        (mat1 * m)\T\T = m
        (m\T * mat1\T)\T = m
        (m\T * mat1)\T = m
        m\T\T = m
        m = m *)
    intros.
    rewrite <- mtrans_trans at 1. rewrite mmul_mtrans.
    rewrite mtrans_mat1. rewrite mmul_1_r. rewrite mtrans_trans. easy.
  Qed.
  
End MatArith.


(** Convert between vector and list *)
Section v2l_l2v.

  Context `{Equiv_Aeq : Equivalence A Aeq} {A0 : A}.

  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vector_scope.
  
  Fixpoint v2l {n} (v : @vec A n) : list A :=
    match v with
    | []%vector => []%list
    | (x :: v')%vector => (x :: (v2l v'))%list
    end.
  
  Fixpoint l2v (l : list A) (n : nat) : vec n :=
    match n with
    | 0 => []%vector
    | S n' => (List.hd A0 l) :: (l2v (List.tl l) n')
    end.
  
  Lemma v2l_length : forall n (v : @vec A n), length (v2l v) = n.
  Proof.
    intros. induction v; simpl; auto.
  Qed.

  (** v2l is a proper morphism *)
  Lemma v2l_aeq_mor : forall n, Proper (@veq _ Aeq n ==> eqlistA Aeq) v2l.
  Proof.
    unfold Proper, respectful.
    induction n; intros; vsimp. easy.
    simpl. apply vcons_eq_iff in H as [].
    f_equiv; auto.
  Qed.

  Global Existing Instance v2l_aeq_mor.

  (** l2v is a proper morphism *)
  (* ToDo: I cann't write a correct formalization of this proper morphism *)
  (* Lemma l2v_aeq_mor : forall (n:nat), Proper (eqlistA Aeq ==> eq ==> veq) (l2v). *)
  Lemma l2v_aeq_mor : forall (n:nat) (l1 l2 : list A),
      (l1 == l2)%list -> l2v l1 n == l2v l2 n.
  Proof.
    induction n; intros; simpl. easy.
    (* apply vcons_aeq_mor; auto. *)
    constructor; auto.
    + rewrite H. easy.
    + apply IHn. rewrite H. easy.
  Qed.

  (* Global Existing Instance l2v_aeq_mor. *)

  (** if l2v equal, then list equal *)
  Lemma l2v_eq_imply_list_eq : forall n (l1 l2 : list A),
      length l1 = n -> length l2 = n -> l2v l1 n == l2v l2 n ->
      (l1 == l2)%list.
  Proof.
    induction n; intros.
    - apply List.length_zero_iff_nil in H,H0. subst. easy.
    - destruct l1,l2; try easy.
      inv H. inv H0. simpl in *.
      apply vcons_eq_iff in H1 as [].
      apply IHn with (l1 := l1) in H2; auto.
  Qed.

  (** if v2l equal, then vector equal *)
  Lemma v2l_eq_imply_veq : forall n (v1 v2 : vec n),
      (v2l v1 == v2l v2)%list -> v1 == v2.
  Proof.
    induction n; intros; vsimp; simpl in *. easy.
    apply cons_eq_iff in H as []. apply IHn in H0.
    apply vcons_eq_iff; split; auto.
  Qed.

  Lemma v2l_l2v_id : forall (n : nat) (l : list A), length l = n ->
    (v2l (l2v l n) == l)%list.
  Proof.
    induction n; intros; simpl.
    - apply (length_zero_iff_nil (Aeq:=Aeq)) in H. easy.
    - destruct l; try easy. rewrite IHn; auto. f_equiv.
  Qed.
  
  Lemma l2v_v2l_id : forall (n : nat) (v : vec n), l2v (v2l v) n == v.
  Proof.
    intros. induction v; simpl. easy.
    (* apply vcons_aeq_mor; auto. *)
    constructor; auto. easy.
  Qed.
  
End v2l_l2v.

Arguments v2l {A n}.
Arguments l2v {A}.


(** Convert between matrix and list list *)
Section m2l_l2m.

  Context `{Equiv_Aeq : Equivalence A Aeq} {A0 : A}.

  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  
  Fixpoint m2l {r c} (m : @mat A r c) : list (list A) :=
    match m with
    | []%vector => []%list
    | (x :: v')%vector => (v2l x) :: (m2l v')
    end.

  Fixpoint l2m (dl : list (list A)) (r c : nat) : @mat A r c :=
    match r with
    | 0 => Vector.nil
    | S n' => Vector.cons (l2v A0 (List.hd List.nil dl) c) 
      (l2m (List.tl dl) n' c)
    end.

  (** m2l is a proper morphism *)
  Lemma m2l_aeq_mor : forall r c, Proper (@meq A Aeq r c ==> eqlistA (eqlistA Aeq)) m2l.
  Proof.
    unfold Proper, respectful, mat.
    induction r; intros; vsimp; simpl. easy.
    apply vcons_eq_iff in H as []. f_equiv; auto.
    rewrite H. easy.
  Qed.

  Global Existing Instance m2l_aeq_mor.

  (** if l2m equal, then dlist equal *)
  Lemma l2m_eq_imply_dlist_eq : forall r c (dl1 dl2 : list (list A)),
      length dl1 = r -> length dl2 = r -> width dl1 c -> width dl2 c ->
      l2m dl1 r c == l2m dl2 r c -> (dl1 == dl2)%dlist.
  Proof.
    induction r; intros; simpl in *; try easy.
    - apply List.length_zero_iff_nil in H,H0. subst. easy.
    - destruct dl1,dl2; try easy.
      apply vcons_eq_iff in H3 as [].
      inv H. inv H0. inv H1. inv H2.
      simpl in *. f_equiv; auto.
      + apply (l2v_eq_imply_list_eq (n:=length l) (A0:=A0)); auto.
      + apply IHr with (c:=length l); auto.
  Qed.

  (** if m2l equal, then mat equal *)
  Lemma m2l_eq_imply_mat_eq : forall r c (m1 m2 : mat r c),
      (m2l m1 == m2l m2)%dlist -> m1 == m2.
  Proof.
    unfold mat.
    induction r; intros; vsimp; simpl in *. easy.
    apply cons_eq_iff in H as [].
    apply IHr in H0. apply v2l_eq_imply_veq in H.
    apply vcons_eq_iff; split; auto.
  Qed.

  Lemma m2l_l2m_id : forall {r c} (dl : list (list A)) (H1 : length dl = r)
    (H2 : width dl c), (m2l (l2m dl r c) == dl)%dlist.
  Proof.
    induction r; intros.
    - simpl. apply (length_zero_iff_nil (Aeq:=eqlistA Aeq)) in H1. easy.
    - destruct dl. easy. simpl. inv H1. inv H2. rewrite IHr; auto.
      f_equiv. apply v2l_l2v_id; auto.
  Qed.
  
  Lemma l2m_m2l_id : forall {r c} (m : mat r c), l2m (m2l m) r c == m. 
  Proof.
    intros. induction m; simpl. easy.
    constructor; auto. apply l2v_v2l_id.
  Qed.

  Lemma l2m_inj : forall {r c} (d1 d2 : list (list A)),
    length d1 = r -> width d1 c -> 
    length d2 = r -> width d2 c -> 
    ~(d1 == d2)%dlist -> ~(l2m d1 r c == l2m d2 r c).
  Proof.
    intros. intro. apply l2m_eq_imply_dlist_eq in H4; auto.
  Qed.
  
  Lemma l2m_surj : forall {r c} (m : mat r c), 
    (exists d, l2m d r c == m).
  Proof.
    unfold mat in *.
    induction r; intros; vsimp.
    - exists List.nil. simpl. easy.
    - simpl. destruct (IHr c x0).
      exists (List.cons (v2l x) x1). simpl.
      apply vcons_eq_iff; split; auto. apply l2v_v2l_id.
  Qed.
    
  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c),
    ~(m1 == m2) -> ~(m2l m1 == m2l m2)%dlist.
  Proof.
    intros. intro. apply m2l_eq_imply_mat_eq in H0. easy.
  Qed.
  
  Lemma m2l_surj : forall {r c} (d : list (list A)), 
    length d = r -> width d c -> 
    (exists m, @m2l r c m == d)%dlist.
  Proof.
    induction r; intros; simpl.
    - apply List.length_zero_iff_nil in H. subst. exists []. simpl. easy.
    - destruct d. easy. inv H. inv H0.
      destruct (IHr (length l) d eq_refl H3).
      exists ((l2v A0 l (length l)) :: x). simpl. f_equiv; auto.
      apply v2l_l2v_id. auto.
  Qed.
  
End m2l_l2m.

Arguments m2l {A r c}.
Arguments l2m {A} A0 dl r c.
