(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Basic configuration (Library, Notations, Warning, etc.)
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
  1. Basic libraries in whole project
  3. Reserved notations for consistence.
    https://coq.inria.fr/distrib/V8.13.2/refman/language/coq-library.html 
  3. Eliminate some warning.  
    https://coq.inria.fr/distrib/V8.13.2/refman/user-extensions/
    syntax-extensions.html?highlight=warning
  4. Customized tactics.
*)


(* ######################################################################### *)
(** * Basic libraries *) 

Require Export Coq.Classes.Morphisms.     (* respectful, ==> *)
Require Export Coq.Setoids.Setoid.        (*  *)
Require Export Coq.Classes.SetoidTactics. (* add_morphism_tactic *)
Require Export Coq.Relations.Relations.   (* equivalence *)
Require Export Coq.Bool.Sumbool.          (* sumbool_not *)
Require Export Coq.Bool.Bool.             (* reflect *)
Require Export Ring.                      (* ring *)
Require Export Field.                     (* field *)

Require Export Coq.Logic.Classical.
Require Export Coq.Logic.FunctionalExtensionality.

Require Arith ZArith QArith Qcanon Reals List SetoidList.


(* ######################################################################### *)
(** * Reserved Notations *)

(** Reserved Notations, to keep same precedence and associativity *)
Reserved Infix    "=="      (at level 70, no associativity).      (* equiv *)
Reserved Infix    "==?"     (at level 65, no associativity).      (* decidable *)
Reserved Infix    "<>?"     (at level 65, no associativity).      (* decidable right *)
Reserved Notation "a != b"  (at level 70, no associativity).
Reserved Infix    "=?"      (at level 70, no associativity).
Reserved Infix    "+"       (at level 50, left associativity).
Reserved Infix    "-"       (at level 50, left associativity).
Reserved Infix    "*"       (at level 40, left associativity).
Reserved Infix    "/"       (at level 40, left associativity).
Reserved Infix    "c*"      (at level 40, left associativity).
Reserved Infix    "*c"      (at level 40, left associativity).
Reserved Infix    "\o"      (at level 50, no associativity).
Reserved Infix    "⋅"       (at level 40, no associativity).
Reserved Notation "- a"     (at level 35, right associativity).
Reserved Notation "/ a"     (at level 35, right associativity).
Reserved Notation "a \T"    (at level 34, left associativity).
Reserved Notation "m1 @ m2" (at level 30, no associativity).

(* this level is consistent with Mathcomp.ssreflect.ssrnotations.v *)

(* safe access (any index) *)
Reserved Notation "m ! i ! j"  (at level 20, i at next level).
Reserved Notation "v ! i"      (at level 20, i at next level).
(* unsafe access (developer must give valid index) *)
Reserved Notation "m $ i $ j"  (at level 20, i at next level).
Reserved Notation "v $ i"      (at level 20, i at next level).



(* ######################################################################### *)
(** * Eliminate Warning. *)

(* Export Set Warnings "-notation-overridden". *)


(* ######################################################################### *)
(** * Customized tactics *)

(** ** Tactics with a short name *)

Global Ltac gd k := generalize dependent k.

(* repeat split *)
Ltac ssplit := 
  repeat 
  match goal with
  | |- _ /\ _ => split
  end.

Ltac inv H :=
  inversion H; clear H; subst.

Ltac simp_proper :=
  unfold Proper; unfold respectful.


(* ######################################################################### *)
(** * Global notations *)

(* this level is consistent with coq.ssr.ssrbool.v *)
(* Notation "~~ b" := (negb b) (at level 35, right associativity) : bool_scope. *)


(* ######################################################################### *)
(** * Global coercions *)

(** bool to Prop *)
Definition is_true (b : bool) : Prop := b = true.
Coercion is_true : bool >-> Sortclass.

Goal true.
apply eq_refl. Qed.

Goal negb false.
simpl. apply eq_refl. Qed.

Example eqnP (n m : nat) : reflect (n = m) (Nat.eqb n m).
Proof.
  gd m. induction n; intros [|m]; simpl; try constructor; auto.
  destruct IHn with m; subst; constructor; auto.
Qed.


(* ######################################################################### *)
(** * A relation is decidable *)

(** ** Class *)

Class Dec {A : Type} (Aeq : relation A) := {
    dec : forall (a b : A), {Aeq a b} + {~(Aeq a b)};
  }.
Infix "==?" := (dec).
Infix "<>?" := (fun a b => sumbool_not _ _ (a ==? b)).

(** ** Instances *)

Section Instances.
  Import Nat Arith ZArith QArith Qcanon Reals SetoidList.
  
  Global Instance Dec_NatEq : Dec (@eq nat).
  Proof. constructor. apply Nat.eq_dec. Defined.

  Global Instance Dec_Z : Dec (@eq Z).
  Proof. constructor. apply Z.eq_dec. Defined.

  Global Instance Dec_Q_Qeq : Dec Qeq.
  Proof. constructor. apply Qeq_dec. Defined.

  Global Instance Dec_Qc : Dec (@eq Qc).
  Proof. constructor. apply Qc_eq_dec. Defined.

  Global Instance Dec_R : Dec (@eq R).
  Proof. constructor. apply Req_EM_T. Defined.

  Global Instance Dec_list `{D:Dec} : Dec (eqlistA Aeq).
  Proof.
  constructor. intros l1. induction l1.
    - intros l2. destruct l2; auto.
      right. intro. easy.
    - intros l2. destruct l2.
      + right. intro. easy.
      + destruct (dec a a0), (IHl1 l2); auto.
        * right. intro. inversion H. easy.
        * right. intro. inversion H. easy.
        * right. intro. inversion H. easy.
  Defined.

  Global Instance Dec_dlist `{D:Dec} : Dec (eqlistA (eqlistA Aeq)).
  Proof. constructor. intros. apply dec. Defined.

End Instances.

(** ** Extra Theories *)
Section Dec_theory.

  Context `{D : Dec}.
  Infix "==" := Aeq.

  (** Tips: these theories are useful for R type *)
  
  (** Calculate equality to boolean, with the help of equality decidability *)
  Definition Aeqb (a b : A) : bool := if a ==? b then true else false.
  Infix "=?" := Aeqb.

  (** Aeqb is true iff equal. *)
  Lemma Aeqb_true : forall a b, a =? b = true <-> a == b.
  Proof.
    intros. unfold Aeqb. destruct dec; split; intros; easy.
  Qed.

  (** Aeqb is false iff not equal *)
  Lemma Aeqb_false : forall a b, a =? b = false <-> ~(a == b).
  Proof.
    intros. unfold Aeqb. destruct dec; split; intros; easy.
  Qed.

  Lemma Aeq_reflect : forall a b : A, reflect (a == b) (a =? b).
  Proof.
    intros. unfold Aeqb. destruct (dec a b); constructor; auto.
  Qed.

End Dec_theory.

(** ** Examples *)
Goal forall a b : nat, {a = b} + {a <> b}.
  apply dec. Qed.


(* ######################################################################### *)
(** * Usually used scopes *)

(** Scope for matrix/vector/list element type *)
Declare Scope A_scope.
Delimit Scope A_scope with A.
Open Scope A.

(** Scope for list type *)
Declare Scope list_scope.
Delimit Scope list_scope with list.
Open Scope list.

(** Scope for list list type *)
Declare Scope dlist_scope.
Delimit Scope dlist_scope with dlist.
Open Scope dlist.

(** Scope for matrix type *)
Declare Scope mat_scope.
Delimit Scope mat_scope with mat.
Open Scope mat.

(** Scope for vector type *)
Declare Scope vec_scope.
Delimit Scope vec_scope with vec.
Open Scope vec_scope.

