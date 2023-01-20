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
Require Export Coq.Bool.Bool.             (* reflect *)
Require Export Ring.                      (* ring *)
Require Export Field.                     (* field *)

Require Export Coq.Logic.Classical.
Require Export Coq.Logic.FunctionalExtensionality.


(* ######################################################################### *)
(** * Reserved Notations *)

(** Reserved Notations, to keep same precedence and associativity *)
Reserved Infix    "=="      (at level 70, no associativity).
Reserved Notation "a != b"  (at level 70, no associativity).
Reserved Infix    "=?"      (at level 70, no associativity).
Reserved Infix    "+"       (at level 50, left associativity).
Reserved Infix    "-"       (at level 50, left associativity).
Reserved Infix    "*"       (at level 40, left associativity).
Reserved Infix    "/"       (at level 40, left associativity).
Reserved Infix    "c*"      (at level 40, left associativity).
Reserved Infix    "*c"      (at level 40, left associativity).
Reserved Infix    "\o"      (at level 50, no associativity).
Reserved Notation "- a"     (at level 35, right associativity).
Reserved Notation "/ a"     (at level 35, right associativity).
Reserved Notation "a \T"    (at level 34, left associativity).

(* this level is consistent with Mathcomp.ssreflect.ssrnotations.v *)
Reserved Notation "v .[ i ]"   (at level 2, left associativity, format "v .[ i ]").
Reserved Notation "m @ i # j"  (at level 20, i at next level).
Reserved Notation "v @ m"      (at level 20).



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
(** * General propeties of algebraic structures *)


(** Bidirection form of functional extensionality (unary function) *)
Lemma fun_eq_iff_forall_eq : forall A B (f g : A -> B),
    (fun i => f i) = (fun i => g i) <-> forall i, f i = g i.
Proof.
  intros. split; intros.
  - (* We can not use functional_extensionality here *)
    (* Although these proofs are simple, but it is very cumbersome.
       I hope to get some concise way *)
    remember (fun (f:A->B) (i:A) => f i) as F eqn:EqF.
    replace (fun i => f i) with (F f) in H by (rewrite EqF; auto).
    replace (fun i => g i) with (F g) in H by (rewrite EqF; auto).
    replace (f i) with (F f i) by (rewrite EqF; auto).
    replace (g i) with (F g i) by (rewrite EqF; auto).
    rewrite H. auto.
  - extensionality i. auto.
Qed.

(** Another form of functional extensionality (binary function) *)
Lemma fun_eq_iff_forall_eq2 : forall A B C (f g : A -> B -> C),
    (fun i j => f i j) = (fun i j => g i j) <-> forall i j, f i j = g i j.
Proof.
  intros. split; intros.
  - rewrite (fun_eq_iff_forall_eq) in H. rewrite H. auto. 
  - extensionality i. extensionality j. auto.
Qed.


Section general_props.

  Context {A B : Type}.
  Variable fa ga : A -> A -> A.
  Infix "+" := fa.
  Infix "*" := ga.
  Variable fb : B -> B -> B.
  Infix "⊕" := fb (at level 50).

End general_props.

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

