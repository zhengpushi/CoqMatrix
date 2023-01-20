(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : Extension of function
  author      : ZhengPu Shi
  date        : 2022.08
  
*)


Require Export List.
Import ListNotations.

Require Export FunctionalExtensionality.


(** A short name of "functional_extensionality" *)
(* Definition fun_eq {A B} := @functional_extensionality A B. *)
Ltac fun_eq := apply functional_extensionality.


(** execute an unary function multiply times with the initial value. 
    Similiar to fold.
    nexec a0 f n := f (f ... (f x) ...)
*)
Fixpoint nexec {A:Type} (a0:A) (f:A->A) (n:nat) : A :=
  match n with
  | O => a0
  | S n' => nexec (f a0) f n'
  end.

(* Compute nexec 0 S 3. *)


(** nexec rewriting *)
Lemma nexec_rw : forall (A:Type) (a:A) (f:A->A) (n:nat),
  nexec (f a) f n = f (nexec a f n).
Proof.
  intros. revert a. induction n; intros; simpl; auto. 
Qed.

(** Linear property of nexec *)
Lemma nexec_linear : forall (A:Type) (a:A) (f:A->A) (g:A->A) (n:nat)
  (H: forall x:A, f (g x) = g (f x)),
  nexec (g a) f n = g (nexec a f n).
Proof.
  intros. revert a. induction n; intros; simpl; auto. rewrite H,IHn. auto.
Qed.

(** map f (seq 0 (S n)) = map f (seq 0 n) + f n
    So, a0 + f 0 + f 1 + ... + f n = (a0 + f 0 + ... + f (n-1)) + f n *)
Lemma fold_map_seq : forall (A:Type) (f:nat->A) (g:A->A->A) (a0:A) (n:nat),
  fold_left g (map f (seq 0 (S n))) a0 = g (fold_left g (map f (seq 0 n)) a0) (f n).
Proof.
  intros.
  rewrite seq_S.  (* seq start (S len) = (seq start len ++ [(start + len)]) *)
  rewrite map_app. (* map f (l ++ l') = (map f l ++ map f l') *)
  rewrite fold_left_app. (* 
    fold_left f (l ++ l') i = fold_left f l' (fold_left f l i) *)
  simpl. auto.
Qed.

