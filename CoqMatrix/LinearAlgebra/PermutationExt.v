(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension for permutation, especially for computable permutation.
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
  1. compute permutation of a list, such as 
     perm [a;b;c] =>
     [[a;b;c]; [a;c;b]; [b;a;c]; [b;c;a]; [c;a;b]; [c;b;a]]
*)

Require Import SetoidListExt.


(* ######################################################################### *)
(** * Computable permutation *)

Section perm.
  Context {A : Type} (A0 : A).
  
  (** Get k-th element and remaining elements from a list *)
  Fixpoint pick (l : list A) (k : nat) : A * list A :=
    match k with
    | 0 => (hd A0 l, tl l)
    | S k' =>
        match l with
        | [] => (A0, [])
        | x :: l' =>
            let (a,l0) := pick l' k' in
            (a, [x] ++ l0)
        end
    end.

  Section test.
    Variable a b c : A.
    Let l := [a;b;c].
    (* Compute pick l 0.     (* = (a, [b; c]) *) *)
    (* Compute pick l 1.     (* = (b, [a; c]) *) *)
    (* Compute pick l 2.     (* = (c, [a; b]) *) *)
    (* Compute pick l 3.     (* = (A0, [a; b; c]) *) *)
  End test.

  (** Get permutation of a list with a special level number *)
  Fixpoint perm_aux (n : nat) (l : list A) : list (list A) :=
    match n with
    | 0 => [[]]
    | S n' =>
        let d1 := map (fun i => pick l i) (seq 0 n) in
        let d2 :=
          map (fun k : A * list A =>
                 let (x, lx) := k in
                 let d3 := perm_aux n' lx in
                 map (fun l1 => [x] ++ l1) d3) d1 in
        concat d2
    end.

  Section test.
    Variable a b c : A.
    Let l := [a;b;c].
    (* Compute perm_aux 0 l.     (* = [[]] *) *)
    (* Compute perm_aux 1 l.     (* = [[a]] *) *)
    (* Compute perm_aux 2 l.     (* = [[a; b]; [b; a]] *) *)
    (* Compute perm_aux 3 l.     (* = [[a; b; c]; [a; c; b]; [b; a; c]; [b; c; a];  *)
    (*                              [c; a; b]; [c; b; a]] *) *)
  End test.

  (** Get permutation of a list *)
  Definition perm (l : list A) : list (list A) := perm_aux (length l) l.

  (** Length of permutation *)
  Definition Pn (l : list A) := length (perm l).

  (** Pn of cons. 
      Example: Pn [a;b;c;d] = 4 * Pn [a;b;c] *)
  Lemma Pn_cons : forall (a : A) (l : list A), Pn (a :: l) = (length (a :: l)) * (Pn l).
  Proof.
    intros. simpl. unfold Pn.
    unfold perm. simpl. rewrite app_length. rewrite map_length. f_equal.
    rewrite List.map_map.
    rewrite concat_length.
    rewrite List.map_map.
    Admitted.

  (** Length of permutation equal to the factorial of the length *)
  Lemma Pn_eq : forall l, Pn l = fact (length l).
  Proof.
    induction l; simpl; auto.
    rewrite Pn_cons. rewrite IHl. simpl. auto.
  Qed.

  (** The inverse number of a permutation *)
  (* Definition inv_no             (*  *) *)

  
End perm.

(* Compute perm 0 [1;2]. *)
(* Compute perm 0 [1;2;3]. *)
(* Compute perm 0 [1;2;3;4]. *)
(* Compute Pn _ [1;2;3]. *)
(* Compute Pn _ [1;2;3;4]. *)
(* Compute fact 4. *)



