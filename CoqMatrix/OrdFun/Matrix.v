(*
  Copyright 2023 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with a function with index of ordinal type.
  author    : ZhengPu Shi
  date      : 2023.03
  remark    :
  1. ordinal is proposed from mathcomp,
     and can be found in lots of works, such as
     https://www-sop.inria.fr/members/Anders.Mortberg/papers/sasaki-murao.pdf
     
 *)

Require Import List. Import ListNotations.
Require Import BasicConfig.
Require Import NatExt.

(** ** Bounded integers *)
Section ord.
  (** ordinal number of natural number, 0 <= i < n *)
  Inductive ordinal {n : nat} :=
    Ordinal (i : nat) (_ : i <? n).
  
  Notation "''I_' n" := (@ordinal n) (at level 10, n at next level, format "''I_' n").

  (** convert ordinal to nat *)
  Coercion nat_of_ord {n} (o:'I_n) := let '(Ordinal i _) := o in i.
End ord.
Notation "''I_' n" := (@ordinal n) (at level 10, n at next level, format "''I_' n").

Section test.
  (** Nat.ltb是可计算的，所以具体数值时可以自动完成证明 *)
  Example ex_i3_1 : 'I_3 := Ordinal 1 (eq_refl (Nat.ltb _ 3)).
  Example ex_i3_2 : 'I_3 := Ordinal 2 (eq_refl (Nat.ltb _ 3)).
  Check ex_i3_2 < 2.
End test.

(** Get list of all ordinal numbers 'I_n *)
Definition ord_enum (n : nat) : list ('I_n).
  pose (seq 0 n).
  (* refine (map (fun i => Ordinal i _) l). (seq 0 n)). *)
Admitted.

Compute ord_enum 3.

Section ord_props.
  Variable n : nat.
  (* Lemma ltn_ord (i : ordinal) : i < n. Proof. exact: valP i. Qed. *)
  (* Lemma ord_inj : injective nat_of_ord. Proof. exact: val_inj. Qed. *)
End ord_props.

Section vec.
  Context {A : Type} {A0 : A}.
  Definition vec (n : nat) := 'I_n -> A.

  (* Definition l2v (n : nat) (l : list A) := vec n := *)
  (*     match n with *)
  (*       | O -> *)
End vec.

Section mat.
  Context {A : Type}.
  Definition mat (r c : nat) := 'I_r -> 'I_c -> A.
End mat.

Section vec_and_mat.
  (* 一个mat 也是一个vec，不过默认是行向量，每一个元素是一个列向量，
     即，一个mat可以看成是由列向量组成的向量 *)
  Variable m : @mat nat 3 4.
  Check m : vec 3.
End vec_and_mat.

Check ('I_3 -> ('I_2 -> nat)).

(* Definition enum (P : A -> bool) :=  *)
(* Definition enum_mem T (mA : mem_pred _) := filter mA (Finite.enum T). *)
(* Notation enum A := (enum_mem (mem A)). *)
(* Definition pick (T : finType) (P : pred T) := ohead (enum P). *)

(* Variable r c : nat. *)
(* Variable m : mat r c. *)
(* Check map (fun i => m i) (seq 0 r). *)
(* Definition m2l {r c} (m : mat r c) : list (list A) := *)

