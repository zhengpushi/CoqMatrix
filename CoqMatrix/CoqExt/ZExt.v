(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Z.
  author    : ZhengPu Shi
  date      : 2022.04
*)

Require Export BasicConfig.

Require Export ZArith.
Open Scope Z.


(* ######################################################################### *)
(** * Conversion between Z and other types *)
Definition nat2Z (n : nat) : Z := Z.of_nat n.
Definition Z2nat (z : Z) : nat := Z.to_nat z.


(* ######################################################################### *)
(** * Properties for Zeqb and Zeq *)

Definition Zeqb := Z.eqb.

Infix     "=?"          := Zeqb           : Z_scope.

(** Reflection of (=) and (=?) *)
Lemma Zeqb_true_iff : forall x y, x =? y = true <-> x = y.
Proof.
  apply Z.eqb_eq.
Qed.

Lemma Zeqb_false_iff : forall x y, x =? y = false <-> x <> y.
Proof.
  apply Z.eqb_neq.
Qed.


(* ######################################################################### *)
(** * Other properties *)

(** Boolean equality of Zadd satisfy right cancelling rule *)
Lemma Zadd_eqb_cancel_r : forall (z1 z2 a : Z),
  (z1 + a =? z2 + a)%Z = (z1 =? z2)%Z.
Proof.
  intros.
  remember (z1 =? z2)%Z as b1 eqn : H1.
  remember (z1 + a =? z2 + a)%Z as b2 eqn : H2.
  destruct b1,b2; auto.
  - apply eq_sym in H1,H2. apply Z.eqb_eq in H1. apply Z.eqb_neq in H2.
    subst. auto.
  - apply eq_sym in H1,H2. apply Z.eqb_neq in H1. apply Z.eqb_eq in H2.
    apply Z.add_cancel_r in H2. apply H1 in H2. easy.
Qed.
