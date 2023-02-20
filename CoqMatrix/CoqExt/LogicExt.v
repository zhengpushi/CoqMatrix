(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : Extension of Logic
  author      : ZhengPu Shi
  date        : 2023.02
  
*)


(** Good exercises for logic *)
Section exercise_forall_exist_not.

  (** These lemmas needn't axiom *)

  Let all_not_not_ex:
    forall (U : Type) (P : U -> Prop), (forall n : U, ~ P n) -> ~ (exists n : U, P n).
  Proof. intros. intro. destruct H0. specialize (H x). easy. Qed.
  
  Let ex_not_not_all: forall (U : Type) (P : U -> Prop),
      (exists n : U, ~ P n) -> ~ (forall n : U, P n).
  Proof. intros. intro. destruct H. specialize (H0 x). easy. Qed.

  (** These lemmas need axiom in Classic Logic *)

  Let reverse_proof : forall P Q : Prop, (~Q -> ~P) -> (P -> Q).
  Proof. Abort.
  
  Let not_ex_not_all:
    forall (U : Type) (P : U -> Prop), ~ (exists n : U, ~ P n) -> forall n : U, P n.
  Proof. Abort.

  Let not_ex_all_not:
    forall (U : Type) (P : U -> Prop), ~ (exists n : U, P n) -> forall n : U, ~ P n.
  Proof. Abort.
  
  Let not_all_ex_not: forall (U : Type) (P : U -> Prop),
      ~ (forall n : U, P n) -> exists n : U, ~ P n.
  Proof. Abort.

  Let not_all_not_ex: forall (U : Type) (P : U -> Prop),
      ~ (forall n : U, ~ P n) -> exists n : U, P n.
  Proof. Abort.
  
End exercise_forall_exist_not.
