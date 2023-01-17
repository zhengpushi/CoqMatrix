(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Isomorphism Theory.
  author    : ZhengPu Shi
  date      : 2022.07
  
  ref:
  1. https://blog.csdn.net/grb819/article/details/111745405
 *)

From CoqExt Require Export BasicConfig HierarchySetoid.

Generalizable Variable A B C Aeq Beq Ceq Aadd Aopp Amul Ainv.


(** * Isomorphism mapping is equivalence relation *)
Section isomor_equiv.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Context `{Equiv_Beq : Equivalence B Beq}.
  Context `{Equiv_Ceq : Equivalence C Ceq}.

  Context {fa : A -> A -> A} {fb : B -> B -> B} {fc : C -> C -> C}.
  Context {fa_mor : Proper (Aeq ==> Aeq ==> Aeq) fa}.
  Context {fb_mor : Proper (Beq ==> Beq ==> Beq) fb}.
  Context {fc_mor : Proper (Ceq ==> Ceq ==> Ceq) fc}.
  
  (** Isomorphism mapping is reflexive *)
  Theorem isomorphism_refl : Isomorphism fa fb (Aeq:=Aeq)(Beq:=Beq) ->
                             Isomorphism fa fb (Aeq:=Aeq)(Beq:=Beq).
  Proof.
    intros. auto.
  Qed.

  (** Isomorphism mapping is symmetric *)
  Theorem isomorphism_sym : Isomorphism fa fb (Aeq:=Aeq)(Beq:=Beq) ->
                            Isomorphism fb fa (Aeq:=Beq)(Beq:=Aeq).
  Proof.
    (* intros [(phi, [Hhomo [[[Hinj] [Hsurj]] Hproper]])]. *)
    intros [(phi, [Hhomo [Hbij Hproper]])].
    constructor.
    exists (proj1_sig (bij_inverse_exist Hbij)).
    unfold bij_inverse_exist.
    destruct Hbij as [[Hinj] [Hsurj]]. simpl.
    destruct constructive_definite_description_setoid as (psi,[HA HB]). simpl.
  Admitted.

  Theorem isomorphism_trans : Isomorphism fa fb (Aeq:=Aeq)(Beq:=Beq) ->
                              Isomorphism fb fc (Aeq:=Beq)(Beq:=Ceq) ->
                              Isomorphism fa fc (Aeq:=Aeq)(Beq:=Ceq).
  Proof.
  Admitted.


End isomor_equiv.


(** * Preserve commutative, associative, cancel, etc. *)
Section isomor_perserve.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Context `{Equiv_Beq : Equivalence B Beq}.
  Context `{Equiv_Ceq : Equivalence C Ceq}.

  Context {fa : A -> A -> A} {fb : B -> B -> B} {fc : C -> C -> C}.
  Context {fa_mor : Proper (Aeq ==> Aeq ==> Aeq) fa}.
  Context {fb_mor : Proper (Beq ==> Beq ==> Beq) fb}.
  Context {fc_mor : Proper (Ceq ==> Ceq ==> Ceq) fc}.

  (** Note that, here is iff, it is strong than the case in homomorphism *)

  
  Theorem isomor_keep_comm : Isomorphism fa fb (Aeq:=Aeq)(Beq:=Beq) ->
                             Commutative fa Aeq <-> Commutative fb Beq.
  Proof.
  Admitted.

  Theorem isomor_keep_assoc : Isomorphism fa fb (Aeq:=Aeq)(Beq:=Beq) ->
                              Associative fa Aeq <-> Associative fb Beq.
  Proof.
  Admitted.

  (* Theorem isomor_keep_cancel_left : forall {A B} (fa : A -> A -> A) *)
  (*                                     (fb : B -> B -> B) (H1 : isomorphism fa fb), *)
  (*     cancel_left fa <-> cancel_left fb. *)
  (* Proof. *)
  (* Admitted. *)

  (* Theorem isomor_keep_cancel_right : forall {A B} (fa : A -> A -> A) *)
  (*                                      (fb : B -> B -> B) (H1 : isomorphism fa fb), *)
  (*     cancel_right fa <-> cancel_right fb. *)
  (* Proof. *)
  (* Admitted. *)

  (* Theorem isomor_keep_distr_left : forall {A B} (fa ga : A -> A -> A) *)
  (*                                    (fb gb : B -> B -> B) (H1 : isomorphism2 fa ga fb gb), *)
  (*     distributive_left fa ga <-> distributive_left fb gb. *)
  (* Proof. *)
  (* Admitted. *)

  (* Theorem isomor_keep_distr_right : forall {A B} (fa ga : A -> A -> A) *)
  (*                                     (fb gb : B -> B -> B) (H1 : isomorphism2 fa ga fb gb), *)
  (*     distributive_right fa ga <-> distributive_right fb gb. *)
  (* Proof. *)
  (* Admitted. *)

End isomor_perserve.

