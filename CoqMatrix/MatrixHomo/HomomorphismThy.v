(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Homomorphism Theory.
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. it is implemented with equivalence equality, not Leibniz equality.
  
  History   :
    2022.07.12  by ZhengPu Shi, remove equivalence relation, only use eq
 *)

From CoqExt Require Export BasicConfig HierarchySetoid.

Generalizable Variable A B C Aeq Beq Ceq Aadd Aopp Amul Ainv.

Section Homo.
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Context `{Equiv_Beq : Equivalence B Beq}.
  
  Context {fa : A -> A -> A} {fb : B -> B -> B}.
  Context {fa_mor : Proper (Aeq ==> Aeq ==> Aeq) fa}.
  Context {fb_mor : Proper (Beq ==> Beq ==> Beq) fb}.
  Infix "+" := fa. Infix "⊕" := fb (at level 50).
  
  (** If <A,+> and <B,⊕> is homomorphism, and + is commutative,
    then ⊕ is commutative too. *)
  Lemma homo_keep_comm : Homomorphism fa fb (Aeq:=Aeq) (Beq:=Beq) -> 
                         Commutative fa Aeq -> Commutative fb Beq.
  Proof.
    intros [(phi & [[Hhomo] [[Hsurj] Hproper]])] [comm].
    constructor. intros b1 b2.
    destruct (Hsurj b1) as (a1 & Ha1).
    destruct (Hsurj b2) as (a2 & Ha2). clear Hsurj.
    rewrite <- Ha1, <- Ha2. rewrite <- !Hhomo. rewrite comm. easy.
  Qed.
  
  (** If <A,+> and <B,⊕> is homomorphism, and + is associative,
    then ⊕ is associative too. *)
  Lemma homo_keep_assoc : Homomorphism fa fb (Aeq:=Aeq) (Beq:=Beq) -> 
                          Associative fa Aeq -> Associative fb Beq.
  Proof.
    intros [(phi & [[Hhomo] [[Hsurj] Hproper]])] [assoc].
    constructor. intros b1 b2 b3.
    destruct (Hsurj b1) as (a1 & Ha1).
    destruct (Hsurj b2) as (a2 & Ha2).
    destruct (Hsurj b3) as (a3 & Ha3). clear Hsurj.
    rewrite <- Ha1, <- Ha2, <- Ha3. rewrite <- !Hhomo. rewrite assoc. easy.
  Qed.

  
  Context {ga : A -> A -> A} {gb : B -> B -> B}.
  Context {ga_mor : Proper (Aeq ==> Aeq ==> Aeq) ga}.
  Context {gb_mor : Proper (Beq ==> Beq ==> Beq) gb}.
  Infix "*" := ga. Infix "⊗" := gb (at level 40).

  (** If <A,+,*>,<B,⊕,⊗> is homomorphism,
    and * is left distributive about + over A,
    then ⊗ is left distributive about ⊕ over B. *)
  Lemma homo_keep_distr_l : Homomorphism2 fa ga fb gb (Aeq:=Aeq) (Beq:=Beq) -> 
                            DistributiveLeft fa ga Aeq -> DistributiveLeft fb gb Beq.
  Proof.
    intros [(phi & [[HhomoA] [[HhomoB] [[Hsurj] Hproper]]])] [distr].
    constructor. intros b1 b2 b3.
    destruct (Hsurj b1) as (a1, Ha1).
    destruct (Hsurj b2) as (a2, Ha2).
    destruct (Hsurj b3) as (a3, Ha3). clear Hsurj.
    rewrite <- Ha1, <- Ha2, <- Ha3.
    rewrite <- HhomoA. rewrite <- HhomoB. rewrite distr.
    rewrite HhomoA. rewrite !HhomoB. easy.
  Qed.
  
  (** If <A,+,*>,<B,⊕,⊗> is homomorphism,
    and * is right distributive about + over A,
    then ⊗ is right distributive about ⊕ over B. *)
  Lemma homo_keep_distr_r : Homomorphism2 fa ga fb gb (Aeq:=Aeq) (Beq:=Beq) -> 
                            DistributiveRight fa ga Aeq -> DistributiveRight fb gb Beq.
  Proof.
    intros [(phi & [[HhomoA] [[HhomoB] [[Hsurj] Hproper]]])] [distr].
    constructor. intros b1 b2 b3.
    destruct (Hsurj b1) as (a1, Ha1).
    destruct (Hsurj b2) as (a2, Ha2).
    destruct (Hsurj b3) as (a3, Ha3). clear Hsurj.
    rewrite <- Ha1, <- Ha2, <- Ha3.
    rewrite <- HhomoA. rewrite <- HhomoB. rewrite distr.
    rewrite HhomoA. rewrite !HhomoB. easy.
  Qed.
    
End Homo.

Section Compose.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Context `{Equiv_Beq : Equivalence B Beq}.
  Context `{Equiv_Ceq : Equivalence C Ceq}.
  
  Context {fa : A -> A -> A} {fb : B -> B -> B} {fc : C -> C -> C}.
  Context {fa_mor : Proper (Aeq ==> Aeq ==> Aeq) fa}.
  Context {fb_mor : Proper (Beq ==> Beq ==> Beq) fb}.
  Context {fc_mor : Proper (Ceq ==> Ceq ==> Ceq) fc}.

  (** Composition of homomorphism mapping is also homomorphism mapping *)
  Lemma homom_comp_imply_homo :
    Homomorphism fa fb (Aeq:=Aeq)(Beq:=Beq) ->
    Homomorphism fb fc (Aeq:=Beq)(Beq:=Ceq) ->
      Homomorphism fa fc (Aeq:=Aeq)(Beq:=Ceq).
  Proof.
  (*   intros. *)
  (*   destruct H as [phi [Hhomo Hsurj]], H0 as [psi [Hhomo' Hsurj']]. *)
  (*   exists (fun a => psi (phi a)). split. *)
  (*   - intros a b. rewrite <- Hhomo'. f_equal. rewrite <- Hhomo. auto. *)
  (*   - intros c. *)
  (*     destruct (Hsurj' c) as [b Hb]. *)
  (*     destruct (Hsurj b) as [a Ha]. *)
  (*     exists a. subst. auto. *)
    (* Qed. *)
  Admitted.
  
End Compose.
