(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Type of Matrix Element
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. This is an inteface of different matrix implementation.
  2. Element type is orgainized to several levels
     (1) ElementType
         EqElementType, Aeq is eq.
     (2) DecidableElementType, based on ElementType.
     (3) RingElementType, based on ElementType.
     (4) FieldElementType, based on RingEementType.
     (5) DecidableFieldElementType, based on FieldElementType, and 
         satisfy Decidable relation.
*)

Require Export BasicConfig NatExt ZExt QExt QcExt RExt HierarchySetoid.



(* ######################################################################### *)
(** * Base type *)

(** ** Type of base type *)
Module Type BaseType.
  Parameter A : Type.
End BaseType.

(** ** Instances *)

Module BaseTypeNat <: BaseType.
  Definition A := nat.
End BaseTypeNat.

Module BaseTypeZ <: BaseType.
  Import ZArith.
  Definition A := Z.
End BaseTypeZ.

Module BaseTypeQ <: BaseType.
  Import QArith.
  Definition A := Q.
End BaseTypeQ.

Module BaseTypeQc <: BaseType.
  Import Qcanon.
  Definition A := Qc.
End BaseTypeQc.

Module BaseTypeR <: BaseType.
  Import Reals.
  Definition A := R.
End BaseTypeR.

Module BaseTypeFun (A B : BaseType) <: BaseType.
  Import Reals.
  Definition A := A.A -> B.A.
End BaseTypeFun.


(* ######################################################################### *)
(** * Element with setoid equality *)

(** ** Type of element *)
Module Type ElementType <: BaseType.
  Parameter A : Type.
  Parameter Aeq : relation A.
  Parameter A0 : A.

  Global Infix "==" := Aeq : A_scope.
  
  Axiom Equiv_Aeq : Equivalence Aeq.
  Global Existing Instance Equiv_Aeq.
End ElementType.


(** Type of element which specify the Aeq is eq, used in lots of cases *)
Module Type EqElementType (B : BaseType)
<: BaseType
  := ElementType
     with Definition A := B.A
     with Definition Aeq := @eq B.A.


(** ** Instances *)
Module ElementTypeNat <: EqElementType BaseTypeNat.
  Export Arith.
  Open Scope nat.

  Definition A : Type := nat.
  Definition Aeq : relation A := eq.
  Definition A0 : A := 0.

  Infix "==" := Aeq : A_scope.

  Lemma Equiv_Aeq : Equivalence Aeq.
  Proof.
    apply eq_equivalence.
  Qed.
End ElementTypeNat.

Module ElementTypeZ <: EqElementType BaseTypeZ.
  Export ZArith.
  Open Scope Z.
  
  Definition A : Type := Z.
  Definition Aeq : relation A := eq.
  Definition A0 : A := 0.

  Infix "==" := Aeq : A_scope.

  Lemma Equiv_Aeq : Equivalence Aeq.
  Proof.
    apply eq_equivalence.
  Qed.
End ElementTypeZ.

(** Tips, this module cannot be a EqElementType *)
Module ElementTypeQ <: ElementType.
  Export QArith.
  Open Scope Q.
  
  Definition A : Type := Q.
  Definition Aeq : relation A := Qeq.
  Definition A0 : A := 0.

  Infix "==" := Aeq : A_scope.

  Lemma Equiv_Aeq : Equivalence Aeq.
  Proof.
    apply Q_Setoid.
  Qed.
End ElementTypeQ.

Module ElementTypeQc <: EqElementType BaseTypeQc.
  Export Qcanon.
  Open Scope Qc.
  
  Definition A : Type := Qc.
  Definition Aeq : relation A := eq.
  Definition A0 : A := 0.

  Infix "==" := Aeq : A_scope.

  Lemma Equiv_Aeq : Equivalence Aeq.
  Proof.
    apply eq_equivalence.
  Qed.
End ElementTypeQc.

Module ElementTypeR <: EqElementType BaseTypeR.
  Export Reals.
  Open Scope R.

  Definition A : Type := R.
  Definition Aeq : relation A := eq.
  Definition A0 : A := 0%R.

  Infix "==" := Aeq : A_scope.

  Lemma Equiv_Aeq : Equivalence Aeq.
  Proof.
    apply eq_equivalence.
  Qed.
End ElementTypeR.

Module ElementTypeFun (I O : ElementType) <: ElementType.
  Definition A : Type := {f : I.A -> O.A | Proper (I.Aeq ==> O.Aeq) f}.
  Definition Aeq : relation A :=
    fun (f g : A) => forall (a : I.A),
        O.Aeq (proj1_sig f a) (proj1_sig g a).
  Infix "=I=" := I.Aeq (at level 20).
  Infix "=O=" := O.Aeq (at level 20).
  Infix "==" := Aeq : A_scope.
  
  Definition A0 : A.
    refine (exist _ (fun _ => O.A0) _).
    unfold Proper, respectful. intros. destruct (O.Equiv_Aeq). reflexivity.
  Defined.
  Lemma Equiv_Aeq : Equivalence Aeq.
  Proof.
    destruct (I.Equiv_Aeq), (O.Equiv_Aeq).
    constructor; cbv; intros; try easy.
    destruct x.
    specialize (H a). specialize (H0 a).
    rewrite H0 in H. auto.
  Qed.
End ElementTypeFun.

Module ElementType_Test.
  Import Reals.
  Import FunctionalExtensionality.
  Open Scope R.
  
  Module Import ElementTypeFunEx1 := ElementTypeFun ElementTypeNat ElementTypeR.
  Definition f : A.
    refine (exist _ (fun i => match i with 0%nat => 1%R | 1%nat => 2%R | _ => 1%R end) _).
    unfold Proper, respectful. intros. rewrite H. reflexivity.
  Defined.
  Definition g : A.
    refine (exist _ (fun i => match i with 1%nat => 2%R | _ => 1%R end) _ ).
    unfold Proper, respectful. intros. rewrite H. reflexivity.
  Defined.

  Goal f == g.
  Proof.
    cbv. intros. auto.
  Qed.
End ElementType_Test.


(* ######################################################################### *)
(** * Element with decidable relation *)

(** ** Type of element with decidable relation *)
Module Type DecidableElementType <: ElementType.
  Include ElementType.

  Axiom Dec_Aeq : Decidable Aeq.
End DecidableElementType.

Module Type EqDecidableElementType (B : BaseType)
<: EqElementType B
  := DecidableElementType
     with Definition A := B.A
     with Definition Aeq := @eq B.A.


(** ** Instances *)
Module DecidableElementTypeNat
<: DecidableElementType.
  Include ElementTypeNat.

  Lemma Dec_Aeq : Decidable Aeq.
  Proof.
    constructor. apply Nat.eq_dec.
  Qed.
End DecidableElementTypeNat.

Module DecidableElementTypeZ
<: DecidableElementType.
  Include ElementTypeZ.

  Lemma Dec_Aeq : Decidable Aeq.
  Proof.
    constructor. apply Z.eq_dec.
  Qed.
End DecidableElementTypeZ.

Module DecidableElementTypeQ
<: DecidableElementType.
  Include ElementTypeQ.

  Lemma Dec_Aeq : Decidable Aeq.
  Proof.
    constructor. apply Qeq_dec.
  Qed.
End DecidableElementTypeQ.

Module DecidableElementTypeQc
<: DecidableElementType.
  Include ElementTypeQc.

  Lemma Dec_Aeq : Decidable Aeq.
  Proof.
    constructor. apply Qc_eq_dec.
  Qed.
End DecidableElementTypeQc.

Module DecidableElementTypeR
<: DecidableElementType.
  Include ElementTypeR.

  Lemma Dec_Aeq : Decidable Aeq.
  Proof.
    constructor. apply Req_EM_T.
  Qed.
End DecidableElementTypeR.

Module DecidableElementTypeFun (I O : DecidableElementType)
<: DecidableElementType.
  Include (ElementTypeFun I O).
  
  Lemma Dec_Aeq : Decidable Aeq.
  Proof.
    constructor.
    intros. destruct a as [a Ha], b as [b Hb].
  Admitted.

End DecidableElementTypeFun.



(* ######################################################################### *)
(** * Element with ring structure *)

(** ** Type of Element with ring structure *)
Module Type RingElementType <: ElementType.
  Include ElementType.
  Open Scope A_scope.

  Parameter A1 : A.
  Parameter Aadd Amul : A -> A -> A.
  Parameter Aopp : A -> A.

  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Global Infix "+" := Aadd : A_scope.
  Global Infix "*" := Amul : A_scope.
  Global Notation "- a" := (Aopp a) : A_scope.
  Global Infix "-" := Asub : A_scope.

  (** Use these lemmas, we can replace "Add Morphism ..." with "Existing Morphism" *)
  Axiom Aadd_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Aadd).
  Axiom Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Axiom Amul_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Amul).

  Global Existing Instance Aadd_aeq_mor.
  Global Existing Instance Aopp_aeq_mor.
  Global Existing Instance Amul_aeq_mor.

  Axiom Ring_thy : ring_theory A0 A1 Aadd Amul Asub Aopp Aeq.

  (** A Group structure can be derived from the context *)
  Axiom AGroup_inst : AGroup Aadd A0 Aopp Aeq.
  Global Existing Instance AGroup_inst.

  (** A Ring structure can be derived from the context *)
  Axiom Ring_inst : Ring Aadd A0 Aopp Amul A1 Aeq.
  Global Existing Instance Ring_inst.

End RingElementType.

Module Type EqRingElementType (B : BaseType)
<: EqElementType B
  := RingElementType
     with Definition A := B.A
     with Definition Aeq := @eq B.A.


(** ** Instances *)

Module RingElementTypeZ
<: RingElementType.
  Include ElementTypeZ.

  Definition A1 : A := 1.
  Definition Aadd := Zplus.
  Definition Aopp := Z.opp.
  Definition Amul := Zmult.

  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Global Infix "+" := Aadd : A_scope.
  Global Infix "*" := Amul : A_scope.
  Global Notation "- a" := (Aopp a) : A_scope.
  Global Infix "-" := Asub : A_scope.

  Lemma Aadd_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Aadd).
  Proof.
    unfold Proper, respectful. intros. rewrite H,H0. easy.
  Qed.

  Lemma Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Proof.
    unfold Proper, respectful. intros. rewrite H. easy.
  Qed.

  Lemma Amul_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Amul).
  Proof.
    unfold Proper, respectful. intros. rewrite H,H0. easy.
  Qed.
  
  Lemma Ring_thy : ring_theory A0 A1 Aadd Amul Asub Aopp Aeq.
  Proof.
    constructor; intros;
      unfold A,Aeq,Aadd,Aopp,Amul,A0,A1;
      unfold ElementTypeQ.Aeq,ElementTypeQ.A0,ElementTypeQ.A;
      auto with zarith.
  Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  Lemma AGroup_inst : AGroup Aadd A0 Aopp Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor; try apply Equiv_Aeq;
    unfold Aadd,Aeq,Aopp,A0,A; ring.
  Qed.

  Lemma Ring_inst : Ring Aadd A0 Aopp Amul A1 Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor, Amul_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Amul,A0,A1,A; ring.
  Qed.
  
End RingElementTypeZ.

Module RingElementTypeQ
<: RingElementType.
  Include ElementTypeQ.
  
  Definition A1 : A := 1.
  Definition Aadd := Qplus.
  Definition Aopp := Qopp.
  Definition Amul := Qmult.

  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Global Infix "+" := Aadd : A_scope.
  Global Infix "*" := Amul : A_scope.
  Global Notation "- a" := (Aopp a) : A_scope.
  Global Infix "-" := Asub : A_scope.

  Lemma Aadd_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Aadd).
  Proof.
    unfold Proper, respectful. intros. rewrite H,H0. easy.
  Qed.

  Lemma Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Proof.
    unfold Proper, respectful. intros. rewrite H. easy.
  Qed.

  Lemma Amul_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Amul).
  Proof.
    unfold Proper, respectful. intros. rewrite H,H0. easy.
  Qed.
  
  Lemma Ring_thy : ring_theory A0 A1 Aadd Amul Asub Aopp Aeq.
  Proof.
    constructor; intros;
      unfold A,Aeq,Aadd,Aopp,Amul,A0,A1;
      unfold ElementTypeQ.Aeq,ElementTypeQ.A0,ElementTypeQ.A;
      try ring.
  Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  Lemma AGroup_inst : AGroup Aadd A0 Aopp Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor; try apply Equiv_Aeq;
    unfold Aadd,Aeq,Aopp,A0,A; ring.
  Qed.

  Lemma Ring_inst : Ring Aadd A0 Aopp Amul A1 Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor, Amul_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Amul,A0,A1,A; ring.
  Qed.
  
End RingElementTypeQ.

Module RingElementTypeQc
<: RingElementType.
  Include ElementTypeQc.

  Definition A1 : A := 1.
  Definition Aadd := Qcplus.
  Definition Aopp := Qcopp.
  Definition Amul := Qcmult.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Global Infix "+" := Aadd : A_scope.
  Global Infix "*" := Amul : A_scope.
  Global Notation "- a" := (Aopp a) : A_scope.
  Global Infix "-" := Asub : A_scope.

  Lemma Aadd_aeq_mor : Proper (Aeq  ==> Aeq ==> Aeq) (Aadd).
  Proof.
    unfold Proper, respectful. intros. rewrite H,H0. easy.
  Qed.

  Lemma Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Proof.
    unfold Proper, respectful. intros. rewrite H. easy.
  Qed.

  Lemma Amul_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Amul).
  Proof.
    unfold Proper, respectful. intros. rewrite H,H0. easy.
  Qed.
  
  Lemma Ring_thy : ring_theory A0 A1 Aadd Amul Asub Aopp Aeq.
  Proof.
    constructor; intros;
      unfold A,Aeq,Aadd,Aopp,Amul,A0,A1;
      unfold ElementTypeQc.Aeq,ElementTypeQc.A0,ElementTypeQc.A;
      try ring.
  Qed.

  Add Ring Ring_thy_inst : Ring_thy.

  Lemma AGroup_inst : AGroup Aadd A0 Aopp Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,A0,A; ring.
  Qed.

  Lemma Ring_inst : Ring Aadd A0 Aopp Amul A1 Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor, Amul_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Amul,A0,A1,A; ring.
  Qed.

End RingElementTypeQc.

Module RingElementTypeR
<: RingElementType.
  Include ElementTypeR.
  
  Definition A1 : A := 1.
  Definition Aadd := Rplus.
  Definition Aopp := Ropp.
  Definition Amul := Rmult.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Global Infix "+" := Aadd : A_scope.
  Global Infix "*" := Amul : A_scope.
  Global Notation "- a" := (Aopp a) : A_scope.
  Global Infix "-" := Asub : A_scope.

  Lemma Aadd_aeq_mor : Proper (Aeq  ==> Aeq ==> Aeq) (Aadd).
  Proof.
    unfold Proper, respectful. intros. rewrite H,H0. easy.
  Qed.

  Lemma Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Proof.
    unfold Proper, respectful. intros. rewrite H. easy.
  Qed.

  Lemma Amul_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) (Amul).
  Proof.
    unfold Proper, respectful. intros. rewrite H,H0. easy.
  Qed.

  Lemma Ring_thy : ring_theory A0 A1 Aadd Amul Asub Aopp Aeq.
  Proof.
    constructor; intros;
      unfold A,Aeq,Aadd,Aopp,Amul,A0,A1;
      unfold ElementTypeR.Aeq,ElementTypeR.A0,ElementTypeR.A;
      try ring.
  Qed.
  
  Add Ring Ring_thy_inst : Ring_thy.

  Lemma AGroup_inst : AGroup Aadd A0 Aopp Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,A0,A; ring.
  Qed.

  Lemma Ring_inst : Ring Aadd A0 Aopp Amul A1 Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor, Amul_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Amul,A0,A1,A; ring.
  Qed.

End RingElementTypeR.

Module RingElementTypeFun (I O : RingElementType) <: RingElementType.
  Include (ElementTypeFun I O).

  Definition A1 : A.
    refine (exist _ (fun _ => O.A1) _).
    unfold Proper, respectful. intros. destruct (O.Equiv_Aeq). reflexivity.
  Defined.

  Definition Aadd : A -> A -> A.
    cbv. intros [f Pf] [g Pg].
    refine (exist _ (fun x : I.A => O.Aadd (f x) (g x)) _).
    intros.
    pose proof (O.Aadd_aeq_mor). apply H0. apply Pf; easy. apply Pg; easy.
  Defined.
    
  Definition Aopp : A -> A.
    cbv. intros [f Pf].
    refine (exist _ (fun x : I.A => O.Aopp (f x)) _).
    intros.
    pose proof (O.Aopp_aeq_mor). apply H0. apply Pf; easy.
  Defined.

  Definition Amul : A -> A -> A.
    cbv. intros [f Pf] [g Pg].
    refine (exist _ (fun x : I.A => O.Amul (f x) (g x)) _).
    intros.
    pose proof (O.Amul_aeq_mor). apply H0. apply Pf; easy. apply Pg; easy.
  Defined.

  Notation Asub := (fun x y => Aadd x (Aopp y)).

  Lemma Aadd_aeq_mor : Proper (Aeq  ==> Aeq ==> Aeq) (Aadd).
  Proof.
    unfold Proper, respectful.
    intros [x Px] [y Py] H1 [x0 Px0] [y0 Py0] H2.
    cbv in *. intros. apply O.Aadd_aeq_mor; auto.
  Qed.

  Lemma Aopp_aeq_mor : Proper (Aeq ==> Aeq) (Aopp).
  Proof.
    unfold Proper, respectful. intros [x Px] [y Py] H1.
    cbv in *. intros. apply O.Aopp_aeq_mor; auto.
  Qed.

  Lemma Amul_aeq_mor : Proper (Aeq  ==> Aeq ==> Aeq) (Amul).
  Proof.
    unfold Proper, respectful. intros [x Px] [y Py] H1 [x0 Px0] [y0 Py0] H2.
    cbv in *. intros. apply O.Amul_aeq_mor; auto.
  Qed.

  Lemma Ring_thy : ring_theory A0 A1 Aadd Amul Asub Aopp Aeq.
  Proof.
    destruct (O.Ring_thy).
    constructor; intros; cbv; intros;
      repeat match goal with | x:A |- _ => destruct x end; auto.
  Qed.

  Lemma AGroup_inst : AGroup Aadd A0 Aopp Aeq.
  Proof.
    Add Ring Ring_thy_inst_o : O.Ring_thy.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,A0,A;
      repeat match goal with a : ?A |- _ => destruct a end; intros; simpl; ring.
  Qed.

  Lemma Ring_inst : Ring Aadd A0 Aopp Amul A1 Aeq.
  Proof.
    repeat constructor; intros;
      auto using Aadd_aeq_mor, Aopp_aeq_mor, Amul_aeq_mor; try apply Equiv_Aeq;
      unfold Aadd,Aeq,Aopp,Amul,A0,A1,A;
      repeat match goal with a : ?A |- _ => destruct a end; intros; simpl; ring.
  Qed.

End RingElementTypeFun.


Module RingElementTypeTest.
  Import FunctionalExtensionality.
  Import RingElementTypeQ.
  Import RingElementTypeR.
  
  Module Import RingElementTypeFunEx1 :=
    RingElementTypeFun RingElementTypeQ RingElementTypeR.
  Definition f : A.
    refine (exist _ (fun i:Q => Q2R i + R1) _).
    unfold Proper, respectful. intros. rewrite H. easy.
  Defined.

  Definition g : A.
    refine (exist _ (fun i:Q => Q2R (i+1)) _).
    unfold Proper, respectful. intros. rewrite H. easy.
  Defined.

  Goal (f == g)%A.
  Proof.
    unfold f,g,Aeq. hnf. cbn. intros. rewrite Qreals.Q2R_plus.
    hnf. f_equal. cbv. auto with real.
  Qed.
  
End RingElementTypeTest.



(* ######################################################################### *)
(** * Element with field structure *)

(** ** Type of Element with field structure *)

Module Type FieldElementType <: RingElementType.
  Include RingElementType.
  Open Scope A_scope.

  Parameter Ainv : A -> A.

  Notation Adiv := (fun x y => Amul x (Ainv y)).
  Notation "/ a" := (Ainv a) : A_scope.
  Infix "/" := Adiv : A_scope.

  Axiom Ainv_aeq_mor : Proper (Aeq ==> Aeq) Ainv.
  Global Existing Instance Ainv_aeq_mor.

  (** 1 <> 0. *)
  Axiom A1_neq_A0 : ~(A1 == A0)%A.
  
  Axiom Field_thy: field_theory A0 A1 Aadd Amul Asub Aopp Adiv Ainv Aeq.
  (* Add Field Field_thy_inst : Field_thy. *)

  (** A Field structure can be derived from the context *)

  Axiom Field_inst : Field Aadd A0 Aopp Amul A1 Ainv Aeq.
  Global Existing Instance Field_inst.

End FieldElementType.


(** ** Instances *)

Module FieldElementTypeQ <: FieldElementType.
  Include RingElementTypeQ.

  Definition Ainv := Qinv.

  Notation Adiv := (fun x y => Amul x (Ainv y)).

  Lemma Ainv_aeq_mor : Proper (Aeq ==> Aeq) Ainv.
  Proof.
    unfold Proper, respectful. intros. rewrite H. easy.
  Qed.

  Lemma A1_neq_A0 : ~(A1 == A0)%A.
  Proof.
    intro. cbv in *. inv H.
  Qed.
    
  Lemma Field_thy: field_theory A0 A1 Aadd Amul Asub Aopp Adiv Ainv Aeq.
  Proof.
    constructor; intros; try easy.
    apply Ring_thy.
    unfold Amul,Ainv,A1,Aeq. unfold ElementTypeQ.Aeq. field. auto.
  Qed.

  Add Field Field_thy_inst : Field_thy.
  
  Lemma Field_inst : Field Aadd A0 Aopp Amul A1 Ainv Aeq.
  Proof.
    constructor. apply Ring_inst.
    intros. unfold Amul,Ainv,Aeq,A1,A. field. auto.
    apply A1_neq_A0.
    apply Ainv_aeq_mor.
  Qed.

End FieldElementTypeQ.

Module FieldElementTypeQc
<: FieldElementType.
  Include RingElementTypeQc.

  Definition Ainv := Qcinv.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  Lemma Ainv_aeq_mor : Proper (Aeq ==> Aeq) Ainv.
  Proof.
    unfold Proper, respectful. intros. rewrite H. easy.
  Qed.

  Lemma A1_neq_A0 : ~(A1 == A0)%A.
  Proof.
    intro. cbv in *. inv H.
  Qed.
  
  Lemma Field_thy: field_theory A0 A1 Aadd Amul Asub Aopp Adiv Ainv Aeq.
  Proof.
    constructor; intros; try easy.
    apply Ring_thy.
    unfold Amul,Ainv,A1,Aeq. unfold ElementTypeQc.Aeq,ElementTypeQc.A. field. auto.
  Qed.

  (* Bug: when publish the project to opam, CI report error in ocaml4.07.1 as follows,

Error: Illegal application: 
The term "@fieldAinvProper" of type
 "forall (A : Type) (Aadd : A -> A -> A) (A0 : A) (Aopp : A -> A) (Amul : A -> A -> A) 
    (A1 : A) (Ainv : A -> A) (Aeq : A -> A -> Prop),
  Field Aadd A0 Aopp Amul A1 Ainv Aeq -> Proper (Aeq ==> Aeq) Ainv"
cannot be applied to the terms
 "A" : "Type"
 "Qcplus" : "Qc -> Qc -> Qc"
 "Q2Qc 0" : "Qc"
 "Qcopp" : "Qc -> Qc"
 "Qcmult" : "Qc -> Qc -> Qc"
 "1" : "Qc"
 "Ainv" : "Qc -> Qc"
 "Aeq" : "relation A"
 "Field_Qc" : "Field Qcplus (Q2Qc 0) Qcopp Qcmult 1 Qcinv eq"
The 1st term has type "Type@{A.u0}" which should be coercible to "Type@{Field.u0}".
    
    But I don't know why?
    just need comment this declaration.
*)
  (* Check @fieldAinvProper Qc Qcplus (Q2Qc (Qmake Z0 xH)) *)
  (*   Qcopp Qcmult (Q2Qc (Qmake (Zpos xH) xH)) Ainv Aeq. *)
    
  (* Add Field Field_thy_inst : Field_thy. *)
  
  Lemma Field_inst : Field Aadd A0 Aopp Amul A1 Ainv Aeq.
  Proof.
    constructor. apply Ring_inst.
    intros. unfold Amul,Ainv,Aeq,A1,A. field. auto.
    apply A1_neq_A0.
    apply Ainv_aeq_mor.
  Qed.

End FieldElementTypeQc.

Module FieldElementTypeR
<: FieldElementType.
  Include RingElementTypeR.
  
  Definition Ainv := Rinv.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  Lemma Ainv_aeq_mor : Proper (Aeq ==> Aeq) Ainv.
  Proof.
    unfold Proper, respectful. intros. rewrite H. easy.
  Qed.

  Lemma A1_neq_A0 : ~(A1 == A0)%A.
  Proof.
    cbv in *. auto with real.
  Qed.

  Lemma Field_thy: field_theory A0 A1 Aadd Amul Asub Aopp Adiv Ainv Aeq.
  Proof.
    constructor; intros; try easy.
    apply Ring_thy.
    apply A1_neq_A0.
    unfold Amul,Ainv,A1,Aeq. unfold ElementTypeR.Aeq,ElementTypeR.A. field. auto.
  Qed.

  Add Field Field_thy_inst : Field_thy.
  
  Lemma Field_inst : Field Aadd A0 Aopp Amul A1 Ainv Aeq.
  Proof.
    constructor. apply Ring_inst.
    intros. unfold Amul,Ainv,Aeq,A1,A. field. auto.
    apply A1_neq_A0.
    apply Ainv_aeq_mor.
  Qed.
  
End FieldElementTypeR.

(* Module FieldElementTypeFun (I O : FieldElementType) <: FieldElementType. *)
(*   Include (RingElementTypeFun I O). *)

(*   Definition Ainv : A -> A. *)
(*     cbv. intros [f Pf]. *)
(*     refine (exist _ (fun x : I.A => O.Ainv (f x)) _). *)
(*     constructor. intros. *)
(*     pose proof (O.Resp_Ainv_Aeq). apply respectUnary. apply Pf; easy. *)
(*   Defined. *)
  
(*   Notation Adiv := (fun x y => Amul x (Ainv y)). *)

  (* Lemma Ainv_aeq_mor : Proper (Aeq ==> Aeq) Ainv. *)
  (* Proof. *)
  (*   unfold Proper, respectful. intros [x Px] [y Py] H1. *)
  (*   cbv in *. intros. apply O.Resp_Ainv_Aeq; auto. *)
  (* Qed. *)
  
(*   (* Import FunctionalExtensionality. *) *)
(*   Lemma A1_neq_A0 : ~(A1 == A0)%A. *)
(*   Proof. cbv in *. intros. specialize (H I.A0). apply O.A1_neq_A0 in H. auto. Qed. *)

(*   Lemma Field_thy: field_theory A0 A1 Aadd Amul Asub Aopp Adiv Ainv Aeq. *)
(*   Proof. *)
(*     destruct (I.Field_thy), (O.Field_thy). *)
(*     constructor. *)
(*     - apply Ring_thy. *)
(*     - apply A1_neq_A0. *)
(*     - intros. *)
(*       repeat match goal with | x:A |- _ => destruct x end. *)
(*       cbv in *; intros. *)
(*       pose proof (O.Amul_aeq_mor). *)
(*       pose proof (O.Equiv_Aeq). *)
(*       apply H; easy. *)
(*     - intros. *)
(*       repeat match goal with | x:A |- _ => destruct x end. *)
(*       cbv in *; intros. *)
(*       apply Finv_l0. revert a. *)
(*       (* Note that, this is not true. *)
(*          H means: ~(x a1 = 0 /\ x a2 = 0 /\ ...) *)
(*          but we need: x a1 <> 0 /\ x a2 <> 0 /\ ... *)
(*          !!this is not provable. *)
(*        *) *)
(*       admit. *)
(*   Admitted. *)

(* End FieldElementTypeFun. *)

Module FieldElementTypeTest.
  Import FunctionalExtensionality.
  Import FieldElementTypeQ.
  Import FieldElementTypeR.

  (* Include (FieldElementTypeFun FieldElementTypeQ FieldElementTypeR). *)
End FieldElementTypeTest.



(* ######################################################################### *)
(** * Element with field structure and decidable relation *)

(** ** Type of Element with field structure and decidable relation *)

Module Type DecidableFieldElementType
<: FieldElementType
<: DecidableElementType.
  Include FieldElementType.
  Open Scope A_scope.

  Axiom Dec_Aeq : Decidable Aeq.
  Global Existing Instance Dec_Aeq.
End DecidableFieldElementType.

Module Type EqDecidableFieldElementType (B : BaseType)
<: EqElementType B
<: DecidableFieldElementType
  := DecidableFieldElementType
     with Definition A := B.A
     with Definition Aeq := @eq B.A.

(** ** Instances *)

Module DecidableFieldElementTypeQ
<: DecidableFieldElementType.
  Include FieldElementTypeQ.
  Import DecidableElementTypeQ.
  
  Lemma Dec_Aeq : Decidable Aeq.
  Proof.
    apply Dec_Aeq.
  Qed.
End DecidableFieldElementTypeQ.

Module DecidableFieldElementTypeQc
<: DecidableFieldElementType.
(* <: EqDecidableFieldElementType BaseTypeQc. *) (* needn't do this *)
  Include FieldElementTypeQc.
  Import DecidableElementTypeQc.
  
  Lemma Dec_Aeq : Decidable Aeq.
  Proof.
    apply Dec_Aeq.
  Qed.
End DecidableFieldElementTypeQc.

Module DecidableFieldElementTypeR
<: DecidableFieldElementType.
  Include FieldElementTypeR.
  Import DecidableElementTypeR.

  Lemma Dec_Aeq : Decidable Aeq.
  Proof.
    apply Dec_Aeq.
  Qed.
End DecidableFieldElementTypeR.
