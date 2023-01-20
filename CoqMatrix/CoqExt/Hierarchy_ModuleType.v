(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : common mathematical hierarchy structure by Module Type
  author    : ZhengPu Shi
  date      : 2021.05


  refrence  :
  1. https://en.wikipedia.org/wiki/Ring_(mathematics)

  remark    :
  1. The operations or properties below are not needed by ring structure, 
     just for convenient.
      
        Aeqb, Aeqdec, Aeqb_true_iff, Aeqb_false_iff
    
     We may construct more elegent algebra structre use Typeclasses.

*)

From Coq Require Export Ring Field.
From FCS Require Export BasicConfig.
From FCS Require ZExt QcExt RExt RAST.


(* ######################################################################### *)
(** * Scope of element *)

(** New scope for field. *)
Declare Scope A_scope.
Delimit Scope A_scope with A.
Open Scope A_scope.


(* ######################################################################### *)
(** * Ring Structure *)


(** ** Ring Signature *)
Module Type RingSig.
  
  (** Carrier and operations *)
  Parameter A : Type.   (* Carrier Type *)
  Parameter A0 : A.     (* Additive unit element *)
  Parameter A1 : A.     (* Multiplicative unit element *)
  Parameter Aadd : A -> A -> A.    	(* Addition operation *)
  Parameter Amul : A -> A -> A.     (* Multiplication operation *)
  Parameter Aopp : A -> A.          (* Additive inverse *)
  Parameter Aeqb : A -> A -> bool.
  
  (** New scope, and notations *)
  Bind Scope A_scope with A A0 A1 Aadd Amul Aopp Aeqb.
  
  (** Notations for carrier operations *)
  Notation  "a =? b"    := (Aeqb a b)         : A_scope.
  Infix     "+"         := Aadd               : A_scope.
  Infix     "*"         := Amul               : A_scope.
  Notation  "- a"       := (Aopp a)           : A_scope.
  Notation  Asub        := (fun x y => x + -y).
  Infix     "-"         := Asub               : A_scope.

  (** Equality is decidable *)
  Parameter Aeqdec : forall (x y : A), {x = y} + {x <> y}.

  (** Reflection of Aeq and Aeqb *)
  Parameter Aeqb_true_iff : forall x y, (x =? y = true) <-> x = y.
  Parameter Aeqb_false_iff : forall x y, (x =? y = false) <-> (x <> y).
  
  (** Ring tactic requirement *)
  Parameter Ring_thy : ring_theory A0 A1 Aadd Amul Asub Aopp eq.
  Add Ring Ring_thy_inst : Ring_thy.
  
End RingSig.


(** ** Ring theory *)

(** Although ring and field tactic is enough automatic, but some cases we also 
  need to manually rewrite. So, we gather and added lots of properties for 
  Ring structure. Thus, no matter what the carrier is, the unified name can be 
  used always. *)
Module RingThy (E : RingSig).
  Export E.
  Notation "0" := A0.
  Notation "1" := A1.
  Infix "+" := Aadd.
  Notation "- x" := (Aopp x).
  Notation "a - b" := (a + (-b)).
  
  Lemma add_comm : forall a b : A, a + b = b + a.
  Proof. intros. ring. Qed.
  
  Lemma add_assoc : forall a b c : A, (a + b) + c = a + (b + c). 
  Proof. intros. ring. Qed.
  
  Lemma add_0_l : forall a : A, 0 + a = a.
  Proof. intros. ring. Qed.
  
  Lemma add_0_r : forall a : A, a + 0 = a.
  Proof. intros. ring. Qed.
  
  Lemma add_opp_l : forall a : A, -a + a = 0.
  Proof. intros. ring. Qed.
  
  Lemma add_opp_r : forall a : A, a - a = 0.
  Proof. intros. ring. Qed.
  
  Lemma opp_opp : forall a : A, - - a = a.
  Proof. intros. ring. Qed.
  
  Lemma add_cancel_l : forall a b1 b2 : A, a + b1 = a + b2 -> b1 = b2.
  Proof.
    intros.
    rewrite <- (add_0_l b1).
    rewrite <- (add_0_l b2).   (* 0 + b1 = 0 + b2  *)
    rewrite <- (add_opp_l a).  (* -a + a + b1 = -a + a + b1 *)
    rewrite ?add_assoc.        (* -a + (a + b1) = -a + (a + b2) *)
    rewrite H. reflexivity.
  Qed.
  
  Lemma add_cancel_r : forall a1 a2 b : A, a1 + b = a2 + b -> a1 = a2.
  Proof.
    intros.
    rewrite <- (add_0_r a1).
    rewrite <- (add_0_r a2).
    rewrite <- (add_opp_r b).
    rewrite <- ?add_assoc.
    rewrite H. reflexivity.
  Qed.
  
End RingThy.


(** ** Ring on Z *)
Module RingZ.

  Export ZArith.
  (* Open Scope Z. *)

  Module Export RingDefZ : RingSig
    with Definition A := Z
    with Definition A0 := 0%Z
    with Definition A1 := 1%Z
    with Definition Aadd := Z.add
    with Definition Amul := Z.mul
    with Definition Aopp := Z.opp
    with Definition Aeqb := Z.eqb
    .

    Definition A := Z.
    Definition A0 := 0%Z.
    Definition A1 := 1%Z.
    Definition Aadd := Z.add.
    Definition Amul := Z.mul.
    Definition Aopp := Z.opp.
    Definition Aeqb := Z.eqb.
    
    Definition Aeqdec := Z.eq_dec.
    Definition Aeqb_true_iff := Z.eqb_eq.
    Definition Aeqb_false_iff := Z.eqb_neq.
    
    Definition Ring_thy : ring_theory A0 A1 Aadd Amul Z.sub Aopp eq.
      constructor; intros; try reflexivity.
      apply Zplus_comm.
      apply Zplus_assoc.
      apply Z.mul_1_l.
      apply Z.mul_comm.
      apply Z.mul_assoc.
      apply Z.mul_add_distr_r.
      apply Z.add_opp_diag_r.
    Defined.
    
    Add Ring Ring_thy_inst : Ring_thy.
    
  End RingDefZ.
  
  Module Export RingThyZ := RingThy RingDefZ.
  
End RingZ.


(** ** Test for Ring on Z *)

Module RingZ_test.

  Import RingZ.
  
  Example ex2 : forall a b c d : A, 
    (a + b) * (c + d) = a * c + a * d + c * b + b * d.
  Proof.
    intros. ring. Qed.
  
End RingZ_test.


(** ** Ring on Q *)

Module RingQ.

  Export QExt.
  
  (* Open Scope Q_scope. *)
  Module Export RingDefQ : RingSig
    with Definition A := Q
    with Definition A0 := 0
    with Definition A1 := 1
    with Definition Aadd := Qplus
    with Definition Amul := Qmult
    with Definition Aopp := Qopp
    with Definition Aeqb := Qeqb
    .

    Definition A := Q.
    Definition A0 := 0.
    Definition A1 := 1.
    Definition Aadd := Qplus.
    Definition Amul := Qmult.
    Definition Aopp := Qopp.
    Definition Aeqb := Qeqb.
    Definition Aeqdec := Qeqdec.
    Definition Aeqb_true_iff := Qeqb_true_iff.
    Definition Aeqb_false_iff := Qeqb_false_iff.
    
    (** Ring Theory *)
    
    Definition Ring_thy : ring_theory A0 A1 Aadd Amul Qminus Aopp eq.
      constructor; intros; try reflexivity; try apply Qeq_iff_eq.
      apply Qplus_0_l.
      apply Qplus_comm.
      apply Qplus_assoc.
      apply Qmult_1_l.
      apply Qmult_comm.
      apply Qmult_assoc.
      apply Qmult_plus_distr_l.
      apply Qplus_opp_r.
    Defined.
    
    Add Ring Ring_thy_inst : Ring_thy.
    
  End RingDefQ.

End RingQ.


(** ** Test for Ring on Q *)

Module RingQ_test.

  Import RingQ.
  Open Scope A_scope.
  
  Example ex2 : forall a b c d : A, 
    (a + b) * (c + d) = a * c + a * d + c * b + b * d.
  Proof.
    intros. ring. Qed.
  
End RingQ_test.


(** ** Ring on Qc *)

Module RingQc.
  
  Export QcExt.
  (* Open Scope Qc_scope. *)

  Module Export RingDefQc : RingSig
    with Definition A := Qc
    with Definition A0 := 0
    with Definition A1 := 1
    with Definition Aadd := Qcplus
    with Definition Amul := Qcmult
    with Definition Aopp := Qcopp
    with Definition Aeqb := Qceqb
    .

    Definition A := Qc.
    Definition A0 := 0.
    Definition A1 := 1.
    Definition Aadd := Qcplus.
    Definition Amul := Qcmult.
    Definition Aopp := Qcopp.
    Definition Aeqb := Qceqb.
    Definition Aeqdec := Qceqdec.
    Definition Aeqb_true_iff := Qceqb_true_iff.
    Definition Aeqb_false_iff := Qceqb_false_iff.
    
    (** Ring Theory *)
    
    Definition Ring_thy : ring_theory A0 A1 Aadd Amul Qcminus Aopp eq.
      constructor; intros; try reflexivity.
      apply Qcplus_0_l.
      apply Qcplus_comm.
      apply Qcplus_assoc.
      apply Qcmult_1_l.
      apply Qcmult_comm.
      apply Qcmult_assoc.
      apply Qcmult_plus_distr_l.
      apply Qcplus_opp_r.
    Defined.
    
    Add Ring Ring_thy_inst : Ring_thy.
    
  End RingDefQc.

End RingQc.


(** ** Test for Ring on Qc *)

Module RingQc_test.

  Import RingQc.
  Open Scope A_scope.
  
  Example ex2 : forall a b c d : A, 
    (a + b) * (c + d) = a * c + a * d + c * b + b * d.
  Proof.
    intros. ring. Qed.
  
End RingQc_test.


(** ** Ring on R *)

Module RingR.

  Export Reals RExt.
  Open Scope R.

  Module Export RingDefR : RingSig
    with Definition A := R
    with Definition A0 := R0
    with Definition A1 := R1
    with Definition Aadd := Rplus
    with Definition Amul := Rmult
    with Definition Aopp := Ropp
    with Definition Aeqb := Reqb
    .
    
    Definition A := R.
    Definition A0 := R0.
    Definition A1 := R1.
    Definition Aadd := Rplus.
    Definition Amul := Rmult.
    Definition Aopp := Ropp.
    
    (** Ring Theory *)
    
    Definition Ring_thy : ring_theory A0 A1 Aadd Amul Rminus Aopp eq.
      constructor; intros; cbv; ring. Defined.
    
    Add Ring Ring_thy_inst : Ring_thy.

    Definition Aeqb r1 r2 := Reqb r1 r2.
    Definition Aeqdec := Req_EM_T.
    Definition Aeqb_true_iff := Reqb_true_iff.
    Definition Aeqb_false_iff := Reqb_false_iff.

  End RingDefR.

End RingR.


(** ** Test for Ring on R *)

Module RingR_test.

  Import RingR.
  Open Scope A_scope.

  Example ex2 : forall a b c d : A, 
    (a + b) * (c + d) = (a * c + a * d + c * b + b * d).
  Proof.
    intros. ring. Qed.
  
End RingR_test.


(** ** Ring on T *)

Module RingT.

  Export RAST.
  Open Scope T.

  Module Export RingDefT : RingSig
    with Definition A := T
    with Definition A0 := T0
    with Definition A1 := T1
    with Definition Aadd := Tadd
    with Definition Amul := Tmul
    with Definition Aopp := Topp
    with Definition Aeqb := Teqb
    .
    
    Definition A := T.
    Definition A0 := T0.
    Definition A1 := T1.
    Definition Aadd := Tadd.
    Definition Amul := Tmul.
    Definition Aopp := Topp.
    
    (** Ring Theory *)
    
    Definition Ring_thy := T_ring.
    Add Ring Ring_thy_inst : Ring_thy.

    Definition Aeqb r1 r2 := Teqb r1 r2.
    Definition Aeqdec := Teqdec.
    Axiom Teqb_true_iff : forall x y : T, (x =? y)%T = true <-> x = y.
    Axiom Teqb_false_iff : forall x y : T, (x =? y)%T = false <-> x <> y.
    Definition Aeqb_true_iff := Teqb_true_iff.
    Definition Aeqb_false_iff := Teqb_false_iff.

  End RingDefT.

End RingT.


(** ** Test for Ring on T *)

Module RingT_test.

  Import RingT.

  Open Scope T.
  Example ex1 : forall a b c d : T, 
    (a + b) * (c + d) = a * c + a * d + c * b + b * d.
  Proof. intros. ring. Qed.

  Open Scope A_scope.
  Example ex2 : forall a b c d : A, 
    (a + b) * (c + d) = (a * c + a * d + c * b + b * d).
  Proof.
    intros. ring. Qed. 
  
End RingT_test.


(* ######################################################################### *)
(** * Field Signature *)


(** ** Signature for field *)
Module Type FieldSig <: RingSig.
  
  (** Carrier *)
  Parameter A : Type.
  
  (** Operations *)
  Parameter A0 A1 : A.
  Parameter Aadd Amul : A -> A -> A.
  Parameter Aopp Ainv : A -> A.
  Parameter Aeqb : A -> A -> bool.
  
  (** Notations *)
  Notation "0" := A0 : A_scope.
  Notation "1" := A1 : A_scope.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Asub := (fun x y => x + -y).
  Notation Adiv := (fun x y => x * /y).
  Infix "-" := Asub : A_scope.
  Infix "/" := Adiv : A_scope.
  Notation "a =? b" := (Aeqb a b) (at level 70) : A_scope.
  
  (** Bind something to the scope *)
  Bind Scope A_scope with A A0 A1 Aadd Amul Aopp Ainv Aeqb.

  (** Properties *)

  (** Equality is decidable *)
  Parameter Aeqdec : forall (x y : A), {x = y} + {x <> y}.

  (** Reflection of Aeq and Aeqb *)
  Parameter Aeqb_true_iff : forall x y, (x =? y = true) <-> x = y.
  Parameter Aeqb_false_iff : forall x y, (x =? y = false) <-> (x <> y).
  
  (** 1 <> 0. *)
  Parameter A1_neq_A0 : A1 <> A0.
  
  (** Ring theory *)
  Parameter Ring_thy : ring_theory A0 A1 Aadd Amul Asub Aopp eq.
  Add Ring Ring_thy_inst : Ring_thy.

  (** Field Theory *)
  Parameter Field_thy: field_theory A0 A1 Aadd Amul Asub Aopp Adiv Ainv eq.
  Add Field Field_thy_inst : Field_thy.

End FieldSig.


(** ** Field theory *)

Module FieldThy (E : FieldSig).

  Export E.

  Open Scope A_scope.

  Lemma add_comm : forall a b, a + b = b + a.
  Proof. intros. ring. Qed.
  
  Lemma add_assoc : forall a b c, (a + b) + c = a + (b + c). 
  Proof. intros. ring. Qed.
  
  Lemma add_0_l : forall a, 0 + a = a.
  Proof. intros. ring. Qed.
  
  Lemma add_0_r : forall a, a + 0 = a.
  Proof. intros. ring. Qed.
  
  Lemma add_opp_l : forall a, -a + a = 0.
  Proof. intros. ring. Qed.
  
  Lemma add_opp_r : forall a, a - a = 0.
  Proof. intros. ring. Qed.
  
  Lemma opp_opp : forall a, - - a = a.
  Proof. intros. ring. Qed.
  
  Lemma add_cancel_l : forall a b1 b2, a + b1 = a + b2 -> b1 = b2.
  Proof.
    intros.
    rewrite <- (add_0_l b1).
    rewrite <- (add_0_l b2).   (* 0 + b1 = 0 + b2  *)
    rewrite <- (add_opp_l a).  (* -a + a + b1 = -a + a + b1 *)
    rewrite ?add_assoc.        (* -a + (a + b1) = -a + (a + b2) *)
    rewrite H. reflexivity.
  Qed.
  
  Lemma add_cancel_r : forall a1 a2 b, a1 + b = a2 + b -> a1 = a2.
  Proof.
    intros. rewrite <- (add_0_r a1). rewrite <- (add_0_r a2).
    rewrite <- (add_opp_r b). rewrite <- ?add_assoc. rewrite H. auto.
  Qed.
  
  Lemma mul_comm : forall a b, a * b = b * a.
  Proof. intros. ring. Qed.
  
  Lemma mul_assoc : forall a b c, (a * b) * c = a * (b * c). 
  Proof. intros. ring. Qed.
  
  Lemma mul_0_l : forall a, 0 * a = 0.
  Proof. intros. ring. Qed.
  
  Lemma mul_0_r : forall a, a * 0 = 0.
  Proof. intros. ring. Qed.
  
  Lemma mul_1_l : forall a, 1 * a = a.
  Proof. intros. ring. Qed.
  
  Lemma mul_1_r : forall a, a * 1 = a.
  Proof. intros. ring. Qed.
  
  Lemma mul_inv_l : forall a, a <> 0 -> /a * a = 1.
  Proof. intros. field. auto. Qed.
  
  Lemma mul_inv_r : forall a, a <> 0 -> a / a = 1.
  Proof. intros. field. auto. Qed.
  
  Lemma inv_inv : forall a, a <> 0 -> //a = a.
  Proof. intros. field. split; auto. apply A1_neq_A0. Qed.
  
  Lemma mul_cancel_l : forall a b1 b2, a <> 0 -> a * b1 = a * b2 -> b1 = b2.
  Proof.
    intros. rewrite <- (mul_1_l b1). rewrite <- (mul_1_l b2).
    rewrite <- (mul_inv_l a); auto. rewrite ?mul_assoc. f_equal. auto.
  Qed.
  
  Lemma mul_cancel_r : forall a1 a2 b, b <> 0 -> a1 * b = a2 * b -> a1 = a2.
  Proof.
    intros. rewrite <- (mul_1_r a1). rewrite <- (mul_1_r a2).
    rewrite <- (mul_inv_r b); auto. rewrite <- ?mul_assoc. f_equal. auto.
  Qed.
  
End FieldThy.



(** ** Field on Qc *)

Module FieldQc.
  
  Export QcExt.
  Open Scope Qc_scope.
  
  Module Export FieldDefQc : FieldSig
    with Definition A := Qc
    with Definition A0 := 0
    with Definition A1 := 1
    with Definition Aadd := Qcplus
    with Definition Aopp := Qcopp
    with Definition Amul := Qcmult
    with Definition Ainv := Qcinv
    with Definition Aeqb := Qceqb.
    
    Definition A := Qc.
    Definition A0 := 0.
    Definition A1 := 1.
    Definition Aadd := Qcplus.
    Definition Aopp := Qcopp.
    Definition Amul := Qcmult.
    Definition Ainv := Qcinv.
    Definition Aeqb := Qceqb.
    Definition Aeqdec := Qceqdec.
    Definition Aeqb_true_iff := Qceqb_true_iff.
    Definition Aeqb_false_iff := Qceqb_false_iff.
    
    Lemma A1_neq_A0 : A1 <> A0.
    Proof. intro. discriminate. Qed.
    
    Lemma Ring_thy : ring_theory A0 A1 Aadd Amul Qcminus Aopp eq.
    Proof.
      constructor; intros; try auto.
      apply Qcplus_0_l. apply Qcplus_comm. apply Qcplus_assoc.
      apply Qcmult_1_l. apply Qcmult_comm. apply Qcmult_assoc.
      apply Qcmult_plus_distr_l. apply Qcplus_opp_r.
    Qed.
    Add Ring Ring_thy_inst : Ring_thy.
    
    Lemma Field_thy : field_theory A0 A1 Aadd Amul Qcminus Aopp Qcdiv 
      Ainv eq.
    Proof.
      constructor; try easy. apply Ring_thy.
      intros. rewrite Qcmult_comm,Qcmult_inv_r; auto.
    Qed.
    Add Field Field_thy_inst : Field_thy.

  End FieldDefQc.

  Module Export FieldThyQc := FieldThy FieldDefQc.

End FieldQc.


(** ** Test for FieldQc *)
Module FieldQc_test.

  Import FieldQc.
  Open Scope A_scope.

  Goal forall a b c : A, (c<>0) -> (a + b) / c = a / c + b / c.
  Proof. intros. field. auto. Qed.

  Goal forall a b, a <> 0 -> /a * a * b = b.
  Proof. intros. rewrite mul_inv_l. field. auto. Qed.

End FieldQc_test.


(** ** Field on R *)

Module FieldR.
  
  Export RExt.
  Open Scope R_scope.

  Module Export FieldDefR : FieldSig
    with Definition A := R
    with Definition A0 := 0
    with Definition A1 := 1
    with Definition Aadd := Rplus
    with Definition Aopp := Ropp
    with Definition Amul := Rmult
    with Definition Ainv := Rinv
    with Definition Aeqb := Reqb.
    
    Definition A := R.
    Definition A0 := 0.
    Definition A1 := 1.
    Definition Aadd := Rplus.
    Definition Aopp := Ropp.
    Definition Amul := Rmult.
    Definition Ainv := Rinv.
    Definition Aeqb := Reqb.
    Definition Aeqdec := Req_EM_T.
    Definition Aeqb_true_iff := Reqb_true_iff.
    Definition Aeqb_false_iff := Reqb_false_iff.
    
    Lemma A1_neq_A0 : A1 <> A0.
    Proof. intro. auto with R. Qed.
    
    Lemma Ring_thy : ring_theory A0 A1 Aadd Amul Rminus Aopp eq.
    Proof. constructor; intros; cbv; ring. Qed.
    Add Ring Ring_thy_inst : Ring_thy.
    
    Lemma Field_thy : field_theory A0 A1 Aadd Amul Rminus Aopp Rdiv Ainv eq.
    Proof.
      constructor; try easy. apply Ring_thy. apply A1_neq_A0.
      intros; cbv; field; auto.
    Qed.
    Add Field Field_thy_inst : Field_thy.

  End FieldDefR.

  Module Export FieldThyR := FieldThy FieldDefR.

End FieldR.

(** ** Test for FieldR *)
Module FieldR_test.

  Import FieldR.
  Open Scope A_scope.

  Goal forall a b c : A, (c<>0) -> (a + b) / c = a / c + b / c.
  Proof. intros. field. auto. Qed.

End FieldR_test.


(** ** Field on T *)

Module FieldT.
  
  Export RAST.
  Open Scope T_scope.
  
  Module Export FieldDefT : FieldSig
    with Definition A := T
    with Definition A0 := T0
    with Definition A1 := T1
    with Definition Aadd := Tadd
    with Definition Aopp := Topp
    with Definition Amul := Tmul
    with Definition Ainv := Tinv
    with Definition Aeqb := Teqb.
    
    Axiom Teqb_true_iff : forall x y : T, (x =? y)%T = true <-> x = y.
    Axiom Teqb_false_iff : forall x y : T, (x =? y)%T = false <-> x <> y.
    
    Definition A := T.
    Definition A0 := T0.
    Definition A1 := T1.
    Definition Aadd := Tadd.
    Definition Aopp := Topp.
    Definition Amul := Tmul.
    Definition Ainv := Tinv.
    Definition Aeqb := Teqb.
    Definition Aeqdec := Teqdec.
    Definition Aeqb_true_iff := Teqb_true_iff.
    Definition Aeqb_false_iff := Teqb_false_iff.
    
    Lemma A1_neq_A0 : A1 <> A0.
    Proof. intro. easy. Qed.
    
    Lemma Ring_thy : ring_theory A0 A1 Aadd Amul Tsub Aopp eq.
    Proof. constructor; intros; cbv; ring. Qed.
    Add Ring Ring_thy_inst : Ring_thy.
    
    Lemma Field_thy : field_theory A0 A1 Aadd Amul Tsub Aopp Tdiv Ainv eq.
    Proof.
      constructor; try easy. apply Ring_thy.
      intros; cbv; field; auto.
    Qed.
    Add Field Field_thy_inst : Field_thy.

  End FieldDefT.
  
  Module Export FieldThyT := FieldThy FieldDefT.

End FieldT.

(** ** Test for FieldR *)
Module FieldT_test.

  Import FieldT.
  Open Scope A_scope.

  Goal forall a b c : A, (c<>0) -> (a + b) / c = a / c + b / c.
  Proof. intros. field. auto. Qed.

End FieldT_test.

