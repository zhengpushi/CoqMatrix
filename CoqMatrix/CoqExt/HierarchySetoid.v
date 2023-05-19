(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Algebraic hierarchy (use type class) (Setoid version)
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
  1. The motivate of this module is to support development with good organized 
    algebraic hierarchy, instead of scattered def./op./props.
  2. There are three technologies to form a hierarchy: module is a strong 
    specification and too heavy; type classes is used in Coq standard library;
    canonical structure is used in mathematical component.
  3. For type classes, ref to this paper "A Gentle Introduction to Type Classes 
    and Relations in Coq" and the refrence manual of Coq at 
    "https://coq.inria.fr/distrib/V8.13.2/refman/addendum/type-classes.html".
  4. About Q (rational number), we mainly use Qcanon (Qc) instead of Q, hence 
    the convenient of equality relation. Precisely, Qc use eq that has best 
    built-in support in Coq, rather than Q use Qeq that we should use Setoid 
    and write more code to let it work.
  
  reference :
  1.  Arkansas Tech University / Dr. Marcel B. Finan /
      MATH 4033: Elementary Modern Algebra
  
  (a) 5 Definition and Examples of Groups
  https://faculty.atu.edu/mfinan/4033/absalg5.pdf
  (b) 14 Elementary Properties of Groups
  https://faculty.atu.edu/mfinan/4033/absalg14.pdf
  
  2. 
  https://math.okstate.edu/people/binegar/3613/3613-l21.pdf
  
 *)

Require Export BasicConfig.   (* reserved notation *)
Require Export Coq.Classes.RelationClasses. (* binary_relation *)
Require Import Coq.Logic.Description. (* constructive_definite_description *)
Require Export List SetoidList. Import ListNotations.
Require Export Lia Lra.
Require Export Ring Field.
Require Import Arith ZArith QArith QcExt RExt.

Open Scope nat_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* Meanwhile, like A0,A1,... also be availble *)
Generalizable Variables A Azero Aone Aeq Aadd Aopp Amul Ainv Adiv.


(* ######################################################################### *)
(** * Small utilities *)

(** repeat split and intro *)
Ltac split_intro :=
  repeat (try split; try intro).

(** Applicate a unary function for n-times, i.e. f ( .. (f a0) ...) *)
Fixpoint iterate {A} (f : A -> A) (n : nat) (a0 : A) : A :=
  match n with
  | O => a0
  | S n' => f (iterate f n' a0)
  end.

Section test.
  Context {A} {f : A -> A} (Azero : A).
  (* Compute iterate f 3 Azero. *)
End test.

(** x is an unique element which holds by P. Setoid version *)
Definition unique_setoid {A: Type} {Aeq: relation A} (P: A -> Prop) (x: A) :=
  P x /\ (forall x' : A, P x' -> Aeq x x').

(** constructive_definite_description, setoid version *)
Axiom constructive_definite_description_setoid :
  forall (A : Type) (Aeq:relation A) (P : A -> Prop),
    (exists x : A, (P x /\ unique_setoid (Aeq:=Aeq) P x)) -> {x : A | P x}.

(** functional_extensionality, setoid version *)
Axiom functional_extensionality_setoid :
  forall {A B} {Beq: relation B} (feq: relation (A->B)) (f g : A -> B),
    (forall a : A, Beq (f a) (g a)) -> feq f g.


(* ######################################################################### *)
(** * A relation is equivalence relation *)

(** ** Class *)

(* Global Hint Constructors Equivalence : core. *)

(** ** Instances *)

(** eqlistA is a equivalence relation *)
Global Instance Equivalence_eqlistA `{Equiv_Aeq:Equivalence A Aeq}
  : Equivalence (eqlistA Aeq).
Proof. apply eqlistA_equiv. auto. Defined.

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * A relation is decidable, usually for equality relation *)

(** ** Class *)

Class Decidable {A:Type} (Aeq:A->A->Prop) := {
    decidable : forall (a b : A), {Aeq a b} + {~(Aeq a b)};
  }.
(* Global Hint Constructors Decidable : core. *)

(** ** Instances *)

Section Instances.
  Import Arith ZArith Reals.

  (** Note that, the instances of EqDec should be declared transparent to enable
    calculation. That is, use Defined instead of Qed. *)
  Global Instance Decidable_NatEq : Decidable Nat.eq.
  Proof. constructor. apply Nat.eq_dec. Defined.

  Global Instance Decidable_Z : @Decidable Z eq.
  Proof. constructor. apply Z.eq_dec. Defined.

  Global Instance Decidable_R : @Decidable R eq.
  Proof. constructor. apply Req_EM_T. Defined.
  
  Global Instance Decidable_list `{Dec:Decidable} : Decidable (eqlistA Aeq).
  Proof.
    constructor. intros l1. induction l1.
    - intros l2. destruct l2; auto.
      right. intro. easy.
    - intros l2. destruct l2.
      + right. intro. easy.
      + destruct (decidable a a0), (IHl1 l2); auto.
        * right. intro. inversion H. easy.
        * right. intro. inversion H. easy.
        * right. intro. inversion H. easy.
  Defined.

  Global Instance Decidable_dlist `{Dec:Decidable} : Decidable (eqlistA (eqlistA Aeq)).
  Proof.
    constructor. intros l1. induction l1.
    - intros l2. destruct l2; auto.
      right. intro. easy.
    - intros l2. destruct l2.
      + right. intro. easy.
      + destruct (decidable a l), (IHl1 l2); auto.
        * right. intro. inversion H. easy.
        * right. intro. inversion H. easy.
        * right. intro. inversion H. easy.
  Defined.

End Instances.

(** ** Extra Theories *)
Section Dec_theory.

  Context `{Dec : Decidable}.

  (** Tips: these theories are useful for R type *)
  
  (** Calculate equality to boolean, with the help of equality decidability *)
  Definition Aeqb (a b : A) : bool := if decidable a b then true else false.

  (** Aeqb is true iff equal. *)
  Lemma Aeqb_true : forall a b, Aeqb a b = true <-> Aeq a b.
  Proof.
    intros. unfold Aeqb. destruct decidable; split; intros; auto;  easy.
  Qed.

  (** Aeqb is false iff not equal *)
  Lemma Aeqb_false : forall a b, Aeqb a b = false <-> ~(Aeq a b).
  Proof.
    intros. unfold Aeqb. destruct decidable; split; intros; auto; try easy.
  Qed.

  Lemma Aeq_reflect : forall a b : A, reflect (Aeq a b) (Aeqb a b).
  Proof.
    intros. unfold Aeqb. destruct (decidable a b); constructor; auto.
  Qed.

End Dec_theory.

(** ** Examples *)
Goal forall a b : nat, {a = b} + {a <> b}.
  apply decidable. Qed.


(* ######################################################################### *)
(** * Respect: an operation respect a relation *)

(** deprecated, replaced with "Proper" in Coq *)

(* (** ** Class *) *)

(* (** A unary operation is respect to the equality relation *) *)
(* Class RespectUnary {A B:Type} (op:A->B) (Aeq:A->A->Prop) (Beq:B->B->Prop) := { *)
(*     respectUnary : forall x y : A, *)
(*       Aeq x y -> Beq (op x) (op y) *)
(*   }. *)

(* (** A binary operation is respect to the equality relation *) *)
(* Class RespectBinary {A B C:Type} (op:A->B->C) *)
(*   (Aeq:A->A->Prop) (Beq:B->B->Prop) (Ceq:C->C->Prop):= { *)
(*     respectBinary : forall x y : A, *)
(*       Aeq x y -> forall x0 y0 : B, Beq x0 y0 -> Ceq (op x x0) (op y y0) *)
(*   }. *)

(** ** Instances *)
Hint Resolve
  Nat.add_wd Nat.mul_wd  (* nat *)
  Z.add_wd Z.opp_wd Z.sub_wd Z.mul_wd (* Z *)
  Qplus_comp Qopp_comp Qminus_comp Qmult_comp Qinv_comp Qdiv_comp (* Q *)
  Qcplus_wd Qcopp_wd Qcminus_wd Qcmult_wd Qcinv_wd Qcdiv_wd (* Qc *)
  Rplus_wd Ropp_wd Rminus_wd Rmult_wd Rinv_wd Rdiv_wd (* R *)
  : wd.

(* (** ** Extra Theories *) *)

(* (** ** Examples *) *)



(* ######################################################################### *)
(** * Associative *)

(** ** Class *)
Class Associative {A:Type} (Aop:A->A->A) (Aeq:A->A->Prop) := {
    associative : forall a b c, Aeq (Aop (Aop a b) c) (Aop a (Aop b c));
  }.

(** ** Instances *)
Global Instance Assoc_NatAdd : Associative Nat.add eq.
constructor. auto with arith. Defined.

(** ** Extra Theories *)
Lemma associative_inv : forall `{Equiv_Aeq : Equivalence A Aeq} {Aop:A->A->A}
                          `{Assoc:Associative A Aop Aeq} a b c,
    Aeq (Aop a (Aop b c)) (Aop (Aop a b) c).
Proof. intros. rewrite -> associative. easy. Qed.

(** ** Examples *)
Goal forall a b c : nat, (a + (b + c) = (a + b) + c).
  apply associative_inv. Qed.

Goal forall a b c : nat, ((a + b) + c = a + (b + c)).
  apply associative. Qed.


(* ######################################################################### *)
(** * Commutative *)

(** ** Class *)
Class Commutative {A:Type} (Aop:A->A->A) (Aeq:A->A->Prop) := {
    commutative : forall a b, Aeq (Aop a b) (Aop b a)
  }.

(** ** Instances *)
Global Instance Comm_NatAdd : Commutative Nat.add eq.
constructor. auto with arith. Defined.

Global Instance Comm_NatMul : Commutative Nat.mul eq.
constructor. auto with arith. Defined.

(** ** Extra Theories *)

(** ** Examples *)
Goal forall a b : nat, (a + b = b + a)%nat.
  apply commutative. Qed.

Goal forall a b : nat, (a * b = b * a)%nat.
  apply commutative. Qed.


(* ######################################################################### *)
(** * Identity Left/Right *)

(** ** Class *)
Class IdentityLeft {A:Type} (Aop:A->A->A) (Ae:A) (Aeq:A->A->Prop) := {
    identityLeft : forall a, Aeq (Aop Ae a) a
  }.

Class IdentityRight {A:Type} (Aop:A->A->A) (Ae:A) (Aeq:A->A->Prop) := {
    identityRight : forall a, Aeq (Aop a Ae) a
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Inverse Left/Right *)

(** ** Class *)
Class InverseLeft {A:Type} (Aop:A->A->A) (Ae:A) (Aopinv:A->A) (Aeq:A->A->Prop)
  := {
    inverseLeft : forall a, Aeq (Aop (Aopinv a) a) Ae
  }.

Class InverseRight {A:Type} (Aop:A->A->A) (Ae:A) (Aopinv:A->A) (Aeq:A->A->Prop)
  := {
    inverseRight : forall a, Aeq (Aop a (Aopinv a)) Ae
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)


(* ######################################################################### *)
(** * Distributive *)

(** ** Class *)

(* Class DistributiveUnary {A:Type} (Aadd:A->A->A) (Aopp:A->A) (Aeq:A->A->Prop) := { *)
(*     distributiveUnary : forall a b, *)
(*       Aeq *)
(*         (Aopp (Aadd a b)) *)
(*         (Aadd (Aopp a) (Aopp b)) *)
(*   }. *)

Class DistributiveLeft {A:Type} (Aadd Amul:A->A->A) (Aeq:A->A->Prop) := {
    distributiveLeft : forall a b c,
      Aeq
        (Amul a (Aadd b c))
        (Aadd (Amul a b) (Amul a c))
  }.

Class DistributiveRight {A:Type} (Aadd Amul:A->A->A) (Aeq:A->A->Prop) := {
    distributiveRight : forall a b c,
      Aeq
        (Amul (Aadd a b) c)
        (Aadd (Amul a c) (Amul b c))
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Involution Law *)

(** ** Class *)

(* Class Involution {A : Type} (Aopp : A -> A) (Aeq:A->A->Prop) := { *)
(*     involution : forall a, Aeq (Aopp (Aopp a)) a *)
(*   }. *)

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Injective *)

(** ** Class *)

Class Injective {A B : Type} {Aeq: relation A} {Beq: relation B} (phi: A -> B) := {
    injective : forall a1 a2 : A, ~(Aeq a1 a2) -> ~(Beq (phi a1) (phi a2))
  }.
  
(** ** Instances *)

(** ** Extra Theories *)
Section theory.

  Context {A B : Type} {Aeq: relation A} {Beq: relation B}.

  Notation Injective := (Injective (Aeq:=Aeq) (Beq:=Beq)).
  
  (** Second form of injective *)
  Definition injective_form2 (phi: A -> B) :=
    forall (a1 a2 : A), Beq (phi a1) (phi a2) -> Aeq a1 a2.

  (** These two forms are equal *)
  Lemma injective_eq_injective_form2 (phi: A -> B) :
    Injective phi <-> injective_form2 phi.
  Proof.
    split; intros.
    - hnf. destruct H as [H]. intros.
      specialize (H a1 a2). apply imply_to_or in H. destruct H.
      + apply NNPP in H. auto.
      + easy.
    - hnf in H. constructor. intros. intro. apply H in H1. easy.
  Qed.

  (** Injective function preserve equal relation *)
  Lemma inj_pres_eq : forall (f : A -> B),
      Injective f -> (forall a1 a2 : A, Beq (f a1) (f a2) -> Aeq a1 a2).
  Proof.
    intros. apply injective_eq_injective_form2 in H. apply H. auto.
  Qed.

End theory.

(** ** Examples *)



(* ######################################################################### *)
(** * Surjective *)

(** ** Class *)

Class Surjective {A B : Type} {Beq: relation B} (phi: A -> B) := {
    surjective : forall (b : B), (exists (a : A), Beq (phi a) b)
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Bijective *)

(** ** Class *)

Class Bijective {A B : Type} {Aeq: relation A} {Beq: relation B} (phi: A -> B) := {
    bijInjective :> Injective (Aeq:=Aeq) (Beq:=Beq) phi;
    bijSurjective :> Surjective (Beq:=Beq) phi
  }.

(** ** Instances *)

(** ** Extra Theories *)
Section theory.
  Context {A B: Type} {Aeq:relation A} {Beq:relation B}.
  Context {Equiv_Aeq:Equivalence Aeq} {Equiv_Beq:Equivalence Beq}.
  Notation Bijective := (Bijective (Aeq:=Aeq) (Beq:=Beq)).
  Infix "=A=" := Aeq (at level 70).
  Infix "=B=" := Beq (at level 70).
  
  (** There exist inverse function from a bijective function.

      ref: https://stackoverflow.com/questions/62464821/
      how-to-make-an-inverse-function-in-coq

      Tips: there are two methods to formalize "existential", sig and ex.
      ex makes a Prop, sig makes a Type. 
      Here, we proof the ex version. the sig version could be derived by an axiom:
      [constructive_definite_description : 
      forall (A : Type) (P : A -> Prop), (exists ! x : A, P x) -> {x : A | P x} ]
   *)

  Lemma bij_inverse_exist : forall (phi : A -> B) (Hbij: Bijective phi),
    {psi : B -> A | (forall a : A, (psi (phi a)) =A= a) /\  (forall b : B, phi (psi b) =B= b)}.
  Proof.
    intros. destruct Hbij as [Hinj [Hsurj]].
    apply injective_eq_injective_form2 in Hinj. hnf in *.
    (* Tips, unique is eq version, we need setoid version *)
    (* assert (H : forall b, exists! a, phi a =B= b). *)
    assert (H: forall b, exists a, phi a =B= b /\ unique_setoid (Aeq:=Aeq) (fun x => phi x =B= b) a).
    { intros b.
      destruct (Hsurj b) as [a Ha]. exists a. unfold unique_setoid. repeat split; auto.
      intros a' Ha'. apply Hinj. rewrite Ha. rewrite Ha'. easy. }
    eapply constructive_definite_description_setoid.
    exists (fun b => proj1_sig (constructive_definite_description_setoid (H b))).
    split.
    - split.
      + intros a. destruct (constructive_definite_description_setoid). simpl.
        apply Hinj. auto.
      + intros b. destruct (constructive_definite_description_setoid). simpl. auto.
    - hnf. split.
      + split.
        * intros. destruct (constructive_definite_description_setoid). simpl.
          apply Hinj. auto.
        * intros. destruct (constructive_definite_description_setoid). simpl. auto.
      + intros psi [H1 H2].
        eapply functional_extensionality_setoid.
        intros b. destruct (constructive_definite_description_setoid). simpl.
        assert (phi (psi b) =B= b); auto using H2.
        rewrite <- H0 in b0. apply Hinj in b0. exact b0.
        Unshelve. exact eq.
  Defined.

  (** A bijective function preserve equal relation *)
  (* Lemma bij_pres_eq_forward : forall (f : A -> B), *)
  (*     Bijective f -> (forall (a1 a2 : A), Aeq a1 a2 -> Beq (f a1) (f a2)). *)
  (* Proof. *)
  (*   intros. destruct H as [H1 H2]. *)
  (*   (* I can't prove now. *) *)
  (*   Abort. *)
    

End theory.

(** ** Examples *)



(* ######################################################################### *)
(** * Homomorphic  *)

(** ** Class *)

Class Homomorphic {A B : Type} {Beq: relation B}
  (fa : A -> A -> A) (fb : B -> B -> B) (phi: A -> B) := {
    homomorphic : forall (a1 a2 : A), Beq (phi (fa a1 a2)) (fb (phi a1) (phi a2))
  }.

(** ** Instances *)

(** ** Extra Theories *)

(* Definition homo_inj (phi : A -> B) : Prop := *)
(*   homomorphic phi /\ injective phi. *)

(* (** phi is a homomorphic and surjective mapping *) *)
(* Definition homo_surj (phi : A -> B) : Prop := *)
(*   homomorphic phi /\ surjective phi. *)

(** ** Examples *)



(* ######################################################################### *)
(** * Homomorphism *)

(** ** Class *)

(** If there exist a homomorphic and surjective mapping from <A,+> to <B,⊕>,
    then we said <A,+> and <B,⊕> is homomorphism *)
Class Homomorphism {A B : Type} {Aeq: relation A} {Beq: relation B}
  (fa : A -> A -> A) (fb : B -> B -> B) := {
    homomorphism : exists (phi: A -> B),
      Homomorphic fa fb phi (Beq:=Beq)
      /\ Surjective phi (Beq:=Beq)
      (* need this condition, although this is not explicit in math. *)
      /\ Proper (Aeq ==> Beq) phi
  }.

(** If there exist two homomorphic and surjective mapping from <A,+> to <B,⊕>
    and from <A,*> to <B,⊗>, then we said <A,+,*> and <B,⊕,⊗> is homomorphism *)
Class Homomorphism2 {A B : Type} {Aeq: relation A} {Beq: relation B}
  (fa ga : A -> A -> A) (fb gb : B -> B -> B) := {
    homomorphism2 : exists (phi: A -> B),
      Homomorphic fa fb phi (Beq:=Beq)
      /\ Homomorphic ga gb phi (Beq:=Beq)
      /\ Surjective phi (Beq:=Beq)
      (* need this condition, although this is not explicit in math. *)
      /\ Proper (Aeq ==> Beq) phi
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Isomorphism *)

(** ** Class *)

(** If there exist a homomorphic and bijective mapping from <A,+> to <B,⊕>,
    then we said <A,+> and <B,⊕> is isomorphism *)
Class Isomorphism {A B : Type} {Aeq: relation A} {Beq: relation B}
  (fa : A -> A -> A) (fb : B -> B -> B) := {
    isomorphism : exists (phi: A -> B),
      Homomorphic fa fb phi (Beq:=Beq)
      /\ Bijective phi (Aeq:=Aeq) (Beq:=Beq)
      (* need this condition, although this is not explicit in math. *)
      /\ Proper (Aeq ==> Beq) phi
  }.

(** If there exist two homomorphic and bijective mapping from <A,+> to <B,⊕>
    and from <A,*> to <B,⊗>, then we said <A,+,*> and <B,⊕,⊗> is isomorphism *)
Class Isomorphism2 {A B : Type} {Aeq: relation A} {Beq: relation B}
  (fa ga : A -> A -> A) (fb gb : B -> B -> B) := {
    isomorphism2 : exists (phi: A -> B),
      Homomorphic fa fb phi (Beq:=Beq)
      /\ Homomorphic ga gb phi (Beq:=Beq)
      /\ Bijective phi (Aeq:=Aeq) (Beq:=Beq)
      (* need this condition, although this is not explicit in math. *)
      /\ Proper (Aeq ==> Beq) phi
  }.

(** ** Instances *)

(** ** Extra Theories *)

(** ** Examples *)



(* ######################################################################### *)
(** * Monoid *)

(** ** Class *)
Class Monoid {A:Type} (Aadd : A -> A -> A) (Azero : A) (Aeq:A->A->Prop) := {
    monoidAaddProper :> Proper (Aeq ==> Aeq ==> Aeq) Aadd;
    monoidEquiv :> Equivalence Aeq;
    monoidAssoc :> Associative Aadd Aeq;
    monoidIdL :> IdentityLeft Aadd Azero Aeq;
    monoidIdR :> IdentityRight Aadd Azero Aeq;
  }.

(** ** Instances *)
Section Instances.

  Import Arith ZArith Qcanon Reals.
  
  Global Instance Monoid_NatAdd : Monoid Nat.add 0%nat eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_NatMul : Monoid Nat.mul 1%nat eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_ZAdd : Monoid Z.add 0%Z eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_ZMul : Monoid Z.mul 1%Z eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_QcAdd : Monoid Qcplus 0 eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_QcMul : Monoid Qcmult 1 eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_RAdd : Monoid Rplus 0%R eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

  Global Instance Monoid_RMul : Monoid Rmult 1%R eq.
  repeat constructor; auto with wd; try apply eq_equivalence; intros; ring. Qed.

End Instances.

(** ** Extra Theories *)
(* What' a theory? a group of properties related to this sturcture *)

(* deprecated *)
(** monoid rewriting, need manualy specify the name of a Instance.
    It is strict, but less automated. *)
Ltac monoid_rw_old M :=
  rewrite (@associative _ _ _ (@monoidAssoc _ _ _ M)) ||
    rewrite (@identityLeft _ _ _ _ (@monoidIdL _ _ _ M)) ||
    rewrite (@identityRight _ _ _ _ (@monoidIdR _ _ _ M)).

Ltac monoid_simpl_old M := intros; repeat monoid_rw_old M; auto.

(** monoid rewriting, automatic inference the Instance. But sometimes it will fail *)
Ltac monoid_rw :=
  rewrite identityLeft ||
    rewrite identityRight ||
    rewrite associative.

Ltac monoid_simpl := intros; repeat monoid_rw; try reflexivity; auto.

Section Theory.
  Context `{M:Monoid}.
  Infix "+" := Aadd : A_scope.
  Infix "==" := Aeq : A_scope.

End Theory.

(** ** Examples *)

Section Examples.
  
  Import Reals.

  Goal forall a b c : R, ((a * b) * c = a * (b * c))%R.
  Proof.
    apply associative.
  Qed.

End Examples.


(* ######################################################################### *)
(** * Abelian monoid *)

(** ** Class *)
Class AMonoid {A} Aadd Azero Aeq := {
    amonoidMonoid :> @Monoid A Aadd Azero Aeq;
    amonoidComm :> Commutative Aadd Aeq;
  }.

(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  Global Instance AMonoid_QcAdd : AMonoid Qcplus 0 eq.
  split_intro; subst; ring. Defined.

  Global Instance AMonoid_QcMul : AMonoid Qcmult 1 eq.
  split_intro; subst; ring. Defined.

  Global Instance AMonoid_RAdd : AMonoid Rplus 0%R eq.
  split_intro; subst; ring. Defined.

  Global Instance AMonoid_RMul : AMonoid Rmult 1%R eq.
  split_intro; subst; ring. Defined.

End Instances.

  
(** ** Extra Theories *)

Ltac amonoid_simpl :=
  monoid_simpl;
  apply commutative.

(* Section Theory. *)

(*   Context `(AM : AMonoid). *)
(*   Infix "*" := op. *)

(*   Lemma amonoid_comm : forall a b, a * b = b * a. *)
(*   Proof. apply comm. Qed. *)

(*   Lemma amonoid_comm' : forall a b, a * b = b * a. *)
(*   Proof. destruct AM. auto. Qed. *)

(* End Theory. *)

(** ** Examples *)
Section Examples.

  Import Qcanon.
  
  Goal forall a b : Qc, a * b = b * a.
  Proof.
    amonoid_simpl.
  Qed.

End Examples.



(* ######################################################################### *)
(** * Group *)

(** ** Class *)
Class Group {A} Aadd Azero (Aopp : A -> A) Aeq := {
    groupMonoid :> @Monoid A Aadd Azero Aeq;
    groupInvL :> InverseLeft Aadd Azero Aopp Aeq;
    groupInvR :> InverseRight Aadd Azero Aopp Aeq;
    groupAaddProper :> Proper (Aeq ==> Aeq ==> Aeq) Aadd;
    groupAoppProper :> Proper (Aeq ==> Aeq) Aopp;
    (* groupDistrAinv :> DistributiveUnary Aop Ainv Aeq; *)
    (* groupInvoAinv :> Involution Ainv Aeq; *)
  }.

(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  Global Instance Group_QcAdd : Group Qcplus 0 Qcopp eq.
  split_intro; subst; ring. Defined.

  Global Instance Group_RAdd : Group Rplus 0%R Ropp eq.
  split_intro; subst; ring. Defined.

End Instances.


(** ** Extra Theories *)

Ltac group_rw :=
  rewrite inverseLeft ||
    rewrite inverseRight.

Ltac group_simpl :=
  repeat (group_rw || monoid_rw || group_rw);
  try reflexivity;
  auto.

(*
  Group Theory

  1.  Arkansas Tech University / Dr. Marcel B. Finan /
      MATH 4033: Elementary Modern Algebra
  
  (a) 5 Definition and Examples of Groups
  https://faculty.atu.edu/mfinan/4033/absalg5.pdf
  (b) 14 Elementary Properties of Groups
  https://faculty.atu.edu/mfinan/4033/absalg14.pdf
 *)
Section GroupTheory.
  
  Context `{G:Group}.
  Infix "==" := Aeq.
  Infix "+" := Aadd.
  Notation "0" := Azero.
  Notation "- a" := (Aopp a).
  Notation Asub := (fun x y => x + (-y)).
  Infix "-" := Asub.

  (** *** Additional properties. *)
  Section additional_props.

    (** - 0 = 0 *)
    Theorem group_opp_zero_eq_zero : - 0 == 0.
    Proof.
      pose proof (inverseLeft 0). rewrite identityRight in H. auto.
    Qed.

    (** Asub is proper morphism *)
    Lemma Asub_aeq_mor : Proper (Aeq ==> Aeq ==> Aeq) Asub.
    Proof.
      unfold Proper, respectful.
      intros. rewrite H,H0. easy.
    Qed.

    Global Existing Instance Asub_aeq_mor.

  End additional_props.
  
  (** Theorem 5.1 *)
  (* Note that, I give two theorem rather than one. *)
  Theorem group_id_uniq_l : forall e',
      (forall a, e' + a == a) -> e' == 0.
  Proof.
    intros.
    (* e = e' + e = e' *)
    assert (e' == e' + 0). { rewrite identityRight. reflexivity. }
    assert (e' + 0 == 0); auto.
    rewrite H0. rewrite <- H1 at 2. reflexivity.
  Qed.

  Theorem group_id_uniq_r : forall e', (forall a, a + e' == a) -> e' == 0.
  Proof.
    intros.
    (* e = e + e' = e' *)
    assert (0 == 0 + e'). { rewrite H. easy. }
    assert (0 + e' == e') by group_simpl.
    apply transitivity with (0 + e'); auto. group_simpl.
  Qed.

  (* Note that, I give two theorem rather than one. *)
  Theorem group_inv_uniq_l : forall x1 x2 y,
      x1 + y == 0 /\ y + x2 == 0 -> x1 == x2.
  Proof.
    intros. destruct H as [Ha Hb].
    (* x1 == x1+e == x1+(y+x2) == (x1+y)+x2 == e+x2 == x2 *)
    assert (x1 == x1 + 0) by group_simpl.
    rewrite H. rewrite <- Hb. rewrite <- associative.
    rewrite Ha. group_simpl.
  Qed.

  Theorem group_inv_uniq_r :
    (forall x y1 y2, x + y1 == 0 /\ y2 + x == 0 -> y1 == y2).
  Proof.
    intros. destruct H as [Ha Hb].
    (* y1 == e+y1 == (y2+x)+y1 == y2+(x+y1) == y2+e == y2 *)
    assert (y1 == 0 + y1). group_simpl.
    rewrite H. rewrite <- Hb. rewrite associative.
    rewrite Ha. group_simpl.
  Qed.

  (** Theorem 14.1 *)
  Theorem group_cancel_l : forall x y1 y2, x + y1 == x + y2 -> y1 == y2.
  Proof.
    intros.
    (* y1 == e+y1 == (-x+x)+y1 == (-x)+(x+y1) == (-x)+(x+y1) 
      == (-x+x)+y1 == e+y1 == y1*)
    rewrite <- identityLeft.
    assert (0 == (-x) + x). group_simpl.
    rewrite H0. rewrite associative. rewrite H.
    rewrite <- associative. group_simpl.
  Qed.

  Theorem group_cancel_r : forall x1 x2 y, x1 + y == x2 + y -> x1 == x2.
  Proof.
    intros.
    (* x1 = x1+e = x1+(y+ -y) = (x1+y)+(-y) = (x2+y)+(-y)
      = x2+(y+ -y) = x2+e = x2 *)
    rewrite <- identityRight.
    assert (0 == y + (-y)). group_simpl.
    rewrite H0. rewrite <- associative. rewrite H.
    rewrite associative. group_simpl.
  Qed.

  Theorem group_inv_inv : forall x,  - - x == x.
  Proof.
    intros. apply group_cancel_l with (- x). group_simpl.
  Qed.

  Theorem group_inv_distr : forall x y, - (x + y) == (- y) + (- x).
  Proof.
    intros.
    (* (x+y)+ -(x+y) = e = x+ -x = x+e+ -x = x+(y+ -y)+ -x
      = (x+y)+(-y+ -x), by cancel_l, got it *)
    apply group_cancel_l with (x + y).
    rewrite inverseRight. rewrite <- associative. rewrite (associative x y).
    group_simpl.
  Qed.
    
  (** Theorem 14.2 *)
  (* a + x = b -> x = (-a) + b *)
  Theorem group_equation_sol_l : forall a b x, a + x == b -> x == (- a) + b.
  Proof.
    intros.
    (* left mult a *)
    apply group_cancel_l with (a).
    rewrite <- associative. group_simpl.
  Qed.

  (* a + x = b /\ a + y = b -> x = -a + b /\ y = -a + b *)
  Theorem group_equation_sol_l_uniq : 
    forall a b x y, (a + x == b /\ a + y == b) -> (x == -a + b /\ y == -a + b).
  Proof.
    intros. destruct H. split.
    apply group_equation_sol_l; auto.
    apply group_equation_sol_l; auto.
  Qed.

  (* x + a = b -> x = b + (-a) *)
  Theorem group_equation_sol_r : forall a b x, x + a == b -> x == b + (- a).
  Proof.
    intros.
    (* right mult a *)
    apply group_cancel_r with (a). group_simpl.
  Qed.

  (* (x + a = b /\ y + a = b) -> (x = b + -a /\ y = b + -a) *)
  Theorem group_equation_sol_r_uniq : 
    forall a b x y, (x + a == b /\ y + a == b) -> (x == b + (- a) /\ y == b + (- a)).
  Proof.
    intros; destruct H. split.
    apply group_equation_sol_r; auto.
    apply group_equation_sol_r; auto.
  Qed.

  (** Definition 14.1 (multiple operations) *)
  (* batch : list A -> A
    [] = e
    [a1] = a1
    [a1;a2] = a1 * a2
    [a1;a2;a3] = (a1*a2)*a3
    [a1;a2;...;a_n-1;an] = ((...(a1*a2)* ... )*a_n-1)*an *)
  Definition group_batch (l:list A) :=
    match l with
    | [] => 0
    | x :: l' => fold_left Aadd l' x
    end.
  
  Section test.
    Variable (a1 a2 a3 a4 : A).
    
    (* Compute group_batch []. *)
    (* Compute group_batch [a1]. *)
    (* Compute group_batch [a1;a2]. *)
    (* Compute group_batch [a1;a2;a3]. *)
    (* Compute group_batch [a1;a2;a3;a4]. *)

  End test.

  (** Theorem 14.3 (Generalized Associative Law) *)
  Section th14_3.

    Notation "'Σ' a '&' l " := (fold_left Aadd l a) (at level 10).
    
    Theorem group_assoc_general (l1 l2 : list A) :
      (group_batch l1) + (group_batch l2) ==  group_batch (l1 ++ l2).
    Proof.
      (* reduct to fold_left *)
      destruct l1,l2; simpl; group_simpl.
      - rewrite app_nil_r. group_simpl.
      - rename a into a1, a0 into a2.
        (* H1. forall a l1 l2, Σ a & (l1 ++ l2) = Σ (Σ a & l1) & l2
           H2. forall a b l, a + Σ b & l = Σ (a + b) & l
           H3. forall a b l, Σ a & (b :: l) = Σ (a + b) & l
           by H1, right = Σ (Σ a1 & l1) & (a2 :: l2).
           by H2, left  = Σ ((Σ a1 & l1) + a2) & l2).
           remember (Σ a1 & l1) as c, then goal become to
              Σ (c + a2) & l2 = Σ c & (a2 :: l2)
           by H3, we got it. *)
        assert (forall a l1 l2, Σ a & (l1 ++ l2) == Σ (Σ a & l1) & l2) as H1.
        { intros a l0. gd a. induction l0; intros; try reflexivity.
          simpl. rewrite IHl0. reflexivity. }
        assert (forall a b l, a + Σ b & l == Σ (a + b) & l) as H2.
        { intros. gd b. gd a. induction l; simpl; intros; try reflexivity.
          simpl. rewrite IHl.
          (** fold_left preveres the aeq *)
          assert (forall l a1 a2, a1 == a2 -> Σ a1 & l == Σ a2 & l).
          { induction l0; intros; simpl in *; auto.
            apply IHl0. rewrite H. easy. }
          apply H. group_simpl. }
        assert (forall a b l, Σ a & (b :: l) = Σ (a + b) & l) as H3.
        { intros. gd b. gd a. induction l; auto. }
        rewrite H1. rewrite H2. rewrite H3. easy.
    Qed.
    
  End th14_3.

  Section th14_4.

    Import ZArith.

    (** Definition 14.2 (power)
      a ^ 0      = e
      a ^ n      = a ^ (n-1) * a, for n >= 1
      a ^ (-n)   = (-a) ^ n,  for n >= 1
     *)
    Definition group_power (a : A) (n : Z) : A :=
      match n with
      | Z0 => 0
      | Zpos m => iterate (fun x => Aadd x a) (Pos.to_nat m) 0
      | Z.neg m => iterate (fun x => Aadd x (Aopp a)) (Pos.to_nat m) 0
      end.
    Infix "^" := group_power.
    
    Section test.
      Variable (a1 a2 a3 a4 : A).
      (* Compute group_power a1 3. *)
      (* Compute group_power a1 (-3). *)

    End test.

    (** Remark 14.2 *)
    Lemma group_power_eq1 (n : Z) :
      match n with
      | Z0 => forall a, a ^ n = 0
      | Zpos m => forall a, a ^ n = group_batch (repeat a (Z.to_nat n))
      | Zneg m => forall a, a ^ n = group_batch (repeat (-a) (Z.to_nat (-n)))
      end.
    Proof.
      destruct n; intros; auto.
    Admitted.

    (** Theorem 14.4 *)
    Theorem group_power_inv : forall a n, (a^n) + (a^(- n)) = 0.
    Admitted.

    Theorem group_power_plus : forall a m n, (a^m) + (a^n) = a^(m+n).
    Admitted.

    Theorem group_power_mul : forall a m n, (a^m)^n = a^(m*n).
    Admitted.

  End th14_4.

  
  (** *** Below, these properties are not in textbook *)
  
  Theorem group_inv_id : - 0 == 0.
  Proof.
    intros.
    (* -e = -e + e = e *)
    rewrite <- identityRight. group_simpl.
  Qed.

End GroupTheory.

(** ** Examples *)
Section Examples.
  
  Import Reals.
  
  Goal forall x1 x2 y : R, (x1 + y = 0 /\ y + x2 = 0 -> x1 = x2)%R.
    apply group_inv_uniq_l. Qed.

End Examples.


(* ######################################################################### *)
(** * Abelian Group *)
(* ######################################################################### *)
(** ** Class *)
(** ** Instances *)
(** ** Extra Theories *)
(** ** Examples *)

(* ======================================================================= *)
(** ** Definition and theory *)

Class AGroup {A} Aadd Azero Aopp Aeq := {
    agroupGroup :> @Group A Aadd Azero Aopp Aeq;
    agroupAM :> @AMonoid A Aadd Azero Aeq;
    agroupComm :> Commutative Aadd Aeq;
  }.

Section Theory.
  
  Context `{AG : AGroup}.
  Infix "+" := Aadd.
  Infix "==" := Aeq.
  Notation "- a" := (Aopp a).
  Notation "a - b" := (a + (-b)).

  Lemma agroup_sub_comm : forall a b, a - b == - (b - a).
  Proof.
    intros.
    rewrite (group_inv_distr). rewrite (group_inv_inv). easy.
  Qed.
  
  Lemma agroup_sub_perm : forall a b c, (a - b) - c == (a - c) - b.
  Proof.
    intros.
    rewrite ?associative. rewrite (commutative (-b)). easy.
  Qed.
  
  Lemma agroup_sub_distr : forall a b, - (a + b) == -a + (-b).
  Proof.
    intros. rewrite (group_inv_distr). apply commutative.
  Qed.
  
  Lemma agroup_sub_assoc : forall a b c, (a - b) - c == a - (b + c).
  Proof.
    intros. rewrite ?associative. rewrite agroup_sub_distr. easy.
  Qed.
  
End Theory.

(* ======================================================================= *)
(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  Global Instance AGroup_QcAdd : AGroup Qcplus 0 Qcopp eq.
  split_intro; subst; ring. Defined.

  Global Instance AGroup_RAdd : AGroup Rplus 0%R Ropp eq.
  split_intro; subst; ring. Defined.

  Goal forall a b c : R, ((a - b) - c = a - (b + c))%R.
    intros.
    apply agroup_sub_assoc. Qed.

End Instances.


(* ######################################################################### *)
(** * Ring *)

(** ** Class *)

(* Note that, in mathematics, mul needn't commutative, but ring_theory in Coq 
  need it. Because we want use ring tactic, so add this properties. *)
Class Ring {A} Aadd Azero Aopp Amul Aone Aeq := {
    ringAddAG :> @AGroup A Aadd Azero Aopp Aeq;
    ringMulAM :> @AMonoid A Amul Aone Aeq;
    ringDistrL :> DistributiveLeft Aadd Amul Aeq;
    ringDistrR :> DistributiveRight Aadd Amul Aeq;
  }.

(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  Global Instance Ring_Qc : Ring Qcplus 0 Qcopp Qcmult 1 eq.
  split_intro; subst; ring. Defined.

  Global Instance Ring_R : Ring Rplus R0 Ropp Rmult R1 eq.
  split_intro; subst; ring. Defined.

End Instances.

(** ** Extra Theories *)
Section Theory.

  Context `{R:Ring}.

  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + -b)%A.
  Infix "*" := Amul : A_scope.

  Lemma make_ring_theory : ring_theory Azero Aone Aadd Amul Asub Aopp Aeq.
  Proof.
    constructor; intros;
      try (rewrite ?identityLeft,?associative; reflexivity);
      try (rewrite commutative; reflexivity).
    rewrite distributiveRight; reflexivity.
    rewrite inverseRight; reflexivity.
  Qed.

  Add Ring ring_inst : make_ring_theory.

End Theory.

(** ** Examples *)

Section Examples.

  Import Reals.
  
  Goal forall a b c : R, (a * (b + c) = a * b + a * c)%R.
    apply distributiveLeft. Qed.

End Examples.


(** This example declares an abstract ring structure, and shows how to use fewer code 
    to enable "ring" tactic. *)
Module Demo_AbsRing.
  Context `{R:Ring}.
  Infix "+" := Aadd. Infix "*" := Amul. Infix "==" := Aeq.
  Notation "0" := Azero. Notation "1" := Aone.

  Let ring_thy : ring_theory Azero Aone Aadd Amul (fun x y => Aadd x (Aopp y))
                   Aopp Aeq := make_ring_theory.

  Add Ring ring_thy_inst : ring_thy.

  Goal forall a b c : A, (a + b) * c == 0 + b * c * 1 + 0 + 1 * c * a.
  Proof. intros. ring. Qed.
  
End Demo_AbsRing.

(** This is a concrete ring structure *)
Module Demo_ConcrateRing.
  (*
A={a b e}.
+ 0 1 2 3
0 0 1 2 3
1 1 2 3 0
2 2 3 0 1

* 0 1 2 3
0 0 0 0 0
1 0 1 2 3
2 0 2 0 2
3 0 3 2 1
   *)
  Inductive A := A0 | A1 | A2 | A3.
  Notation "0" := A0. Notation "1" := A1.
  Notation "2" := A2. Notation "3" := A3.

  Definition add  (a b : A) :=
    match a,b with
    | 0,_ => b
    | 1,0 => 1 | 1,1 => 2 | 1,2 => 3 | 1,3 => 0
    | 2,0 => 2 | 2,1 => 3 | 2,2 => 0 | 2,3 => 1
    | 3,0 => 3 | 3,1 => 0 | 3,2 => 1 | 3,3 => 2
    end.
  Infix "+" := add.

  Definition opp (a:A) :=
    match a with
    | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1
    end.
  Notation "- a" := (opp a).
  Notation "a - b" := (a + (-b)).
  
  Definition mul  (a b : A) :=
    match a,b with
    | 0,_ => 0
    | 1,_ => b
    | 2,0 => 0 | 2,1 => 2 | 2,2 => 0 | 2,3 => 2
    | 3,0 => 0 | 3,1 => 3 | 3,2 => 2 | 3,3 => 1
    end.
  Infix "*" := mul.

  Lemma add_comm : forall a b, a + b = b + a.
  Proof. destruct a,b; auto. Qed.
  
  Lemma ring_thy : ring_theory 0 1 add mul (fun x y => add x (opp y)) opp eq.
  Proof.
    constructor; auto;
      try (destruct x,y; auto); try destruct z; auto.
    intros. destruct x; auto.
  Qed.

  Add Ring ring_thy_inst : ring_thy.

  Goal forall a b c : A, a + b + c - b = a + c.
  Proof.
    (* Tips, the proof is simple *)
    intros. ring.
  Qed.
  
End Demo_ConcrateRing.
  

(* ######################################################################### *)
(** * Field *)

(** ** Class *)
Class Field {A} Aadd Azero Aopp Amul Aone Ainv Aeq := {
    (** Field: Ring + mult inversion + (1≠0) *)
    fieldRing :> @Ring A Aadd Azero Aopp Amul Aone Aeq;
    field_mulInvL : forall a, ~(Aeq a Azero) -> Aeq (Amul (Ainv a) a) Aone;
    field_1_neq_0 : ~(Aeq Aone Azero);
    (** additional: Ainv is proper morphism *)
    fieldAinvProper :> Proper (Aeq ==> Aeq) Ainv
  }.

(** ** Instances *)
Section Instances.

  Import Qcanon Reals.
  
  Global Instance Field_Qc : Field Qcplus 0 Qcopp Qcmult 1 Qcinv eq.
  split_intro; subst; (try (field; reflexivity)); try easy.
  field. auto.
  Defined.

  Global Instance Field_R : Field Rplus R0 Ropp Rmult R1 Rinv eq.
  split_intro; subst; try (field; reflexivity); auto.
  field; auto. auto with real.
  Defined.

End Instances.


(** ** Extra Theories *)
Section Theory.

  Context `{F:Field}.
  Infix "==" := Aeq : A_scope.
  Infix "!=" := (fun x y => ~ x == y)%A : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + -b)%A.
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv := (fun a b => a * (/b))%A.
  Infix "/" := Adiv : A_scope.

  Lemma make_field_theory :
    field_theory Azero Aone Aadd Amul Asub Aopp Adiv Ainv Aeq.
  Proof.
    constructor; intros;
      try (rewrite ?identityLeft,?associative; reflexivity);
      try (rewrite commutative; reflexivity).
    apply make_ring_theory.
    apply field_1_neq_0.
    apply field_mulInvL. auto.
  Qed.

  Add Field field_inst : make_field_theory.

  (** a <> 0 -> /a * a = 1 *)
  Lemma field_mul_inv_l : forall a : A, ~(a == 0)%A -> (/a * a == 1)%A.
  Proof. intros. rewrite field_mulInvL; easy. Qed.

  (** a <> 0 -> a * /a = 1 *)
  Lemma field_mul_inv_r : forall a : A, ~(a == 0)%A -> (a * /a == 1)%A.
  Proof. intros. rewrite commutative. rewrite field_mulInvL; easy. Qed.

  (** a <> 0 -> (1/a) * a = 1 *)
  Lemma field_mul_inv1_l : forall a : A, ~(a == 0)%A -> ((Aone/a) * a == 1)%A.
  Proof. intros. simpl. group_simpl. apply field_mul_inv_l. auto. Qed.
  
  (** a <> 0 -> a * (1/a) = 1 *)
  Lemma field_mul_inv1_r : forall a : A, ~(a == 0)%A -> (a * (Aone/a) == 1)%A.
  Proof. intros. simpl. group_simpl. apply field_mul_inv_r. auto. Qed.
  
  (** a <> 0 -> a * b = a * c -> b = c *)
  Lemma field_mul_cancel_l : forall a b c : A,
      (a != 0)%A -> (a * b == a * c)%A -> (b == c)%A.
  Proof.
    intros.
    assert (/a * (a * b) == /a * (a * c))%A.
    { rewrite H0. easy. }
    rewrite <- ?associative in H1.
    rewrite field_mulInvL in H1; auto.
    rewrite ?identityLeft in H1. easy.
  Qed.

  (** c <> 0 -> a * c = b * c -> a = b *)
  Lemma field_mul_cancel_r : forall a b c : A,
      (c != 0)%A -> (a * c == b * c)%A -> (a == b)%A.
  Proof.
    intros.
    assert ((a * c) * /c == (b * c) * /c)%A.
    { rewrite H0. easy. }
    rewrite ?associative in H1.
    rewrite field_mul_inv_r in H1; auto.
    rewrite ?identityRight in H1. easy.
  Qed.

  (** a * b = 0 -> a = 0 \/ b = 0 *)
  Lemma field_mul_eq0_imply_a0_or_b0 : forall (a b : A) (HDec:Decidable Aeq),
      (a * b == 0)%A -> (a == 0)%A \/ (b == 0)%A.
  Proof.
    intros.
    destruct (decidable a 0)%A, (decidable b 0)%A;
      try (left; easy); try (right; easy).
    assert (/a * a * b == 0)%A.
    { rewrite associative. rewrite H. field. auto. }
    rewrite field_mulInvL in H0; auto.
    rewrite identityLeft in H0. easy.
  Qed.

End Theory.

(** ** Examples *)
Section Examples.

  Import Reals.
  
  Goal forall a b : R, (a <> 0 -> /a * a = 1)%R.
    intros. apply field_mulInvL. auto. Qed.

End Examples.

