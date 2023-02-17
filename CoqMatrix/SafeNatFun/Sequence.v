(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : auxiliary library for sequence.
  author    : ZhengPu Shi
  date      : 2022.06
 *)

Require Import Nat PeanoNat Lia Bool.
Require Export BasicConfig HierarchySetoid.


Generalizable Variable A B C Aeq Beq Ceq Aadd Aopp Amul Ainv.

(* ######################################################################### *)
(** * Sequence by function, f : nat -> A  *)

Open Scope nat_scope.
Open Scope A_scope.

(* ======================================================================= *)
(** ** Equality of sequence *)
Section seqeq.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  
  (** Equality of two sequence *)
  Definition seqeq n (f g : nat -> A) := forall i, i < n -> f i == g i.
  
  (** seqeq of Sn has a equivalent form. *)
  Lemma seqeq_Sn : forall n (f g : nat -> A), 
      seqeq (S n) f g <->
        (seqeq n f g) /\ (f n = g n).
  Proof.
    split.
    - intros. split; auto. unfold seqeq. auto.
    - unfold seqeq. intros. destruct H. destruct (i =? n)%nat eqn : E1.
      + apply Nat.eqb_eq in E1. subst; auto.
      + apply Nat.eqb_neq in E1. apply H. lia.
  Qed.
  
  (** Boolean equality of two sequence *)
  Fixpoint seqeqb n (f g : nat -> A) : bool :=
    match n with
    | O => true
    | 1 => Xeqb (f 0)%nat (g 0)%nat
    | S n' => (seqeqb n' f g) && Xeqb (f n') (g n')
    end.
  
  (** seqeqb of Sn has a equivalent form. *)
  Lemma seqeqb_Sn : forall {n} (f g : nat -> A), 
      seqeqb (S n) f g = (seqeqb n f g) && (Xeqb (f n) (g n)).
  Proof.
    intros. destruct n; auto.
  Qed.
  
  (** seqeqb = true <-> seqeq *)
  Lemma seqeqb_true_iff : forall n f g, seqeqb n f g = true <-> seqeq n f g.
  Proof.
    induction n; intros.
    - unfold seqeqb, seqeq. split; intros; auto. lia.
    - rewrite seqeqb_Sn. rewrite seqeq_Sn.
      rewrite andb_true_iff.
      (* s1 <-> t1 -> s2 <-> t2 -> s1 /\ s2 <-> t1 /\ t2 *)
      apply ZifyClasses.and_morph; auto.
      apply Xeqb_true_iff.
  Qed.
  
  (** seqeqb = false <-> ~seqeq *)
  Lemma seqeqb_false_iff : forall n f g, 
      seqeqb n f g = false <-> ~(seqeq n f g).
  Proof.
    induction n; intros.
    - unfold seqeqb, seqeq. split; intros; try easy. destruct H. easy.
    - rewrite seqeqb_Sn. rewrite seqeq_Sn.
      rewrite andb_false_iff.
      rewrite IHn. rewrite Xeqb_false_iff. split; intros H.
      + apply Classical_Prop.or_not_and; auto.
      + apply Classical_Prop.not_and_or in H; auto.
  Qed.
  
  (** seqeq is decidable *)
  Lemma seqeq_dec : forall n f g, {@seqeq n f g} + {~(@seqeq n f g)}.
  Proof.
    intros. destruct (seqeqb n f g) eqn:E1.
    - left. apply seqeqb_true_iff in E1. auto.
    - right. apply seqeqb_false_iff in E1. auto.
  Qed.
  
End Equality.


(* ======================================================================= *)
(** ** Equality of sequence with two index *)
Section Equality2.
  
  (** Equality of two sequence *)
  Definition seq2eq r c (f g : nat -> nat -> A) := 
    forall ri ci, ri < r -> ci < c -> f ri ci = g ri ci.
  
  (** seq2eq of Sr has a equivalent form. *)
  Lemma seq2eq_Sr : forall r c (f g : nat -> nat -> A), 
      seq2eq (S r) c f g <->
        (seq2eq r c f g) /\ (seqeq c (f r) (g r)).
  Proof.
    split.
    - intros. split; auto.
      + unfold seq2eq in *. intros. apply H; auto.
      + unfold seq2eq, seqeq in *. intros. auto.
    - unfold seq2eq,seqeq. intros. destruct H.
      destruct (ri =? r)%nat eqn : E1.
      + apply Nat.eqb_eq in E1. subst; auto.
      + apply Nat.eqb_neq in E1. apply H; auto. lia.
  Qed.
  
  (** Boolean equality of two sequence *)
  Fixpoint seq2eqb r c (f g : nat -> nat -> A) : bool :=
    match r with
    | O => true
    | 1 => seqeqb c (f 0)%nat (g 0)%nat
    | S r' => (seq2eqb r' c f g) && (seqeqb c (f r') (g r')) 
    end.
  
  (** seq2eqb of Sr has a equivalent form. *)
  Lemma seq2eqb_Sr : forall r c (f g : nat -> nat -> A), 
      seq2eqb (S r) c f g = (seq2eqb r c f g) && (seqeqb c (f r) (g r)).
  Proof.
    intros. destruct r; auto.
  Qed.
  
  (** seq2eqb = true <-> seq2eq *)
  Lemma seq2eqb_true_iff : forall r c f g, 
      seq2eqb r c f g = true <-> seq2eq r c f g.
  Proof.
    induction r; intros.
    - unfold seq2eqb, seq2eq. split; intros; auto. lia.
    - rewrite seq2eqb_Sr. rewrite seq2eq_Sr.
      rewrite andb_true_iff.
      (* s1 <-> t1 -> s2 <-> t2 -> s1 /\ s2 <-> t1 /\ t2 *)
      apply ZifyClasses.and_morph; auto.
      apply seqeqb_true_iff.
  Qed.
  
  (** seq2eqb = false <-> ~seq2eq *)
  Lemma seq2eqb_false_iff : forall r c f g, 
      seq2eqb r c f g = false <-> ~(seq2eq r c f g).
  Proof.
    induction r; intros.
    - unfold seq2eqb, seq2eq. split; intros; try easy. destruct H. easy.
    - rewrite seq2eqb_Sr. rewrite seq2eq_Sr.
      rewrite andb_false_iff.
      rewrite IHr. rewrite seqeqb_false_iff. split; intros H.
      + apply Classical_Prop.or_not_and; auto.
      + apply Classical_Prop.not_and_or in H; auto.
  Qed.
  
  (** seq2eq is decidable *)
  Lemma seq2eq_dec : forall r c f g, {seq2eq r c f g} + {~(seq2eq r c f g)}.
  Proof.
    intros. destruct (seq2eqb r c f g) eqn:E1.
    - left. apply seq2eqb_true_iff in E1. auto.
    - right. apply seq2eqb_false_iff in E1. auto.
  Qed.
  
End Equality2.


(* ======================================================================= *)
(** ** Sum of a sequence *)
Section Sum.
  
  (** Same sequence and same index get same element *)
  Lemma f_equal_gen : forall {X B} (f g : A -> B) a b, 
      f = g -> a = b -> f a = g b.
  Proof.
    intros. subst. reflexivity.
  Qed.
  
  (** Sum of a sequence *)
  Fixpoint seqsum (f : nat -> A) (n : nat) : A := 
    match n with
    | O => X0
    | S n' => seqsum f n' + f n'
    end.
  
  (** Sum of a sequence which every element is zero get zero. *)
  Lemma seqsum_seq0 : forall (f : nat -> A) (n : nat), 
      (forall i, (i < n) -> f i = X0) -> seqsum f n = X0.
  Proof.
    intros f n H. induction n; auto.
    simpl. rewrite H; auto. rewrite IHn; auto. ring.
  Qed.
  
  (** Corresponding elements of two sequences are equal, imply the sum are 
      equal. *)
  Lemma seqsum_eq : forall (f g : nat -> A) (n : nat),
      (forall i, i < n -> f i = g i) ->
      seqsum f n = seqsum g n.
  Proof. 
    intros f g n H. 
    induction n; simpl; auto.
    rewrite H, IHn; auto.
  Qed.
  
  (** Sum with plus of two sequence equal to plus with two sum. *)
  Lemma seqsum_plusSeq : forall (f g : nat -> A) (n : nat),
      seqsum (fun i => f i + g i) n = seqsum f n + seqsum g n.  
  Proof. 
    intros f g n. induction n; simpl. ring.
    rewrite IHn. ring.
  Qed.

  (** Constant left multiply to the sum of a sequence. *)
  Lemma seqsum_cmul_l : forall c (f : nat -> A) (n : nat),
      c * seqsum f n = seqsum (fun i => c * f i) n.  
  Proof.  
    intros c f n. induction n; simpl; try ring.
    ring_simplify. rewrite IHn. ring.
  Qed.

  (** Constant right multiply to the sum of a sequence. *)
  Lemma seqsum_cmul_r : forall c (f : nat -> A) (n : nat),
      seqsum f n * c = seqsum (fun i => f i * c) n.  
  Proof.
    intros c f n. induction n; simpl; try ring.
    ring_simplify. rewrite IHn. ring.
  Qed.

  (** Sum a sequence which only one item in nonzero, then got this item. *)
  Lemma seqsum_unique : forall (f : nat -> A) (k : A) (n i : nat), 
      (i < n) -> f i = k -> (forall j, i <> j -> f j = X0) ->
      seqsum f n = k.
  Proof.
    (* key idea: induction n, and case {x =? n} *)
    intros f k n. induction n; intros. easy. simpl.
    destruct (i =? n)%nat eqn : E1.
    - apply Nat.eqb_eq in E1. subst.
      assert (seqsum f n = X0).
      { apply seqsum_seq0. intros. apply H1. subst. lia. }
      rewrite H0. ring.
    - apply Nat.eqb_neq in E1.
      assert (f n = X0).
      { apply H1; auto. }
      assert (seqsum f n = k).
      { apply IHn with i; auto. lia. }
      rewrite H3,H2. ring.
  Qed.
  
  (** Add the sum and a tail element *)
  Lemma seqsum_extend_r : forall n f, 
      seqsum f n + f n = seqsum f (S n).
  Proof.
    reflexivity.
  Qed.
  
  (** Add a head element and the sum *)
  Lemma seqsum_extend_l : forall n f, 
      f O + seqsum (fun i => f (S i)) n = seqsum f (S n).
  Proof.
    intros n f. induction n.
    - simpl. ring.
    - simpl. ring_simplify. rewrite IHn. simpl. ring.
  Qed.

  (** Sum the m+n elements equal to plus of two parts.
      Σ[i,0,(m+n)] f(i) = Σ[i,0,m] f(i) + Σ[i,0,n] f(m + i). *)
  Lemma seqsum_plusIdx : forall m n f, seqsum f (m + n) =
                                    seqsum f m + seqsum (fun i => f (m + i)%nat) n. 
  Proof.
    intros m n f.
    induction m.
    - simpl. ring_simplify. auto.
    - simpl. rewrite IHm.
      rewrite ?add_assoc. f_equal.
      remember (fun x => f (m + x)%nat) as g.
      replace (f (m + n)%nat) with (g n).
      2:{ subst. auto. }
      replace (f m) with (g 0%nat).
      2:{ subst. f_equal. auto. }
      rewrite seqsum_extend_r.
      replace (seqsum (fun x : nat => f (S (m + x))) n) with
        (seqsum (fun x : nat => g (S x)) n).
      2:{ subst. apply seqsum_eq. intros. f_equal. auto. }
      rewrite seqsum_extend_l.
      auto.
  Qed.

  (** Product two sum equal to sum of products.
      Σ[i,0,m] f(i) * Σ[i,0,n] g(i) = Σ[i,0,m*n] f(i/n)*g(i%n).
    
      For example:
        (a + b + c) * (x + y) = a*x + a*y + b*x + b*y + c*x + c*y
   *)
  Lemma seqsum_product : forall m n f g, n <> O ->
                                    seqsum f m * seqsum g n = 
                                      seqsum (fun i => f (i / n)%nat * g (i mod n)%nat) (m * n). 
  Proof.
    intros.
    induction m.
    - simpl. ring.
    - simpl. ring_simplify. rewrite IHm. clear IHm.
      remember ((fun i : nat => f (i / n)%nat * g (i mod n)%nat)) as h.
      rewrite seqsum_cmul_l.
      (* Σ[i,0,n] f(m)*g(i) = Σ[i,0,n] f((m*n+i)/n)*g((m*n+i)%n) *)
      replace (seqsum (fun i : nat => f m * g i) n) 
        with (seqsum (fun i : nat => h ((m * n) + i)%nat) n).
      + rewrite <- seqsum_plusIdx. f_equal. apply Nat.add_comm.
      + subst.
        apply seqsum_eq.
        intros i Hi. f_equal.
        * f_equal.
          (* (m * n + i) / n = m *)
          rewrite Nat.div_add_l; auto.  (* a * b + c) / b = a + c / b *)
          rewrite Nat.div_small; auto.  (* a < b -> a / b = 0 *)
        * f_equal.
          (* (m * n + i) % n = i *)
          rewrite Nat.add_mod; auto.  (* (a + b) % n = a % n + b % n) % n *)
          rewrite Nat.mod_mul; auto.  (* (a * b) mod b = 0 *)
          rewrite Nat.add_0_l.
          repeat rewrite Nat.mod_small; auto. (* a < b -> a % b = 0 *)
  Qed.
  
End Sum.

End Sequence.


Module Sequence_test.
  
  Import Reals.
  Module Import SequenceR := Sequence (FieldR.FieldDefR).
  Open Scope R_scope.
  
  (*   Example seq1 := fun n => R_of_ Z.of_nat n. *)
  (*   Compute seqsum seq1 3. *)
  
  (*   Print Aeqb. *)
  (*   Eval simpl in seqeqb 5 seq1 seq1. *)
  (*   Compute seqeqb 5 seq1 seq1. *)
  
  (*   Example seq2 := fun i j => Z.of_nat i + Z.of_nat j. *)
  (*   Eval simpl in seq2eqb 2 3 seq2 seq2. *)
  (*   Compute seq2eqb 2 3 seq2 seq2. *)
  
End Sequence_test. 

