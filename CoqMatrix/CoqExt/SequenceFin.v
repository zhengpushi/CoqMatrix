(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : auxiliary library for sequence (fin version).
  author    : ZhengPu Shi
  date      : 2023.09
 *)

Require Import Nat PeanoNat Lia Bool.
Require Export BasicConfig HierarchySetoid.
Require Import Fin.
Require Reals.


Generalizable Variable A B C Aeq Beq Ceq Azero Aone Aadd Aopp Amul Ainv.

(* ######################################################################### *)
(** * Sequence by function, f : nat -> A  *)

Open Scope nat_scope.
Open Scope A_scope.

Declare Scope seq_scope.
Delimit Scope seq_scope with seq.
Open Scope seq_scope.

Declare Scope seq2_scope.
Delimit Scope seq2_scope with seq2.
Open Scope seq2_scope.

(* ======================================================================= *)
(** ** Equality of sequence *)
Section seqeq.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.

  (** Equality of two sequence which have one index *)
  Definition seqeq n (f g : Fin.t n -> A) := forall i, f i == g i.

  (** seqeq is a equivalence relation *)
  Section seqeq_equiv.
    Context {n : nat}.
    Infix "==" := (seqeq n) : A_scope.
    Lemma seqeq_refl : forall (f : Fin.t n -> A), f == f.
    Proof.
      intros. hnf. easy.
    Qed.

    Lemma seqeq_sym : forall (f g : Fin.t n -> A), f == g -> g == f.
    Proof.
      intros. hnf in *. intros. rewrite <- H; auto. easy.
    Qed.

    Lemma seqeq_trans : forall (f g h : Fin.t n -> A), f == g -> g == h -> f == h.
    Proof.
      intros. hnf in *. intros. rewrite H, <- H0; auto. easy.
    Qed.

    Lemma seqeq_equiv : Equivalence (seqeq n).
    Proof.
      intros. constructor; intro; intros.
      apply seqeq_refl.
      apply seqeq_sym; auto.
      apply seqeq_trans with y; auto.
    Qed.

    Global Existing Instance seqeq_equiv.
  End seqeq_equiv.


  (** seqeq of S has a equivalent form. *)
  (* Lemma seqeq_S : forall n (f g : Fin.t n -> A), *)
  (*     let f' := fun i => *)
  (*     seqeq (S n) f g <-> (seqeq n f g) /\ (f n == g n). *)
  (*     seqeq (S n) f g <-> (seqeq n f g) /\ (f n == g n). *)
  (* Proof. *)
  (*   split; intros. *)
  (*   - split; auto. unfold seqeq in *. auto. *)
  (*   - unfold seqeq in *. intros. destruct H. *)
  (*     destruct (i =? n) eqn:E1. *)
  (*     + apply Nat.eqb_eq in E1. subst; auto. *)
  (*     + apply Nat.eqb_neq in E1. apply H. lia. *)
  (* Qed. *)
  
  (** seqeq is decidable  *)
  (* Lemma seqeq_dec `{Dec_Aeq : Decidable A Aeq} : forall n, Decidable (seqeq n). *)
  (* Proof. *)
  (*   induction n; constructor; intros. *)
  (*   - left. unfold seqeq. easy. *)
  (*   - unfold seqeq in *. *)
  (*     destruct (decidable a b), (decidable (a n) (b n)). *)
  (*     + left. intros. destruct (i =? n) eqn:E1. *)
  (*       apply Nat.eqb_eq in E1; subst; auto. *)
  (*       apply Nat.eqb_neq in E1. apply a0. lia. *)
  (*     + right. intro. destruct n0. apply H. auto. *)
  (*     + right. intro. destruct n0. intros. auto. *)
  (*     + right. intro. destruct n0. intros. auto. *)
  (* Qed. *)

  (** *** seqeq is decidable with the help of bool equality *)
  Section seqeq_dec_with_eqb.
    
    Context {Aeqb : A -> A -> bool}.
    Context {Aeqb_true_iff : forall a b : A, Aeqb a b = true <-> Aeq a b}.
    Context {Aeqb_false_iff : forall a b : A, Aeqb a b = false <-> ~(Aeq a b)}.

    (** Boolean equality of two sequence *)
    (* Fixpoint seqeqb n (f g : Fin.t (S n) -> A) : bool := *)
    (*   match n with *)
    (*   | O => true *)
    (*   | 1 => Aeqb (f F1) (g F1) *)
    (*   | S n' => *)
    (*       (* (seqeqb n' f g) && *) *)
    (*         Aeqb (f n') (g n') *)
    (*   end. *)
    (* Fixpoint seqeqb n (f g : Fin.t n -> A) : bool := *)
    (*   match n with *)
    (*   | O => true *)
    (*   | 1 => Aeqb (f F1)%nat (g F1)%nat *)
    (*   | S n' => (seqeqb n' f g) && Aeqb (f n') (g n') *)
    (*   end. *)
    
    (** seqeqb of S has a equivalent form. *)
    (* Lemma seqeqb_S : forall {n} (f g : nat -> A),  *)
    (*     seqeqb (S n) f g = (seqeqb n f g) && (Aeqb (f n) (g n)). *)
    (* Proof. *)
    (*   intros. destruct n; auto. *)
    (* Qed. *)
    
    (** seqeqb = true <-> seqeq *)
    (* Lemma seqeqb_true_iff : forall n f g, seqeqb n f g = true <-> seqeq n f g. *)
    (* Proof. *)
    (*   induction n; intros. *)
    (*   - unfold seqeqb, seqeq. split; intros; auto. lia. *)
    (*   - rewrite seqeqb_S. rewrite seqeq_S. *)
    (*     rewrite andb_true_iff. *)
    (*     (* s1 <-> t1 -> s2 <-> t2 -> s1 /\ s2 <-> t1 /\ t2 *) *)
    (*     apply ZifyClasses.and_morph; auto. *)
    (* Qed. *)
    
    (** seqeqb = false <-> ~seqeq *)
    (* Lemma seqeqb_false_iff : forall n f g, seqeqb n f g = false <-> ~(seqeq n f g). *)
    (* Proof. *)
    (*   induction n; intros. *)
    (*   - unfold seqeqb, seqeq. split; intros; try easy. destruct H. easy. *)
    (*   - rewrite seqeqb_S. rewrite seqeq_S. *)
    (*     rewrite andb_false_iff. *)
    (*     rewrite IHn. rewrite Aeqb_false_iff. split; intros H. *)
    (*     + apply Classical_Prop.or_not_and; auto. *)
    (*     + apply Classical_Prop.not_and_or in H; auto. *)
    (* Qed. *)
    
    (** seqeq is decidable (with the help of eqb)  *)
    (* Lemma seqeq_dec_with_eqb : forall n f g, {seqeq n f g} + {~(seqeq n f g)}. *)
    (* Proof. *)
    (*   intros. destruct (seqeqb n f g) eqn:E1. *)
    (*   - left. apply seqeqb_true_iff in E1. auto. *)
    (*   - right. apply seqeqb_false_iff in E1. auto. *)
    (* Qed. *)

    End seqeq_dec_with_eqb.
    
End seqeq.


(* ======================================================================= *)
(** ** Equality of sequence with two index *)
Section seq2eq.

  (* Context `{Equiv_Aeq : Equivalence A Aeq}. *)
  (* Infix "==" := Aeq : A_scope. *)

  (* (** Equality of two sequence which have two indexes *) *)
  (* Definition seq2eq r c (f g : nat -> nat -> A) :=  *)
  (*   forall ri ci, ri < r -> ci < c -> f ri ci == g ri ci. *)
  
  (* (** seq2eq of Sr has a equivalent form. *) *)
  (* Lemma seq2eq_Sr : forall r c (f g : nat -> nat -> A),  *)
  (*     seq2eq (S r) c f g <-> (seq2eq r c f g) /\ (seqeq (Aeq:=Aeq) c (f r) (g r)). *)
  (* Proof. *)
  (*   split. *)
  (*   - intros. split; auto. *)
  (*     + unfold seq2eq in *. intros. apply H; auto. *)
  (*     + unfold seq2eq, seqeq in *. intros. auto. *)
  (*   - unfold seq2eq,seqeq. intros. destruct H. *)
  (*     destruct (ri =? r)%nat eqn : E1. *)
  (*     + apply Nat.eqb_eq in E1. subst; auto. *)
  (*     + apply Nat.eqb_neq in E1. apply H; auto. lia. *)
  (* Qed. *)

  (* (** seq2eq is a equivalence relation *) *)
  
  (* Lemma seq2eq_refl : forall r c (f : nat -> nat -> A), let R := seq2eq r c in R f f. *)
  (* Proof. *)
  (*   intros. hnf. easy. *)
  (* Qed. *)

  (* Lemma seq2eq_sym : forall r c (f g : nat -> nat -> A), let R := seq2eq r c in R f g -> R g f. *)
  (* Proof. *)
  (*   intros. hnf in *. intros. rewrite <- H; auto. easy. *)
  (* Qed. *)

  (* Lemma seq2eq_trans : forall r c (f g h : nat -> nat -> A), *)
  (*     let R := seq2eq r c in R f g -> R g h -> R f h. *)
  (* Proof. *)
  (*   intros. hnf in *. intros. rewrite H, <- H0; auto. easy. *)
  (* Qed. *)

  (* Lemma seq2eq_equiv : forall r c, Equivalence (seq2eq r c). *)
  (* Proof. *)
  (*   intros. constructor; intro; intros. *)
  (*   apply seq2eq_refl. *)
  (*   apply seq2eq_sym; auto. *)
  (*   apply seq2eq_trans with y; auto. *)
  (* Qed. *)

  (* Global Existing Instance seq2eq_equiv. *)

  
  (* (** *** seq2eq is decidable with the help of bool equality *) *)
  (* Section seq2eq_dec_with_eqb. *)
    
  (*   Context {Aeqb : A -> A -> bool}. *)
  (*   Context {Aeqb_true_iff : forall a b : A, Aeqb a b = true <-> Aeq a b}. *)
  (*   Context {Aeqb_false_iff : forall a b : A, Aeqb a b = false <-> ~(Aeq a b)}. *)

  (*   (** seq2eq is decidable  *) *)
  (*   Lemma seq2eq_dec `{Dec_Aeq : Decidable A Aeq} : forall r c, Decidable (seq2eq r c). *)
  (*   Proof. *)
  (*     induction r; constructor; intros. *)
  (*     - left. unfold seq2eq. intros. easy. *)
  (*     - unfold seq2eq in *. specialize (IHr c). *)
  (*       destruct (decidable a b). *)
  (*       + (* Tips: need to construct a prop *) *)
  (*         assert (Decidable (fun f g : nat -> nat -> A => *)
  (*                              forall ci, ci < c -> f r ci == g r ci)) as H. *)
  (*         { constructor. intros. apply seqeq_dec. } *)
  (*         destruct (@decidable _ _ H a b). *)
  (*         * left. intros. destruct (ri =? r) eqn:E1. *)
  (*           ** apply Nat.eqb_eq in E1; subst; auto. *)
  (*           ** apply Nat.eqb_neq in E1. apply a0; auto. lia. *)
  (*         * right. intro. destruct n. intros. apply H0; auto. *)
  (*       + right. intro. destruct n. intros. auto. *)
  (*   Qed. *)

  (*   (** Boolean equality of two sequence *) *)
  (*   Fixpoint seq2eqb r c (f g : nat -> nat -> A) : bool := *)
  (*     match r with *)
  (*     | O => true *)
  (*     | 1 => seqeqb (Aeqb:=Aeqb) c (f 0)%nat (g 0)%nat *)
  (*     | S r' => (seq2eqb r' c f g) && (seqeqb (Aeqb:=Aeqb) c (f r') (g r'))  *)
  (*     end. *)
    
  (*   (** seq2eqb of Sr has a equivalent form. *) *)
  (*   Lemma seq2eqb_Sr : forall r c (f g : nat -> nat -> A),  *)
  (*       seq2eqb (S r) c f g = (seq2eqb r c f g) && (seqeqb (Aeqb:=Aeqb) c (f r) (g r)). *)
  (*   Proof. *)
  (*     intros. destruct r; auto. *)
  (*   Qed. *)
    
  (*   (** seq2eqb = true <-> seq2eq *) *)
  (*   Lemma seq2eqb_true_iff : forall r c f g,  *)
  (*       seq2eqb r c f g = true <-> seq2eq r c f g. *)
  (*   Proof. *)
  (*     induction r; intros. *)
  (*     - unfold seq2eqb, seq2eq. split; intros; auto. lia. *)
  (*     - rewrite seq2eqb_Sr. rewrite seq2eq_Sr. *)
  (*       rewrite andb_true_iff. *)
  (*       (* s1 <-> t1 -> s2 <-> t2 -> s1 /\ s2 <-> t1 /\ t2 *) *)
  (*       apply ZifyClasses.and_morph; auto. *)
  (*       apply (seqeqb_true_iff (Aeqb_true_iff:=Aeqb_true_iff)). *)
  (*   Qed. *)
    
  (*   (** seq2eqb = false <-> ~seq2eq *) *)
  (*   Lemma seq2eqb_false_iff : forall r c f g,  *)
  (*       seq2eqb r c f g = false <-> ~(seq2eq r c f g). *)
  (*   Proof. *)
  (*     induction r; intros. *)
  (*     - unfold seq2eqb, seq2eq. split; intros; try easy. destruct H. easy. *)
  (*     - rewrite seq2eqb_Sr. rewrite seq2eq_Sr. *)
  (*       rewrite andb_false_iff. *)
  (*       rewrite IHr. rewrite (seqeqb_false_iff (Aeqb_false_iff:=Aeqb_false_iff)). *)
  (*       split; intros H. *)
  (*       + apply Classical_Prop.or_not_and; auto. *)
  (*       + apply Classical_Prop.not_and_or in H; auto. *)
  (*   Qed. *)
    

  (*   (** seq2eq is decidable (with the help of eqb)  *) *)
  (*   Lemma seq2eq_dec_with_eqb : forall r c f g, {seq2eq r c f g} + {~(seq2eq r c f g)}. *)
  (*   Proof. *)
  (*     intros. destruct (seq2eqb r c f g) eqn:E1. *)
  (*     - left. apply seq2eqb_true_iff in E1. auto. *)
  (*     - right. apply seq2eqb_false_iff in E1. auto. *)
  (*   Qed. *)

  (* End seq2eq_dec_with_eqb. *)
  
End seq2eq.


(* ======================================================================= *)
(** ** Sum of a sequence *)
Section Sum.

  Context `{M : AMonoid A Aadd Azero Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope.
  
  (** Sum of a sequence *)
  Fixpoint seqsum (n : nat) (f : Fin.t n -> A) (i : nat) : A :=
    match i with
    | O => Azero
    | S i' => f F1 + seqsum f n f i'
    end.

  
  (** Sum of a sequence which every element is zero get zero. *)
  Lemma seqsum_seq0 : forall (f : nat -> A) (n : nat), 
      (forall i, i < n -> f i == Azero) -> seqsum f n == Azero.
  Proof.
    intros f n H. induction n; simpl. easy.
    rewrite H; auto. rewrite IHn; auto. monoid_simpl.
  Qed.

  (** Corresponding elements of two sequences are equal, imply the sum are 
      equal. *)
  Lemma seqsum_eq : forall (f g : nat -> A) (n : nat),
      (forall i, i < n -> f i == g i) -> seqsum f n == seqsum g n.
  Proof. 
    intros f g n H. 
    induction n; simpl; auto. easy.
    rewrite H, IHn; auto. easy.
  Qed.
  
  (** Sum with plus of two sequence equal to plus with two sum. *)
  Lemma seqsum_add (Comm: Commutative Aadd Aeq) : forall (f g : nat -> A) (n : nat),
      seqsum (fun i => f i + g i) n == seqsum f n + seqsum g n.  
  Proof. 
    intros f g n. induction n; simpl. monoid_simpl. rewrite IHn.
    rewrite ?associative. f_equiv.
    rewrite <- ?associative. f_equiv.
    apply commutative.
  Qed.


  (** *** Below, we need ring structure *)
  Context `{R : Ring A Aadd Azero Aopp Amul Aone Aeq}.
  Add Ring ring_inst : make_ring_theory.
  
  Infix "*" := Amul : A_scope.

  
  (** Constant left multiply to the sum of a sequence. *)
  Lemma seqsum_cmul_l : forall c (f : nat -> A) (n : nat),
      c * seqsum f n == seqsum (fun i => c * f i) n.  
  Proof.  
    intros c f n. induction n; simpl. ring.
    ring_simplify. rewrite IHn. ring.
  Qed.

  (** Constant right multiply to the sum of a sequence. *)
  Lemma seqsum_cmul_r : forall c (f : nat -> A) (n : nat),
      seqsum f n * c == seqsum (fun i => f i * c) n.  
  Proof.
    intros c f n. induction n; simpl; try ring.
    ring_simplify. rewrite IHn. ring.
  Qed.

  (** Sum a sequence which only one item in nonzero, then got this item. *)
  Lemma seqsum_unique : forall (f : nat -> A) (k : A) (n i : nat), 
      (i < n) -> f i == k -> (forall j, i <> j -> f j == Azero) ->
      seqsum f n == k.
  Proof.
    (* key idea: induction n, and case {x =? n} *)
    intros f k n. induction n; intros. easy. simpl.
    destruct (i =? n)%nat eqn : E1.
    - apply Nat.eqb_eq in E1. subst.
      assert (seqsum f n == Azero).
      { apply seqsum_seq0. intros. apply H1. lia. }
      rewrite H0. rewrite H2. ring.
    - apply Nat.eqb_neq in E1.
      assert (f n == Azero).
      { apply H1; auto. }
      assert (seqsum f n == k).
      { apply IHn with i; auto. lia. }
      rewrite H3,H2. ring.
  Qed.
  
  (** Add the sum and a tail element *)
  Lemma seqsum_extend_r : forall n f, 
      seqsum f n + f n == seqsum f (S n).
  Proof.
    reflexivity.
  Qed.
  
  (** Add a head element and the sum *)
  Lemma seqsum_extend_l : forall n f, 
      f O + seqsum (fun i => f (S i)) n == seqsum f (S n).
  Proof.
    intros n f. induction n.
    - simpl. ring.
    - simpl. ring_simplify. rewrite IHn. simpl. ring.
  Qed.

  (** Sum the m+n elements equal to plus of two parts.
      Σ[i,0,(m+n)] f(i) = Σ[i,0,m] f(i) + Σ[i,0,n] f(m + i). *)
  Lemma seqsum_plusIdx : forall m n f,
      seqsum f (m + n) == seqsum f m + seqsum (fun i => f (m + i)%nat) n. 
  Proof.
    intros m n f.
    induction m.
    - simpl. ring_simplify. easy.
    - simpl. rewrite IHm.
      rewrite !associative. f_equiv.
      remember (fun x => f (m + x)%nat) as g.
      (* Tips: replace is not suitable for setoid, but only eq. So, use assert *)
      assert (f (m + n)%nat == g n) as H1. { subst. easy. } rewrite H1; clear H1.
      rewrite seqsum_extend_r.
      assert (f m == g 0) as H1. { subst. f_equiv. lia. } rewrite H1; clear H1.
      assert (seqsum (fun x : nat => f (S (m + x))) n ==
                seqsum (fun x : nat => g (S x)) n) as H1.
      { subst. apply seqsum_eq. intros. f_equiv. auto. } rewrite H1; clear H1.
      rewrite seqsum_extend_l.
      easy.
  Qed.

  (** Product two sum equal to sum of products.
      Σ[i,0,m] f(i) * Σ[i,0,n] g(i) = Σ[i,0,m*n] f(i/n)*g(i%n).
    
      For example:
        (a + b + c) * (x + y) = a*x + a*y + b*x + b*y + c*x + c*y
   *)
  Lemma seqsum_product : forall m n f g,
      n <> O ->
      seqsum f m * seqsum g n == seqsum (fun i => f (i / n)%nat * g (i mod n)%nat) (m * n). 
  Proof.
    intros.
    induction m.
    - simpl. ring.
    - simpl. ring_simplify. rewrite IHm; auto. clear IHm.
      remember ((fun i : nat => f (i / n)%nat * g (i mod n)%nat)) as h.
      rewrite seqsum_cmul_l.
      (* Σ[i,0,n] f(m)*g(i) = Σ[i,0,n] f((m*n+i)/n)*g((m*n+i)%n) *)
      assert (seqsum (fun i : nat => f m * g i) n ==
                seqsum (fun i : nat => h ((m * n) + i)%nat) n) as H1.
      { subst. apply seqsum_eq.
        intros i Hi. f_equiv.
        * f_equiv.
          (* (m * n + i) / n = m *)
          rewrite Nat.div_add_l; auto.  (* a * b + c) / b = a + c / b *)
          rewrite Nat.div_small; auto.  (* a < b -> a / b = 0 *)
        * f_equiv.
          (* (m * n + i) % n = i *)
          rewrite Nat.add_mod; auto.  (* (a + b) % n = a % n + b % n) % n *)
          rewrite Nat.mod_mul; auto.  (* (a * b) mod b = 0 *)
          rewrite Nat.add_0_l.
          repeat rewrite Nat.mod_small; auto. (* a < b -> a % b = 0 *)
      }
      rewrite H1; clear H1.
      rewrite <- seqsum_plusIdx. f_equiv. apply Nat.add_comm.
  Qed.
  
End Sum.


Module Sequence_test.
  
  Import Reals.

  Example seq1 := fun n => IZR (Z.of_nat n).

  (* Compute seqsum seq1 3. *)
  (* Compute @seqsum R Rplus R0 seq1 3. *)

  (* Eval simpl in seqeqb 5 seq1 seq1. *)
  (* Compute seqeqb 5 seq1 seq1. *)
  (* Compute seqeqb 5 seq1 seq1. *)
  
  Open Scope Z.
  Example seq2 := fun i j => Z.of_nat i + Z.of_nat j.
  Example seq3 := fun i j => Z.of_nat i + Z.of_nat j + 1.

  (* Eval simpl in seq2eqb 2 3 seq2 seq3. *)
  (* Compute seq2eqb (Aeqb:=Z.eqb) 2 3 seq2 seq3. *)
    
End Sequence_test. 
