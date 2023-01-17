(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : auxiliary library for sequence.
  author    : ZhengPu Shi
  date      : 2022.06
*)

Require RExt.
Require Export HierarchySetoid.


(* ######################################################################### *)
(** * Sequence by function, f : nat -> X *)

Section Sequence.
  (* use natural number *)
  Open Scope nat.
  
  Context `{R:Ring}.

  (** add is respect to aeq *)
  Add Parametric Morphism : add
      with signature aeq ==> aeq ==> aeq as ring_add_aeq_mor.
  Proof. apply respectBinary. Qed.

  (** mul is respect to aeq *)
  Add Parametric Morphism : mul
      with signature aeq ==> aeq ==> aeq as ring_mul_aeq_mor.
  Proof. apply respectBinary. Qed.

  (** opp is respect to aeq *)
  Add Parametric Morphism : opp
      with signature aeq ==> aeq as ring_opp_aeq_mor.
  Proof. apply respectUnary. Qed.

  Add Ring aring : make_ring_theory.

  Context `{ED:@EqDec A aeq}.
  
  (* notations for abstract operations of above structure *)
  Infix "==" := aeq.
  Infix "+" := add.
  Infix "*" := mul.
  
  (* ======================================================================= *)
  (** ** Equality of sequence *)
  Section Equality.
  
    (** Equality of two sequence *)
    Definition seqeq n (f g : nat -> A) := forall i, i < n -> f i == g i.
    
    (** seqeq of Sn has a equivalent form. *)
    Lemma seqeq_Sn : forall n (f g : nat -> A), 
      seqeq (S n) f g <->
      (seqeq n f g) /\ (f n == g n).
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
      | 1 => eqb (f 0)%nat (g 0)%nat
      | S n' => (seqeqb n' f g) && eqb (f n') (g n')
      end.
    
    (** seqeqb of Sn has a equivalent form. *)
    Lemma seqeqb_Sn : forall {n} (f g : nat -> A), 
      seqeqb (S n) f g = (seqeqb n f g) && (eqb (f n) (g n)).
    Proof. intros. destruct n; auto. Qed.
    
    (** seqeqb = true <-> seqeq *)
    Lemma seqeqb_true_iff : forall n f g, seqeqb n f g = true <-> seqeq n f g.
    Proof.
      induction n; intros.
      - unfold seqeqb, seqeq. split; intros; auto. lia.
      - rewrite seqeqb_Sn. rewrite seqeq_Sn.
        rewrite andb_true_iff.
        (* s1 <-> t1 -> s2 <-> t2 -> s1 /\ s2 <-> t1 /\ t2 *)
        apply ZifyClasses.and_morph; auto.
        apply eqb_true.
    Qed.
    
    (** seqeqb = false <-> ~seqeq *)
    Lemma seqeqb_false_iff : forall n f g, 
      seqeqb n f g = false <-> ~(seqeq n f g).
    Proof.
      induction n; intros.
      - unfold seqeqb, seqeq. split; intros; try easy. destruct H. easy.
      - rewrite seqeqb_Sn. rewrite seqeq_Sn.
        rewrite andb_false_iff.
        rewrite IHn.
        rewrite eqb_false. split; intros H.
        + apply Classical_Prop.or_not_and; auto.
        + apply Classical_Prop.not_and_or in H; auto.
    Qed.

    (** 核心思想：函数相等可判定，借助与计算，转换为bool。
        换言之，给出了一个判定过程 eqb，既然计算是可终止的，
        那么，这两个函数就能够判定相等，因为可枚举了。*)

    (** 继续理解：为了判断函数 f 和 g “在某种意义下相等（即seqeq）”，
        编写了辅助函数 seqeqb，它的返回值类型是bool。
        然后证明 seqeq 和 seqeqb 是互相反射的。
        最后，为证明 seqeq 是可判定的（sumbool类型），借助 seqeqb 分两种情况，
        完成了证明。
        所以，对于“函数”这类“非归纳定义的类型”进行可判定性证明时，需要借助
        某个中间结构，将无限的情形转化为有限的情形。 *)
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
      forall ri ci, ri < r -> ci < c -> f ri ci == g ri ci.
    
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
    Proof. intros. destruct r; auto. Qed.
    
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
    Lemma f_equal_gen : forall {X B} (f g : X -> B) a b, 
      f = g -> a = b -> f a = g b.
    Proof. intros. subst. reflexivity. Qed.
    
    (** Sum of a sequence *)
    Fixpoint seqsum (f : nat -> A) (n : nat) : A := 
      match n with
      | O => zero
      | S n' => seqsum f n' + f n'
      end.
    
    (** Sum of a sequence which every element is zero get zero. *)
    Lemma seqsum_seq0 : forall (f : nat -> A) (n : nat), 
      (forall i, (i < n) -> f i == zero) -> seqsum f n == zero.
    Proof.
      intros f n H. induction n; simpl; try reflexivity.
      rewrite IHn; auto. monoid_rw. apply H. auto.
    Qed.
    
    (** Corresponding elements of two sequences are equal, imply the sum are 
      equal. *)
    Lemma seqsum_eq : forall (f g : nat -> A) (n : nat),
      (forall i, i < n -> f i == g i) ->
      seqsum f n == seqsum g n.
    Proof. 
      intros f g n H. 
      induction n; simpl; try reflexivity.
      rewrite H, IHn; try reflexivity; auto.
    Qed.
      
    (** Sum with plus of two sequence equal to plus with two sum. *)
    Lemma seqsum_plusSeq : forall (f g : nat -> A) (n : nat),
      seqsum (fun i => f i + g i) n == seqsum f n + seqsum g n.  
    Proof. 
      intros f g n. induction n; simpl. ring.
      rewrite IHn. ring.
    Qed.

    (** Constant left multiply to the sum of a sequence. *)
    Lemma seqsum_cmul_l : forall c (f : nat -> A) (n : nat),
      c * seqsum f n == seqsum (fun i => c * f i) n.  
    Proof.  
      intros c f n. induction n; simpl; try ring.
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
      (i < n) -> f i == k -> (forall j, i <> j -> f j == zero) ->
      seqsum f n == k.
    Proof.
      (* key idea: induction n, and case {x =? n} *)
      intros f k n. induction n; intros. easy. simpl.
      destruct (i =? n)%nat eqn : E1.
      - apply Nat.eqb_eq in E1. subst.
        assert (seqsum f n == zero).
        { apply seqsum_seq0. intros. apply H1. lia. }
        rewrite H0. rewrite H2. ring.
      - apply Nat.eqb_neq in E1.
        assert (f n == zero). { apply H1; auto. }
        assert (seqsum f n == k). { apply IHn with i; auto. lia. }
        rewrite H3,H2. ring.
    Qed.
    
    (** Add the sum and a tail element *)
    Lemma seqsum_extend_r : forall n f, 
      seqsum f n + f n == seqsum f (S n).
    Proof. reflexivity. Qed.
    
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
    Lemma seqsum_plusIdx : forall m n f, seqsum f (m + n) ==
      seqsum f m + seqsum (fun i => f (m + i)%nat) n. 
    Proof.
      intros m n f.
      induction m.
      - simpl. ring_simplify. reflexivity.
      - simpl. rewrite IHm.
        rewrite <- ?associative.
        f_equal. (* 此策略不能用，所以写下面更复杂的语法来代替 *)
        apply ring_add_aeq_mor; try reflexivity.
        remember (fun x => f (m + x)%nat) as g.
        replace (f (m + n)%nat) with (g n) by (subst; auto).
        replace (f m) with (g 0%nat) by (subst; auto).
        rewrite seqsum_extend_r.
        assert ((seqsum (fun x : nat => f (S (m + x))) n) ==
                  (seqsum (fun x : nat => g (S x)) n)).
        { subst. apply seqsum_eq. intros.
          replace (S (m + i)) with (m + S i)%nat; auto. reflexivity. }
        rewrite H.
        rewrite seqsum_extend_l.
        reflexivity.
    Qed.

    (** Product two sum equal to sum of products.
      Σ[i,0,m] f(i) * Σ[i,0,n] g(i) = Σ[i,0,m*n] f(i/n)*g(i%n).
    
      For example:
        (a + b + c) * (x + y) = a*x + a*y + b*x + b*y + c*x + c*y
    *)
    Lemma seqsum_product : forall m n f g, n <> O ->
      seqsum f m * seqsum g n ==
      seqsum (fun i => f (i / n)%nat * g (i mod n)%nat) (m * n). 
    Proof.
      intros.
      induction m.
      - simpl. ring.
      - simpl. ring_simplify. rewrite IHm. clear IHm.
        remember ((fun i : nat => f (i / n)%nat * g (i mod n)%nat)) as h.
        rewrite seqsum_cmul_l.
        (* Σ[i,0,n] f(m)*g(i) = Σ[i,0,n] f((m*n+i)/n)*g((m*n+i)%n) *)
        assert ((seqsum (fun i : nat => f m * g i) n) ==
                  (seqsum (fun i : nat => h ((m * n) + i)%nat) n)).
        { subst.
          apply seqsum_eq.
          intros i Hi.
          f_equal. (* 此策略不能用，改用复杂的语句来实现 *)
          apply ring_mul_aeq_mor.
          - (* (m * n + i) / n = m *)
            replace ((m * n + i) / n) with m; try reflexivity.
            rewrite Nat.div_add_l; auto.  (* a * b + c) / b = a + c / b *)
            rewrite Nat.div_small; auto.  (* a < b -> a / b = 0 *)
          - (* (m * n + i) % n = i *)
            replace ((m * n + i) mod n) with i; try reflexivity.
            rewrite Nat.add_mod; auto.  (* (a + b) % n = a % n + b % n) % n *)
            rewrite Nat.mod_mul; auto.  (* (a * b) mod b = 0 *)
            rewrite Nat.add_0_l.
            repeat rewrite Nat.mod_small; auto. (* a < b -> a % b = 0 *)
        }
        rewrite H0.
        rewrite <- seqsum_plusIdx.
        rewrite Nat.add_comm. reflexivity.
    Qed.  
    
  End Sum.

End Sequence.

Module Sequence_test.
  
  Import RExt.

  Example seq1 := fun n => Z2R (Z.of_nat n).

  (** 一维数组求和 *)
  (* Compute seqsum seq1 3. *)
  (* Compute @seqsum R Rplus R0 seq1 3. *)

  (** 一维数组相等判定 *)
  (* Eval simpl in seqeqb 5 seq1 seq1. *)
  (* Compute seqeqb 5 seq1 seq1. *)
  (* 由于实数的复杂构造，无法规约到简单的值，只能得到表达式，
     但内部已经转变为 Req_EM_T 这个函数的调用，
     将来映射到OCaml时，可以给出具体的计算。*)
  (* Compute seqeqb 5 seq1 seq1. *)
  
  (** 二维数组相等判定 *)
  Open Scope Z.
  Example seq2 := fun i j => Z.of_nat i + Z.of_nat j.
  Example seq3 := fun i j => Z.of_nat i + Z.of_nat j + 1.

  Eval simpl in seq2eqb 2 3 seq2 seq3.
  Compute seq2eqb 2 3 seq2 seq3.
    
End Sequence_test. 

