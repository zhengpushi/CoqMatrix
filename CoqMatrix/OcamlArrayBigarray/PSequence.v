
Require Export NatExt Hierarchy.

(* Sum of a sequence with tail recursion *)
Section seqsum.
  Context `{HAMonoid : AMonoid}.
  Notation "0" := Azero : A_scope.
  Infix "+" := Aadd : A_scope.

  (* 从左到右（从头到尾）的序列求和，非尾递归实现，方便证明。
       ∑(n,f,a) := (((0 + f[0]) + f[1]) + ...) + f[n-1] *)
  Fixpoint seqsumLeft (n : nat) (f : nat -> A) : A :=
    match n with
    | O => 0
    | S n' => seqsumLeft n' f + f n'
    end.

  (* 从右到左（从尾到头）的序列求和，尾递归实现。
       ∑(n,f) = f[0] + (... (f[n-2] + (f[n-1] + 0)) ...)  *)
  Fixpoint seqsumAux (n : nat) (f : nat -> A) (acc : A) : A :=
    match n with
    | O => acc
    | S n' => seqsumAux n' f (f n' + acc)
    end.
  Definition seqsum (n : nat) (f : nat -> A) : A := seqsumAux n f 0.

  (* seqsumAux可以替换初始值 *)
  Lemma seqsumAux_rebase : forall n f a, seqsumAux n f a = seqsumAux n f 0 + a.
  Proof.
    induction n; intros; simpl. amonoid.
    rewrite IHn. rewrite IHn with (a:=f n + 0). amonoid.
  Qed.

  (* seqsum等于seqsumLeft *)
  Lemma seqsum_eq_seqsumLeft : forall n f, seqsum n f = seqsumLeft n f.
  Proof.
    unfold seqsum. induction n; intros; simpl. auto.
    rewrite seqsumAux_rebase. rewrite IHn. amonoid.
  Qed.

  (** Sum a sequence of (S n) elements, equal to addition of Sum and tail *)
  Lemma seqsumS_tail : forall f n, seqsum (S n) f = seqsum n f + f n.
  Proof. unfold seqsum. intros; simpl. rewrite seqsumAux_rebase. amonoid. Qed.
  
  (** Sum a sequence of (S n) elements, equal to addition of head and Sum *)
  Lemma seqsumS_head : forall n f, seqsum (S n) f = f O + seqsum n (fun i => f (S i)).
  Proof.
    unfold seqsum. induction n; intros; simpl. auto.
    rewrite seqsumAux_rebase with (a:=(f (S n) + 0)).
    rewrite <- !associative. rewrite <- IHn. simpl.
    rewrite seqsumAux_rebase. rewrite seqsumAux_rebase with (a:=(f n + 0)). amonoid.
  Qed.

  (* seqsum with length 0 equal to 0 *)
  Lemma seqsum0 : forall f, seqsum 0 f = 0.
  Proof. intros. auto. Qed.

  (** Sum of a sequence which every element is zero get zero. *)
  Lemma seqsum_eq0 : forall (n : nat) (f : nat -> A), 
      (forall i, i < n -> f i = 0) -> seqsum n f = 0.
  Proof.
    unfold seqsum. induction n; simpl; intros. auto.
    rewrite seqsumAux_rebase. rewrite IHn; auto. rewrite H; auto. amonoid.
  Qed.

  (** Two sequences are equal, imply the sum are equal. *)
  Lemma seqsum_eq : forall (n : nat) (f g : nat -> A),
      (forall i, i < n -> f i = g i) -> seqsum n f = seqsum n g.
  Proof.
    induction n; intros; simpl. rewrite !seqsum0. auto.
    rewrite !seqsumS_tail. rewrite IHn with (g:=g); auto. f_equal; auto.
  Qed.
  
  (** Sum with plus of two sequence equal to plus with two sum. *)
  Lemma seqsum_add : forall (n : nat) (f g h : nat -> A),
      (forall i, i < n -> f i + g i = h i) -> seqsum n f + seqsum n g = seqsum n h.
  Proof.
    intros. induction n; simpl. rewrite !seqsum0. amonoid.
    rewrite !seqsumS_tail. rewrite <- H; auto. amonoid.
  Qed.

  (** Sum with plus of two sequence equal to plus with two sum (simple form). *)
  Lemma seqsum_add' : forall (n : nat) (f g : nat -> A),
      seqsum n f + seqsum n g = seqsum n (fun i => f i + g i).
  Proof.
    intros. rewrite seqsum_add with (h:=fun i => f i + g i); auto.
  Qed.

  (** Sum a sequence which only one item is nonzero, then got this item. *)
  Lemma seqsum_unique : forall (n : nat) (f : nat -> A) (a : A) (i : nat), 
      i < n -> f i = a -> (forall j, j < n -> j <> i -> f j = 0) -> seqsum n f = a.
  Proof.
    induction n; intros. lia.
    rewrite seqsumS_tail. bdestruct (i =? n).
    - subst. rewrite seqsum_eq0. amonoid. intros. apply H1; lia.
    - rewrite IHn with (a:=a)(i:=i); auto; try lia. rewrite H1; auto. amonoid.
  Qed.

  (** Sum the m+n elements equal to plus of two parts.
      Σ[i,0,(m+n)] f(i) = Σ[i,0,m] f(i) + Σ[i,0,n] f(m + i). *)
  Lemma seqsum_plusIdx : forall m n f,
      seqsum (m + n) f = seqsum m f + seqsum n (fun i => f (m + i)%nat). 
  Proof.
    (* induction on `n` is simpler than on `m` *)
    intros. induction n.
    - rewrite seqsum0. rewrite Nat.add_0_r. amonoid.
    - replace (m + S n)%nat with (S (m + n))%nat; auto.
      rewrite !seqsumS_tail. rewrite IHn. amonoid.
  Qed.
  
  (** Sum the m+n elements equal to plus of two parts.
      (i < m -> f(i) = g(i)) ->
      (i < n -> f(m+i) = h(i)) ->
      Σ[i,0,(m+n)] f(i) = Σ[i,0,m] g(i) + Σ[i,0,n] h(i). *)
  Lemma seqsum_plusIdx_ext : forall m n f g h,
      (forall i, i < m -> f i = g i) ->
      (forall i, i < n -> f (m + i)%nat = h i) ->
      seqsum (m + n) f = seqsum m g + seqsum n h.
  Proof.
    intros. induction n; simpl.
    - rewrite seqsum0. rewrite Nat.add_0_r. amonoid. apply seqsum_eq. auto.
    - replace (m + S n)%nat with (S (m + n))%nat; auto.
      rewrite !seqsumS_tail. rewrite IHn; auto. agroup.
  Qed.
  
  (** The order of two nested summations can be exchanged.
      ∑[i,0,r](∑[j,0,c] f_ij) = 
      f00 + f01 + ... + f0c + 
      f10 + f11 + ... + f1c + 
      ...
      fr0 + fr1 + ... + frc = 
      ∑[j,0,c](∑[i,0,r] f_ij) *)
  Lemma seqsum_seqsum : forall r c f,
      seqsum r (fun i => seqsum c (fun j => f i j)) =
        seqsum c (fun j => seqsum r (fun i => f i j)).
  Proof.
    induction r; intros.
    - rewrite !seqsum0. rewrite seqsum_eq0; auto.
    - rewrite seqsumS_tail. rewrite IHr. apply seqsum_add.
      intros. rewrite seqsumS_tail. auto.
  Qed.

  
  (** Let's have a group structure *)
  Context `{G : Group A Aadd Azero}.
  Notation "- a" := (Aopp a) : A_scope.
  
  (** Opposition of the sum of a sequence. *)
  Lemma seqsum_opp : forall (n : nat) (f g : nat -> A),
      (forall i, i < n -> f i = - g i) -> - (seqsum n f) = seqsum n g.
  Proof.
    induction n; intros; simpl.
    - rewrite !seqsum0. group.
    - rewrite !seqsumS_tail. group. rewrite commutative. f_equal; auto.
      rewrite H; auto. group.
  Qed.
  
  (** Opposition of the sum of a sequence (simple form). *)
  Lemma seqsum_opp' : forall (n : nat) (f : nat -> A),
      - (seqsum n f) = seqsum n (fun i => - f i).
  Proof.
    intros. apply seqsum_opp. intros. group.
  Qed.


  Context `{HARing : ARing A Aadd Azero}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := Amul : A_scope.
  
  (* (** Scalar multiplication of the sum of a sequence. *) *)
  (* Lemma seqsum_cmul : forall (n : nat) (f g : nat -> A) (k : A), *)
  (*     (forall i, i < n -> k * f i = g i) -> k * seqsum n f = seqsum n g. *)
  (* Proof. *)
  (*   induction n; intros. rewrite !seqsum0. ring. *)
  (*   rewrite !seqsumS_tail. ring_simplify. rewrite IHn with (g:=g); auto. *)
  (*   rewrite H; auto. *)
  (* Qed. *)

  (** Scalar multiplication of the sum of a sequence (simple form). *)
  Lemma seqsum_cmul_l : forall (n : nat) (f : nat -> A) (k : A),
      k * seqsum n f = seqsum n (fun i => k * f i).
  Proof.
    induction n; intros; simpl.
    - rewrite !seqsum0. ring.
    - rewrite !seqsumS_tail. ring_simplify. rewrite <- IHn. ring.
  Qed.

  (** Scalar multiplication of the sum of a sequence (simple form). *)
  Lemma seqsum_cmul_r : forall (n : nat) (f : nat -> A) (k : A),
      seqsum n f * k = seqsum n (fun i => f i * k).
  Proof.
    induction n; intros; simpl.
    - rewrite !seqsum0. ring.
    - rewrite !seqsumS_tail. ring_simplify. rewrite <- IHn. ring.
  Qed.
End seqsum.
