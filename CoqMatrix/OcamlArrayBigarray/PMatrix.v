(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix with high performance (在Bigarray,NatFun两个模型上开发)
  author    : ZhengPu Shi
  date      : 2024.03

  remark    :
  1. Motivation:
     * develop algorithms of matrix
     * the correctness is verifiable in Coq
     * high performance supported by extracted to OCaml Array or Bigarray
     * the elements are hierarchical (optional)
  2. Design:
     * Bigarray support only integer, float and complex,
       Array support any type
     * Bigarray support multi-dimensional, Array support one-dimensional.
       Thus,
       * If use Bigarray, matrix is supported built-in
       * If use array, matrix is array of array.
         If we want update A[i,j], we must update full row.
     * There are sevel matrix, row vector, column vector, vector. Several ways to do:
       * mat and vec.
       * only mat: rvec:=1*n mat, cvec=n*1 mat, vec=cvec
   3. Our choices:
     * Bigarray
     * only mat, cvec=n*1 mat, vec=cvec, rvec is notation of (cvec\T).

 *)


Require Export Extraction NatExt ListExt Hierarchy QcExt RExt.
Require Export Extraction ExtrOcamlBasic ExtrOcamlNatInt MyExtrOCamlR.

(** Control the scope *)
Open Scope nat_scope.
Open Scope A_scope.
Open Scope mat_scope.

(** Preserved notations *)
Reserved Infix "==" (at level 70).
Reserved Notation "M .[ i , j ]"
  (at level 2, left associativity, format "M .[ i , j ]").
Reserved Notation "M .[ i , j <- a ]"
  (at level 2, left associativity, format "M .[ i , j <- a ]").
Reserved Notation "v .[ i ]"
  (at level 2, left associativity, format "v .[ i ]").
Reserved Notation "v .[ i <- a ]"
  (at level 2, left associativity, format "v .[ i <- a ]").


(** Tactics for automation *)


(* Eliminitate nat comparison *)
Ltac nat_cmp :=
  repeat (
      intros;
      let E := fresh "E" in
      try match goal with
        | [ H : context [?i ??= ?j] |- _]  => destruct (i ??= j) as [E|E]
        | [ |- context [?i ??= ?j]]        => destruct (i ??= j) as [E|E]
        | [ H : context [?i ??< ?j] |- _]  => destruct (i ??< j) as [E|E]
        | [ |- context [?i ??< ?j]]        => destruct (i ??< j) as [E|E]
        | [ H : context [?i ??<= ?j] |- _] => destruct (i ??<= j) as [E|E]
        | [ |- context [?i ??<= ?j]]       => destruct (i ??<= j) as [E|E]
        (* `i = j |- _`, use it to rewrite *)
        | [H : ?i = ?j |- _] => match type of i with | nat => try rewrite H in * end
        end;
      auto; try reflexivity; try easy; try lia; try ring).



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


(** * Matrix element *)

(** ** Interface of matrix element *)
Module Type MatrixElement.
  Parameter A : Type.
  Parameter Azero Aone : A.
  Parameter Aadd Amul : A -> A -> A.
  Parameter Aopp Ainv : A -> A.

  Axiom Field : Field Aadd Azero Aopp Amul Aone Ainv.

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.
  Notation Adiv a b := (a * /b).
  Infix "/" := Adiv : A_scope.
  
End MatrixElement.


(** ** Matrix element of Qc type, for numerical computation in Coq *)
Module MatrixElementQc <: MatrixElement.
  Export QcExt.
  Open Scope Q_scope.
  Open Scope Qc_scope.
  
  Definition A : Type := Qc.
  Definition Azero : A := 0.
  Definition Aone : A := 1.
  Definition Aadd := Qcplus.
  Definition Amul := Qcmult.
  Definition Aopp := Qcopp.
  Definition Ainv := Qcinv.

  Hint Unfold A Azero Aone Aadd Amul Aopp Ainv : A.
  
  Lemma Field : Field Aadd Azero Aopp Amul Aone Ainv.
  Proof.
  Admitted.
  (*   autounfold with A. *)
  (*   repeat constructor; intros; try ring. *)
  (*   apply field_mulInvL; auto. *)
  (*   apply R1_neq_R0. *)
  (* Qed. *)
  
End MatrixElementQc.


(** ** Matrix element of R type, for symbolic computation in Coq *)
Module MatrixElementR <: MatrixElement.
  Export Reals.
  Open Scope R_scope.
  
  Definition A : Type := R.
  Definition Azero : A := R0.
  Definition Aone : A := R1.
  Definition Aadd := Rplus.
  Definition Amul := Rmult.
  Definition Aopp := Ropp.
  Definition Ainv := Rinv.

  Hint Unfold A Azero Aone Aadd Amul Aopp Ainv : A.
  
  Lemma Field : Field Aadd Azero Aopp Amul Aone Ainv.
  Proof.
    autounfold with A.
    repeat constructor; intros; try ring.
    apply field_mulInvL; auto.
    apply R1_neq_R0.
  Qed.
  
End MatrixElementR.


(** * Matrix model *)

(** ** Interface of matrix model *)
Module Type MatrixModel (E : MatrixElement).
  Export E.
  
  (** ** operations *)

  (* matrix type *)
  Parameter mat : forall (r c : nat), Type.
  (* equality of two matrices *)
  Parameter meq : forall {r c} (M1 M2 : mat r c), Prop.
  (* M.[i,j] *)
  Parameter mget : forall {r c} (M : mat r c) (i j : nat), A.
  (* M.[i,j<-a] *)
  Parameter mset : forall {r c} (M : mat r c) (i j : nat) (a : A), mat r c.
  (* Create a matrix with default value *)
  Parameter mcreate : forall r c, mat r c.
  (* Create a matrix with a function *)
  Parameter minit : forall r c (f : nat -> nat -> A), mat r c.

  Infix "==" := meq : mat_scope.
  Notation "M .[ i , j ]" := (mget M i j) : mat_scope.
  Notation "M .[ i , j <- a ]" := (mset M i j a) : mat_scope.

  (** ** specifications *)
  
  (* meq is equivalent relation *)
  Axiom meq_equiv : forall {r c}, Equivalence (@meq r c).
  (* Two matrix are equal if all corresponding elements are equal *)
  Axiom meq_if : forall {r c} (M1 M2 : mat r c),
      (forall i j, i < r -> j < c -> M1.[i,j] = M2.[i,j]) -> M1 == M2.
  (* Two matrix are equal imply all corresponding elements are equal *)
  Axiom meq_imply : forall {r c} (M1 M2 : mat r c),
      M1 == M2 -> (forall i j, i < r -> j < c -> M1.[i,j] = M2.[i,j]).

  (* Get element of a matrix after update with same index return the new value *)
  Axiom mset_eq : forall {r c} (M : mat r c) (i j : nat) (a : A),
      i < r -> j < c -> (M.[i,j<-a]).[i,j] = a.
  (* Get element of a matrix after update with different index return the old value *)
  Axiom mset_neq_i : forall {r c} (M : mat r c) (i j i0 : nat) (a : A),
      i < r -> j < c -> i0 < r -> i <> i0 -> (M.[i,j<-a]).[i0,j] = M.[i0,j].
  Axiom mset_neq_j : forall {r c} (M : mat r c) (i j j0 : nat) (a : A),
      i < r -> j < c -> j0 < c -> j <> j0 -> (M.[i,j<-a]).[i,j0] = M.[i,j0].
  Axiom mset_neq_ij : forall {r c} (M : mat r c) (i j i0 j0 : nat) (a : A),
      i < r -> j < c -> i0 < r -> j0 < c -> i <> i0 -> j <> j0 ->
      (M.[i,j<-a]).[i0,j0] = M.[i,j].
  
  (* Update element with its own value won't change the matrix *)
  Axiom mset_same : forall {r c} (M : mat r c) (i j : nat) (a : A),
      i < r -> j < c -> M.[i,j<-M.[i,j]] == M.
  
  (* Update element twice at same position will only keep last operation *)
  Axiom mset_shadow : forall {r c} (M : mat r c) (i j : nat) (a b : A),
      i < r -> j < c -> M.[i,j<-a].[i,j<-b] == M.[i,j<-b].
  (* Update element twice at different position can exchange the operation *)
  Axiom mset_permute_i : forall {r c} (M : mat r c) (i j i0 : nat) (a b : A),
      i < r -> j < c -> i0 < r -> i <> i0 ->
      M.[i,j<-a].[i0,j<-b] == M.[i0,j<-b].[i,j<-a].
  Axiom mset_permute_j : forall {r c} (M : mat r c) (i j j0 : nat) (a b : A),
      i < r -> j < c -> j0 < c -> j <> j0 ->
      M.[i,j<-a].[i,j0<-b] == M.[i,j0<-b].[i,j<-a].
  Axiom mset_permute_ij : forall {r c} (M : mat r c) (i j i0 j0 : nat) (a b : A),
      i < r -> j < c -> i0 < r -> j0 < c -> i <> i0 -> j <> j0 ->
      M.[i,j<-a].[i0,j0<-b] == M.[i0,j0<-b].[i,j<-a].

  (* Get element from a new created matrix return zero *)
  Axiom mget_mcreate : forall {r c} (i j : nat),
      i < r -> j < c -> (mcreate r c).[i,j] = 0.
  (* Update element of a new created matrix with zero won't change it *)
  Axiom mset_mcreate_same : forall {r c} (i j : nat),
      i < r -> j < c -> (mcreate r c).[i,j<-0] == (mcreate r c).
  
  (* Get element from of a function-generated matrix yields its corresponding value *)
  Axiom mget_minit : forall {r c} f i j,
      i < r -> j < c -> (minit r c f).[i,j] = f i j.
  (* Generate matrix from function is injective *)
  Axiom minit_inj : forall {r c} (f g : nat -> nat -> A),
      minit r c f == minit r c g -> (forall i j, i < r -> j < c -> f i j = g i j).

End MatrixModel.


(** ** Matrix model by bigarray with float64, for extraction to ocaml *)
Module MatrixModel_Bigarray_Float64 <: MatrixModel (MatrixElementR).
  Export MatrixElementR.

  (* matrix type *)
  Parameter mat : forall (r c : nat), Type.
  (* equality of two matrices *)
  Parameter meq : forall {r c} (M1 M2 : mat r c), Prop.
  (* M.[i,j] *)
  Parameter mget : forall {r c} (M : mat r c) (i j : nat), A.
  (* M.[i,j<-a] *)
  Parameter mset : forall {r c} (M : mat r c) (i j : nat) (a : A), mat r c.
  (* Create a matrix with default value *)
  Parameter mcreate : forall r c, mat r c.
  (* Create a matrix with a function *)
  Parameter minit : forall r c (f : nat -> nat -> A), mat r c.

  Infix "==" := meq : mat_scope.
  Notation "M .[ i , j ]" := (mget M i j) : mat_scope.
  Notation "M .[ i , j <- a ]" := (mset M i j a) : mat_scope.


  (** ** specifications *)

  Open Scope nat_scope.
  
  (* meq is equivalent relation *)
  Axiom meq_equiv : forall {r c}, Equivalence (@meq r c).
  (* Two matrix are equal if all corresponding elements are equal *)
  Axiom meq_if : forall {r c} (M1 M2 : mat r c),
      (forall i j, i < r -> j < c -> M1.[i,j] = M2.[i,j]) -> M1 == M2.
  (* Two matrix are equal imply all corresponding elements are equal *)
  Axiom meq_imply : forall {r c} (M1 M2 : mat r c),
      M1 == M2 -> (forall i j, i < r -> j < c -> M1.[i,j] = M2.[i,j]).

  (* Get element of a matrix after update with same index return the new value *)
  Axiom mset_eq : forall {r c} (M : mat r c) (i j : nat) (a : A),
      i < r -> j < c -> (M.[i,j<-a]).[i,j] = a.
  (* Get element of a matrix after update with different index return the old value *)
  Axiom mset_neq_i : forall {r c} (M : mat r c) (i j i0 : nat) (a : A),
      i < r -> j < c -> i0 < r -> i <> i0 -> (M.[i,j<-a]).[i0,j] = M.[i0,j].
  Axiom mset_neq_j : forall {r c} (M : mat r c) (i j j0 : nat) (a : A),
      i < r -> j < c -> j0 < c -> j <> j0 -> (M.[i,j<-a]).[i,j0] = M.[i,j0].
  Axiom mset_neq_ij : forall {r c} (M : mat r c) (i j i0 j0 : nat) (a : A),
      i < r -> j < c -> i0 < r -> j0 < c -> i <> i0 -> j <> j0 ->
      (M.[i,j<-a]).[i0,j0] = M.[i,j].
  
  (* Update element with its own value won't change the matrix *)
  Axiom mset_same : forall {r c} (M : mat r c) (i j : nat) (a : A),
      i < r -> j < c -> M.[i,j<-M.[i,j]] == M.
  
  (* Update element twice at same position will only keep last operation *)
  Axiom mset_shadow : forall {r c} (M : mat r c) (i j : nat) (a b : A),
      i < r -> j < c -> M.[i,j<-a].[i,j<-b] == M.[i,j<-b].
  (* Update element twice at different position can exchange the operation *)
  Axiom mset_permute_i : forall {r c} (M : mat r c) (i j i0 : nat) (a b : A),
      i < r -> j < c -> i0 < r -> i <> i0 ->
      M.[i,j<-a].[i0,j<-b] == M.[i0,j<-b].[i,j<-a].
  Axiom mset_permute_j : forall {r c} (M : mat r c) (i j j0 : nat) (a b : A),
      i < r -> j < c -> j0 < c -> j <> j0 ->
      M.[i,j<-a].[i,j0<-b] == M.[i,j0<-b].[i,j<-a].
  Axiom mset_permute_ij : forall {r c} (M : mat r c) (i j i0 j0 : nat) (a b : A),
      i < r -> j < c -> i0 < r -> j0 < c -> i <> i0 -> j <> j0 ->
      M.[i,j<-a].[i0,j0<-b] == M.[i0,j0<-b].[i,j<-a].

  (* Get element from a new created matrix return zero *)
  Axiom mget_mcreate : forall {r c} (i j : nat),
      i < r -> j < c -> (mcreate r c).[i,j] = Azero.
  (* Update element of a new created matrix with zero won't change it *)
  Axiom mset_mcreate_same : forall {r c} (i j : nat),
      i < r -> j < c -> (mcreate r c).[i,j<-Azero] == (mcreate r c).
  
  (* Get element from of a function-generated matrix yields its corresponding value *)
  Axiom mget_minit : forall {r c} f i j,
      i < r -> j < c -> (minit r c f).[i,j] = f i j.
  (* Generate matrix from function is injective *)
  Axiom minit_inj : forall {r c} (f g : nat -> nat -> A),
      minit r c f == minit r c g -> (forall i j, i < r -> j < c -> f i j = g i j).

  (** ** controlling extraction *)
  Extract Constant mat =>
            "(float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array2.t".
  Extract Constant mget => "fun m -> Bigarray.Array2.get m".
  Extract Constant mset =>
            "fun m i j a -> Bigarray.Array2.set m i j a; m".
  Extraction Implicit mget [r c].
  Extraction Implicit mset [r c].
  Extract Constant mcreate => "Bigarray.Array2.create Float64 C_layout".
  Extract Constant minit => "Bigarray.Array2.init Float64 C_layout".
  (* Unset Extraction SafeImplicits. *)
  (* Recursive Extraction mget mcreate mset minit. *)
  Extraction "matrix.ml" mget mget mcreate mset minit.
  
End MatrixModel_Bigarray_Float64.


(** ** Matrix model by natural indexing function, for proof and computation in Coq *)
Module MatrixModel_NatFun (E : MatrixElement) <: MatrixModel E.
  Export E.

  (* matrix with natural-indexing-function and dimensions encoded by dependent type *)
  Inductive t (r c : nat) := mk_t (f : nat -> nat -> A).
  
  (* convert matrix `x` to function *)
  Definition t2f {r c} (x : t r c) : nat -> nat -> A := let '(mk_t _ _ f) := x in f.
  Coercion t2f : t >-> Funclass.

  (* matrix type *)
  Definition mat (r c : nat) := t r c.
  
  (* equality of two matrices *)
  Definition meq {r c} (M1 M2 : mat r c) : Prop :=
    forall i j, i < r -> j < c -> M1 i j = M2 i j.
  
  (* M.[i,j] *)
  Definition mget {r c} (M : mat r c) (i j : nat) : A := M i j.
  
  (* M.[i,j<-a] *)
  Definition mset {r c} (M : mat r c) (i j : nat) (a : A) : mat r c :=
    mk_t _ _ (fun i0 j0 => if (i0 =? i) && (j0 =? j) then a else M i0 j0).
  
  (* Create a matrix with default value *)
  Definition mcreate r c : mat r c := mk_t _ _ (fun i0 j0 => 0).
  
  (* Create a matrix with a function *)
  Definition minit r c (f : nat -> nat -> A) : mat r c := mk_t _ _ f.

  Infix "==" := meq : mat_scope.
  Notation "M .[ i , j ]" := (mget M i j) : mat_scope.
  Notation "M .[ i , j <- a ]" := (mset M i j a) : mat_scope.

  (** ** specifications *)

  Open Scope nat_scope.
  
  (* meq is equivalent relation *)
  Lemma meq_equiv : forall {r c}, Equivalence (@meq r c).
  Proof. Admitted.
  
  (* Two matrix are equal if all corresponding elements are equal *)
  Lemma meq_if : forall {r c} (M1 M2 : mat r c),
      (forall i j, i < r -> j < c -> M1.[i,j] = M2.[i,j]) -> M1 == M2.
  Proof. Admitted.
  (* Two matrix are equal imply all corresponding elements are equal *)
  Lemma meq_imply : forall {r c} (M1 M2 : mat r c),
      M1 == M2 -> (forall i j, i < r -> j < c -> M1.[i,j] = M2.[i,j]).
  Proof. Admitted.

  (* Get element of a matrix after update with same index return the new value *)
  Lemma mset_eq : forall {r c} (M : mat r c) (i j : nat) (a : A),
      i < r -> j < c -> (M.[i,j<-a]).[i,j] = a.
  Proof. Admitted.
  (* Get element of a matrix after update with different index return the old value *)
  Lemma mset_neq_i : forall {r c} (M : mat r c) (i j i0 : nat) (a : A),
      i < r -> j < c -> i0 < r -> i <> i0 -> (M.[i,j<-a]).[i0,j] = M.[i0,j].
  Proof. Admitted.
  Lemma mset_neq_j : forall {r c} (M : mat r c) (i j j0 : nat) (a : A),
      i < r -> j < c -> j0 < c -> j <> j0 -> (M.[i,j<-a]).[i,j0] = M.[i,j0].
  Proof. Admitted.
  Lemma mset_neq_ij : forall {r c} (M : mat r c) (i j i0 j0 : nat) (a : A),
      i < r -> j < c -> i0 < r -> j0 < c -> i <> i0 -> j <> j0 ->
      (M.[i,j<-a]).[i0,j0] = M.[i,j].
  Proof. Admitted.
  
  (* Update element with its own value won't change the matrix *)
  Lemma mset_same : forall {r c} (M : mat r c) (i j : nat) (a : A),
      i < r -> j < c -> M.[i,j<-M.[i,j]] == M.
  Proof. Admitted.
  
  (* Update element twice at same position will only keep last operation *)
  Lemma mset_shadow : forall {r c} (M : mat r c) (i j : nat) (a b : A),
      i < r -> j < c -> M.[i,j<-a].[i,j<-b] == M.[i,j<-b].
  Proof. Admitted.
  (* Update element twice at different position can exchange the operation *)
  Lemma mset_permute_i : forall {r c} (M : mat r c) (i j i0 : nat) (a b : A),
      i < r -> j < c -> i0 < r -> i <> i0 ->
      M.[i,j<-a].[i0,j<-b] == M.[i0,j<-b].[i,j<-a].
  Proof. Admitted.
  Lemma mset_permute_j : forall {r c} (M : mat r c) (i j j0 : nat) (a b : A),
      i < r -> j < c -> j0 < c -> j <> j0 ->
      M.[i,j<-a].[i,j0<-b] == M.[i,j0<-b].[i,j<-a].
  Proof. Admitted.
  Lemma mset_permute_ij : forall {r c} (M : mat r c) (i j i0 j0 : nat) (a b : A),
      i < r -> j < c -> i0 < r -> j0 < c -> i <> i0 -> j <> j0 ->
      M.[i,j<-a].[i0,j0<-b] == M.[i0,j0<-b].[i,j<-a].
  Proof. Admitted.

  (* Get element from a new created matrix return zero *)
  Lemma mget_mcreate : forall {r c} (i j : nat),
      i < r -> j < c -> (mcreate r c).[i,j] = Azero.
  Proof. Admitted.
  (* Update element of a new created matrix with zero won't change it *)
  Lemma mset_mcreate_same : forall {r c} (i j : nat),
      i < r -> j < c -> (mcreate r c).[i,j<-Azero] == (mcreate r c).
  Proof. Admitted.
  
  (* Get element from of a function-generated matrix yields its corresponding value *)
  Lemma mget_minit : forall {r c} f i j,
      i < r -> j < c -> (minit r c f).[i,j] = f i j.
  Proof. Admitted.
  (* Generate matrix from function is injective *)
  Lemma minit_inj : forall {r c} (f g : nat -> nat -> A),
      minit r c f == minit r c g -> (forall i j, i < r -> j < c -> f i j = g i j).
  Proof. Admitted.
  
End MatrixModel_NatFun.


(** * Matrix theory *)
Module MatrixTheory (E : MatrixElement) (M : MatrixModel E).
  Export M.

  Extraction Implicit M.mget [r c].
  Extraction Implicit mset [r c].

  Notation seqsum := (@seqsum _ Aadd 0).

  (** ** Extra theories for matrix element *)

  Add Field field_inst : (make_field_theory Field).
  
  Let element_ARing : ARing Aadd 0 Aopp Amul 1.
  Proof. apply Field. Qed.
  
  Let element_add_AGroup : AGroup Aadd 0 Aopp.
  Proof. apply Field. Qed.
  
  Lemma element_add_AMonoid : AMonoid Aadd 0.
  Proof. apply Field. Qed.
  

  (* Convert between function and matrix *)
  Definition f2m {r c} (f : nat -> nat -> A) : mat r c := minit r c f.
  Definition m2f {r c} (M : mat r c) : nat -> nat -> A := fun i j => M.[i,j].

  (* Convert between dlist and matrix *)
  Definition l2m {r c} (d : dlist A) : mat r c := f2m (fun i => l2f 0 c (l2f [] r d i)).
  Definition m2l {r c} (M : mat r c) : dlist A := f2l r (fun i => f2l c (m2f M i)).

  (* Algebraic operations *)
  Definition mtrans {r c} (M : mat r c) : mat c r :=
    f2m (fun i0 j0 => M.[j0,i0]).
  Notation "M \T" := (mtrans M) : mat_scope.
  
  Definition madd {r c} (M1 M2 : mat r c) : mat r c :=
    f2m (fun i0 j0 => M1.[i0,j0] + M2.[i0,j0]).
  Infix "+" := madd : mat_scope.

  Definition mmul {r c s} (M1 : mat r c) (M2 : mat c s) : mat r s :=
    f2m (fun i0 k0 => seqsum c (fun j0 => M1.[i0,j0] * M2.[j0,k0])).
  Infix "*" := mmul : mat_scope.

  Lemma mmul_assoc : forall {r c s t} (M1 : mat r c) (M2 : mat c s) (M3 : mat s t),
      (M1 * M2) * M3 == M1 * (M2 * M3).
  Proof.
    pose proof element_ARing.
    intros. apply meq_if; intros. unfold mmul, f2m. rewrite !mget_minit; auto.
    rewrite (seqsum_eq s) with
      (g:=(fun j0 : nat => seqsum c (fun j1 : nat => M1.[i,j1] * M2.[j1,j0] * M3.[j0,j])%A)).
    2:{ intros. rewrite !mget_minit; auto. rewrite seqsum_cmul_r; auto. }
    rewrite (seqsum_eq c) with
      (g:=(fun j0 : nat => seqsum s (fun j1 : nat => M1.[i,j0] * M2.[j0,j1] * M3.[j1,j])%A)).
    2:{ intros. rewrite !mget_minit; auto. rewrite seqsum_cmul_l; auto.
        apply seqsum_eq; intros. field. }
    rewrite seqsum_seqsum. auto.
  Qed.

  Extraction Implicit m2l [r c].
  
End MatrixTheory.


(** * Experiment *)

(** ** Numerical computation in Coq *)
Module test_Qc.
  Module ME := MatrixModel_NatFun MatrixElementQc.
  Module Export MT := MatrixTheory MatrixElementQc ME.
  Open Scope mat_scope.

  (** f2m, m2f *)
  Section f2m_m2f.
    
    (* [[0;2]; [1;3]] *)
    Let M := @f2m 2 2 (fun i j => nat2Qc (i+2*j)).
    Compute (M.[0,0], M.[0,1], M.[1,0], M.[1,1]).
    Compute M.[1,2].
  End f2m_m2f.

  (** l2m, m2l *)
  Section l2m_m2l.
    
    (* [[0;1]; [2;3]] *)
    Let M := @l2m 2 2 (Q2Qc_dlist [[0;1];[2;3]]%Q).
    Compute (M.[0,0], M.[0,1], M.[1,0], M.[1,1]).
    Compute m2l M.
  End l2m_m2l.

  Section algebraic.
    
    (* [0;1]  *)
    (*        [2;3] *)
    Let M1 := @l2m 2 2 (Q2Qc_dlist [[0;1];[2;3]]%Q).
    (* [0;1]    [0;2] *)
    (*        [2;3] => [1;3] *)
    Compute m2l (M1\T).
    (* [0;1]   [0;1]   [0;2] *)
    (*        [2;3] + [2;3] = [4;6] *)
    Compute m2l (M1 + M1).
    (* [0;1]   [0;1]   [2;3] *)
    (*        [2;3] * [2;3] = [6;11] *)
    Compute m2l (M1 * M1).
  End algebraic.
End test_Qc.


(** ** Symbolic computation and proof in Coq *)
Module test_R.
  Module ME := MatrixModel_NatFun MatrixElementR.
  Module Export MT := MatrixTheory MatrixElementR ME.
  Open Scope R_scope.
  Open Scope mat_scope.

  (** f2m, m2f *)
  Section f2m_m2f.
    
    (* [[0;2]; [1;3]] *)
    Let M := @f2m 2 2 (fun i j => nat2R (i+2*j)).
    Compute (M.[0,0], M.[0,1], M.[1,0], M.[1,1]).

    (* the printing is more friendly for humans *)
    Eval cbn in (M.[0,0], M.[0,1], M.[1,0], M.[1,1]).
  End f2m_m2f.

  (** l2m, m2l *)
  Section l2m_m2l.
    
    (* [[0;1]; [2;3]] *)
    Let M := @l2m 2 2 [[0;1];[2;3]].
    Compute m2l M.
  End l2m_m2l.

  Section algebraic.
    
    (* [0;1]  *)
    (*        [2;3] *)
    Let M1 := @l2m 2 2 [[0;1];[2;3]].
    (* [0;1]    [0;2] *)
    (*        [2;3] => [1;3] *)
    Compute m2l (M1\T).
    (* [0;1]   [0;1]   [0;2] *)
    (*        [2;3] + [2;3] = [4;6] *)
    Compute m2l (M1 + M1).
    (* [0;1]   [0;1]   [2;3] *)
    (*        [2;3] * [2;3] = [6;11] *)
    Compute m2l (M1 * M1).
  End algebraic.

  (* 如何证明乘法结合律 *)
  Section proof.

    (* 对于给定维数的具体矩阵，可使用计算的方式来证明 *)
    Variable a11 a12 a21 a22 : A.
    Variable b11 b12 b21 b22 : A.
    Variable c11 c12 c21 c22 : A.
    Let M1 := @l2m 2 2 [[a11;a12];[a21;a22]].
    Let M2 := @l2m 2 2 [[b11;b12];[b21;b22]].
    Let M3 := @l2m 2 2 [[c11;c12];[c21;c22]].

    Goal (M1 * M2) * M3 == M1 * (M2 * M3).
    Proof.
      apply meq_if; intros.
      (* 方法1：对索引 i,j 分解，转换为元素的等式 *)
      repeat (try destruct i; try destruct j; try lia).
      all: cbv. all: ring.
      (* 方法2：不需要分解索引，直接就能得证。 *)
      Restart.
      apply meq_if; intros.
      cbv -[nth].             (* 计算时，最好不要展开 nth *)
      ring.
    Qed.

    (* 对于给定维数的任意矩阵，也可用计算方式来证明 *)
    Variable N1 : mat 2 3.
    Variable N2 : mat 3 4.
    Variable N3 : mat 4 5.
    Goal (N1 * N2) * N3 == N1 * (N2 * N3).
    Proof.
      apply meq_if; intros. cbv. ring.
    Qed.

    (* 对于任意维度的矩阵，一般用性质来证明 *)
    Variable r c s t : nat.
    Variable P1 : mat r c.
    Variable P2 : mat c s.
    Variable P3 : mat s t.
    Goal (P1 * P2) * P3 == P1 * (P2 * P3).
    Proof. apply mmul_assoc. Qed.
  End proof.
  
End test_R.


(** ** Extracted to OCaml *)
(* Module test_Ocaml. *)
  Module ME := MatrixModel_Bigarray_Float64.
  Module Export MT := MatrixTheory MatrixElementR ME.
  (* Import ME. *)
  (* Import MT. *)
  (* Open Scope A_scope. *)
  (* Open Scope mat_scope. *)

  Extraction Implicit mget [r c].
  
  Recursive Extraction MT.
  Extraction "matrix.ml" MT. ?
                               ?
                               Recursive Extraction mtrans madd mmul.
    ?
    ？

    (* 分析矩阵乘法的命令式计算过程 *)
    Section check_mmul_bigarray.
      Variable a11 a12 a21 a22 : A.
      Variable b11 b12 b21 b22 : A.
      Let M1 := @l2m 2 2 [[a11;a12];[a21;a22]].
      Let M2 := @l2m 2 2 [[b11;b12];[b21;b22]].
      Opaque nth.
      Eval cbv in (M1 * M2).

    (* 其过程如下： *)
   (*      => [a11 a12]   [b11 b12] *)
   (*         [a21 a22] * [b21 b22] *)
   (*      => minit将构造出各个元素： *)
   (*         i0=0,k0=0: a11*b11 + a12*b21 + 0 *)
   (*         i0=0,k0=1: a11*b12 + a12*b22 + 0 *)
   (*         i0=1,k0=0: a21*b11 + a22*b21 + 0 *)
   (*         i0=1,k0=1: a21*b12 + a22*b22 + 0  *)
   (*      与命令式做法一致，只是 minit 函数的执行顺序未知。 *)
      (*      此处，由于是 l2m 构造的矩阵，所有有很多 nth 调用。 *)

   (*      下一个例子，不使用 l2m，而是使用一个假设的矩阵，看看生成的代码如何 *)
      Variable M3 M4 : mat 2 2.
      Compute (M3 * M4).
      (* = minit 2 2  *)
   (*        (fun x x0 : nat => (M3.[x,0] * M4.[0,x0] + (M3.[x,1] * M4.[1,x0] + R0))%R) *)
      (* 可以看出，计算过程还是很符合直观的 *)
    End check_mmul_bigarray.
  End test_Ocaml.

  (* ======================================================================= *)

  (** ** Cast between two [mat] type with actual equal dimensions *)

  (** Cast from [mat r1 c1] type to [mat r2 c2] type if [r1 = r2 /\ c1 = c2] *)
  Definition cast_mat {r1 c1 r2 c2} (M : mat r1 c1) : r1 = r2 -> c1 = c2 -> mat r2 c2.
    intros. subst. auto.
  Defined.


  (* ======================================================================= *)
  (** ** Equality of matrix *)
  
  Existing Instance meq_equiv.

  (* (* Proof equality of two matrixs *) *)
  (* Ltac veq := *)
  (*   repeat *)
  (*     (logic; *)
  (*      try *)
  (*        match goal with *)
  (*        | [|- ?v1 == ?v2] => apply veq_if; intros *)
  (*        | [H : ?i < S ?n |- ?a.[?i] = ?b.[?i]] => repeat (destruct i; auto; try lia) *)
  (*        | [H : ?v1 == ?v2 |- ?v1.[?i] = ?v2.[?i]] => apply veq_imply *)
  (*        end; *)
  (*      auto; try lia). *)

  (* (** The equality of 0-D matrix *) *)
  (* Lemma v0eq : forall {A} (v1 v2 : @vec A 0), v1 == v2. *)
  (* Proof. veq. Qed. *)

  (* (** The equality of 1-D matrix *) *)
  (* Lemma v1eq_iff : forall {A} (v1 v2 : @vec A 1), v1 == v2 <-> v1.1 = v2.1. *)
  (* Proof. veq. Qed. *)

  (* Lemma v1neq_iff : forall {A} (v1 v2 : @vec A 1), ~(v1 == v2) <-> v1.1 <> v2.1. *)
  (* Proof. intros. rewrite v1eq_iff; tauto. Qed. *)

  (* (** The equality of 2-D matrix *) *)
  (* Lemma v2eq_iff : forall {A} (v1 v2 : @vec A 2), v1 == v2 <-> v1.1 = v2.1 /\ v1.2 = v2.2. *)
  (* Proof. veq. Qed. *)

  (* Lemma v2neq_iff : forall {A} (v1 v2 : @vec A 2), ~(v1 == v2) <-> (v1.1 <> v2.1 \/ v1.2 <> v2.2). *)
  (* Proof. intros. rewrite v2eq_iff; tauto. Qed. *)

  (* (** The equality of 3-D matrix *) *)
  (* Lemma v3eq_iff : forall {A} (v1 v2 : @vec A 3), *)
  (*     v1 == v2 <-> v1.1 = v2.1 /\ v1.2 = v2.2 /\ v1.3 = v2.3. *)
  (* Proof. veq. Qed. *)

  (* Lemma v3neq_iff : forall {A} (v1 v2 : @vec A 3), *)
  (*     ~(v1 == v2) <-> (v1.1 <> v2.1 \/ v1.2 <> v2.2 \/ v1.3 <> v2.3). *)
  (* Proof. intros. rewrite v3eq_iff; tauto. Qed. *)

  (* (** The equality of 4-D matrix *) *)
  (* Lemma v4eq_iff : forall {A} (v1 v2 : @vec A 4), *)
  (*     v1 == v2 <-> v1.1 = v2.1 /\ v1.2 = v2.2 /\ v1.3 = v2.3 /\ v1.4 = v2.4. *)
  (* Proof. veq. Qed. *)

  (* Lemma v4neq_iff : forall {A} (v1 v2 : @vec A 4), *)
  (*     ~(v1 == v2) <-> (v1.1 <> v2.1 \/ v1.2 <> v2.2 \/ v1.3 <> v2.3 \/ v1.4 <> v2.4). *)
  (* Proof. intros. rewrite v4eq_iff; tauto. Qed. *)

  (* (** ~(v1 == v2) <-> ∃ i, u $ i <> v $ i *) *)
  (* Lemma vneq_iff_exist_nth_neq : forall {r c} (v1 v2 : @vec A n), *)
  (*     ~(v1 == v2) <-> exists i, i < r /\ v1.[i] <> v2.[i]. *)
  (* Proof. *)
  (*   intros. logic. *)
  (*   - rewrite veq_iff in H. *)
  (*     apply not_all_ex_not in H. destruct H as [n0 H]. exists n0. tauto. *)
  (*   - rewrite veq_iff. destruct H as [i H]. *)
  (*     intro. specialize (H0 i). tauto. *)
  (* Qed. *)


  (* ======================================================================= *)
  (** ** Matrix with same elements *)
  Section mconst.
    
    Definition mconst (r c : nat) (a : A) : mat r c := f2m (fun i j => a).

    (** (mconst a).[i,j] = a *)
    Lemma mget_mconst : forall {r c} a i j,
        i < r -> j < c -> (mconst r c a).[i,j] = a.
    Proof. intros. cbv. rewrite mget_minit; auto. Qed.
  End mconst.


  (* ======================================================================= *)
  (** ** Zero matrix *)
  Section mat0.
    
    Definition mat0 r c : mat r c := mconst r c 0.

    (** mat0.[i,j] = 0 *)
    Lemma nth_mat0 : forall {r c} i j, i < r -> j < c -> (mat0 r c).[i,j] = 0.
    Proof. intros. unfold mat0. rewrite mget_mconst; auto. Qed.
    
  End mat0.


  (* Eliminitate index operation *)
  Ltac idx :=
    repeat (
        intros;
        let E := fresh "E" in
        try match goal with
          (* i = i |- _ *)
          | H : ?i = ?i |- _ => clear H
          (* vzero $ i = 0 *)
          (* | [|- context [(vzero _).[?i]]] => rewrite nth_vzero *)
          (* (f2v f) i = f i *)
          (* | [ |- context [(f2v _ ?f).[?i]]]     => rewrite mget_f2v *)
          (* (a.[i<-x].[i] = x *)
          (* | [|- context [(?a.[?i<-?x]).[?i]]]                 => rewrite mset_eq *)
          (* | [H : ?i = ?j |- context [(?a.[?i<-?x]).[?j]]]     => rewrite H, mset_eq *)
          (* | [H : ?j = ?i |- context [(?a.[?i<-?x]).[?j]]]     => rewrite H, mset_eq *)
          (* (a.[i<-x].[j] = a.[j] *)
          (* | [H : ?i <> ?j |- context [(?a.[?i<-?x]).[?j]]]     => rewrite mset_neq *)
          (* | [H : ?j <> ?i |- context [(?a.[?i<-?x]).[?j]]]     => rewrite mset_neq *)
          (* (a.[i<-x].[i<-y] = a.[i<-x] *)
          (* | [ |- context [?a.[?i<-_].[?i<-_]]]      => rewrite mset_shadow *)
          (* ((mcreate a).[i<-a] = (mcreate a) *)
          (* | [ |- context [(mcreate _ ?a).[?i<-?a]]]  => rewrite mset_mcreate_same *)
          (* destruct `??=, ??<, ??<=` *)
          (* | [ H : context [?i ??= ?j] |- _]  => destruct (i ??= j) as [E|E] *)
          (* | [ |- context [?i ??= ?j]]        => destruct (i ??= j) as [E|E] *)
          (* | [ H : context [?i ??< ?j] |- _]  => destruct (i ??< j) as [E|E] *)
          (* | [ |- context [?i ??< ?j]]        => destruct (i ??< j) as [E|E] *)
          (* | [ H : context [?i ??<= ?j] |- _] => destruct (i ??<= j) as [E|E] *)
          (* | [ |- context [?i ??<= ?j]]       => destruct (i ??<= j) as [E|E] *)
          (* `i = j |- _`, use it to rewrite *)
          | [H : ?i = ?j |- _] => match type of i with | nat => try rewrite H in * end
          end;
        auto; try reflexivity; try easy; try lia; try ring).

  (* Ltac idx_perm := *)
  (*   match goal with *)
  (*   (* (a.[i<-x].[j<-y]).[i] = (a.[j<-y].[i<-x]).[i] *) *)
  (*   (* | [|- context [(?a.[?i<-?x].[?j<-?y]).[?i]]] => rewrite mset_permute *) *)
  (*   (* | [|- context [?a.[?i<-?x].[?j<-?y]]] => rewrite mset_permute *) *)
  (*   end; idx. *)
?

  (* ======================================================================= *)
  (** ** Convert between nat-index-function (f) and matrix (v) *)
  Section f2v_v2f.
    Context {A} (Azero : A).

    Definition v2f {n} (M : mat r c) : (nat -> A) := vget v.
    
    (** (f2v f).i = f i *)
    Lemma nth_f2v : forall {n} f i, i < r -> (@f2v A n f).[i] = f i.
    Proof. intros. simpl. idx. Qed.

    (** (v2f v) i = v.i *)
    Lemma nth_v2f : forall {n} (v : vec n) i, i < r -> (v2f v) i = v.[i].
    Proof. intros. unfold v2f. auto. Qed.

    (** f2v (v2f v) = v *)
    Lemma f2v_v2f : forall {n} (v : vec n), (f2v n (v2f v)) == v.
    Proof. intros. unfold v2f. veq. idx. Qed.

    (** v2f (f2v f) = f *)
    Lemma v2f_f2v : forall {n} (f : nat -> A) i, i < r -> v2f (f2v n f) i = f i.
    Proof. intros. unfold v2f. idx. Qed.

  End f2v_v2f.


  (* ======================================================================= *)
  (** ** Convert between list and matrix *)
  Section l2v_v2l.
    Context {A} (Azero : A).

    Definition l2v {n : nat} (l : list A) : @vec A n := f2v n (l2f Azero n l).

    (** (l2v l).i = nth i l *)
    Lemma nth_l2v : forall {n} (l : list A) i, i < r -> (@l2v n l).[i] = nth i l Azero.
    Proof. intros. unfold l2v. rewrite nth_f2v; auto. Qed.

    (** l2v l1 = l2v l2 -> l1 = l2 *)
    Lemma l2v_inj : forall {n} (l1 l2 : list A),
        length l1 = n -> length l2 = n -> @l2v n l1 == @l2v n l2 -> l1 = l2.
    Proof.
      intros. unfold l2v in *.
      apply (l2f_inj Azero n); auto; intros.
      apply f2v_inj with (i:=i) in H1; auto.
    Qed.

    
    Definition v2l {n} (M : mat r c) : list A := f2l n (v2f v).
    
    (** length (v2l a) = n *)
    Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
    Proof. intros. unfold v2l. apply f2l_length. Qed.

    (** nth i (v2l a) = a.i *)
    Lemma nth_v2l : forall {n} (v : vec n) (i j : nat), i < r -> nth i (v2l v) Azero = v.[i].
    Proof. intros. unfold v2l. rewrite nth_f2l; auto. Qed.

    (** v2l v1 = v2l v2 -> v1 = v2 *)
    Lemma v2l_inj : forall {n} (v1 v2 : vec n), v2l v1 = v2l v2 -> v1 == v2.
    Proof. intros. unfold v2l in *. veq. apply f2l_inj with (i:=i) in H; auto. Qed.

    
    (** l2v (v2l v) = v *)
    Lemma l2v_v2l : forall {n} (v : vec n), (@l2v n (v2l v)) == v.
    Proof. intros. unfold l2v,v2l. veq. idx. apply l2f_f2l; auto. Qed.

    (** v2l (l2v l) = l *)
    Lemma v2l_l2v : forall {n} (l : list A), length l = n -> v2l (@l2v n l) = l.
    Proof.
      intros. unfold l2v,v2l.
      apply (list_eq_ext Azero n); auto; intros.
      - rewrite nth_f2l; auto. rewrite v2f_f2v; auto.
      - apply f2l_length.
    Qed.
    
    (** ∀ l, (∃ v, v2l v = l) *)
    Lemma v2l_surj : forall {n} (l : list A), length l = n -> (exists v : vec n, v2l v = l).
    Proof. intros. exists (l2v l). apply v2l_l2v; auto. Qed.
    
    (** ∀ v, (∃ l, l2v l = a) *)
    Lemma l2v_surj : forall {n} (v : vec n), (exists l, @l2v n l == v).
    Proof. intros. exists (v2l v). apply l2v_v2l; auto. Qed.

  End l2v_v2l.


  (* ======================================================================= *)
  (** ** matrix with specific size *)
  Section vec_specific.
    Context {A} {Azero : A}.
    Variable a1 a2 a3 a4 : A.
    
    Definition mkvec0 : @vec A 0 := l2v Azero [].
    Definition mkvec1 : @vec A 1 := l2v Azero [a1].
    Definition mkvec2 : @vec A 2 := l2v Azero [a1;a2].
    Definition mkvec3 : @vec A 3 := l2v Azero [a1;a2;a3].
    Definition mkvec4 : @vec A 4 := l2v Azero [a1;a2;a3;a4].
  End vec_specific.

  (* Lemma meq_equiv : forall {A r c}, Equivalence (@veq (@vec A c) r). *)
  (* Admitted. *)
  (* Existing Instance meq_equiv. *)
  (* x, y : @vec (@vec A r) c *)
  (* H : @veq (@vec A r) c x y *)
  (* y0 : nat *)
  (* x1, y1 : @vec A r *)
  (* H1 : @veq A r x1 y1 *)
  (* ============================ *)
  (* @veq (@vec A r) c (@vset (@vec A r) c x y0 x1) (@vset (@vec A r) c y y0 y1) *)


  (* (M1 === M2) -> v1 == v2 -> i = j -> i < r -> j < r -> M1.[i<-v1] === M2.[i<-v2] *)
  Lemma msetr_meq : forall {A r c} (M1 M2 : @mat A r c) (v1 v2 : @vec A c) i j,
      M1 === M2 -> v1 == v2 -> i = j -> i < r -> j < r -> M1.[i<-v1] === M2.[j<-v2].
  Proof.
    intros. apply meq_if; intros. destruct (i ??= i0).
    - subst. apply meq_imply with (i:=i0) in H; auto. idx.
    - idx. apply meq_imply with (i:=i0); auto.
  Qed.
  
  (* Lemma msetr_meq_mor : forall {A r c}, *)
  (*     Proper (meq ==> eq ==> veq ==> meq) ((fun M => @vset (@vec A c) r M)). *)
  (* Proof. *)
  (* Lemma msetr_meq_mor : forall {A r c}, *)
  (*     Proper (meq ==> eq ==> veq ==> meq) (@vset (@vec A c) r). *)
  (* Proof. *)
  (*   repeat intro. *)
  (*   apply msetr_meq; auto. *)
  (* Existing Instance mset_mat_mor. *)

  (** 检查PArray对证明的支持 *)
  Section proof_test.
    Variable A : Type.
    Variable a b c : A.

    (* 一个给定维度的具体向量，可通过计算直接得证 *)
    (* [a;a] = ([a,a] <- 0,b <- 0,a) *)
    Goal (mcreate 2 a) == vset (vset (mcreate 2 a) 0 b) 0 a.
    Proof. idx. Qed.

    (* 对长度为2的向量进行越界读写，此时并不会进行类型检查。
       并且由于是在函子中使用了抽象的模型，此时不进行具体运算，也加快了速度。
       当使用OCaml中的 array 模型时，越界时会触发异常。
       此外，Coq中验证过的函数不会出现越界访问。 *)
    Compute vget (mcreate 2 a) 5.
    Compute vset (mcreate 2 a) 5 b.
    
    (* 以下命题无法得证。左侧表示，越界写入数据 *)
    Goal vset (mcreate 2 a) 5 b == mcreate 2 a.
    Proof. idx. apply veq_if; intros. Abort.

    (* 任意维度时，就不能通过计算来证明了，需要使用性质来验证 *)
    Goal forall n i, i < r -> mcreate n a == (mcreate n a).[i<-a].
    Proof. idx. Qed.

    (* Variable M : @mat nat 3 4. *)
    (* Goal M.[0,1<-3].[0,2<-2] === M.[0,2<-2].[0,1<-3]. *)
    (* Proof. *)
    (*   idx. *)
    (*   apply meq_if; intros. idx. *)
    (*   ?? *)
    (*     unfold meq. *)
    (*   Check mset. *)
    (*   match goal with *)
    (*   | [ |- context [?M.[?i1,?j1<-?a1].[?i2,?j2<-?a2]]] => *)
    (*       replace i1 with j2 *)
    (*   end. *)
      
    (*   unfold mset. idx. *)
    (*   apply meq_if; intros. *)
      
    (*   idx. *)
    (*   apply mset_mat_mor; idx. *)
    (*   idx_perm. *)
    (* Qed. *)
    (* ?     *)
  End proof_test.
  

  (* ======================================================================= *)
  (** ** 自然基的基向量 *)
  Section veye.
    Context {A} (Azero Aone : A).
    Notation "0" := Azero : A_scope.
    Notation "1" := Aone : A_scope.
    Notation vzero := (vzero 0).
    Context {one_neq_zero : 1 <> 0}.

    Definition veye {n} (i j : nat) : @vec A n :=
      f2v (fun j => if i ??= j then 1 else 0).
    
    (** (veye i).i = 1 *)
    Lemma nth_veye_eq : forall {n} i, i < r -> (@veye n i).[i] = 1.
    Proof. intros. unfold veye. idx. Qed.

    (** (veye i).j = 0 *)
    Lemma nth_veye_neq : forall {n} i j, i <> j -> j < n -> (@veye n i).[j] = 0.
    Proof. intros. unfold veye. idx. Qed.

    (** veye <> 0 *)
    Lemma veye_neq0 : forall {n} i, i < r -> @veye n i <> vzero.
    Proof.
      intros. intro. rewrite veq_iff in H0. specialize (H0 i H).
      rewrite nth_veye_eq, nth_vzero in H0; auto.
    Qed.
    
  End veye.


  (* ======================================================================= *)
  (** ** natural basis, 自然基（最常见的一种标准正交基) *)
  Section veyes.
    Context {A} (Azero Aone : A).
    Notation "0" := Azero : A_scope.
    Notation "1" := Aone : A_scope.
    Notation vzero := (vzero 0).
    Context {one_neq_zero : 1 <> 0}.

    Definition veyes (n : nat) : @vec (@vec A n) n := f2v (fun i => veye 0 1 i).

    (** veyes.ii = 1 *)
    Lemma nth_veyes_eq : forall {n} i, i < r -> (veyes n).[i].[i] = 1.
    Proof. intros. unfold veyes. idx. apply nth_veye_eq; auto. Qed.

    (** veyes.ij = 0 *)
    Lemma nth_veyes_neq : forall {n} i j, i <> j -> i < r -> j < n -> (veyes n).[i].[j] = 0.
    Proof. intros. unfold veyes. idx. apply nth_veye_neq; auto. Qed.
    
  End veyes.



  (* ======================================================================= *)
  (** ** Mapping of a matrix *)
  Section vmap.
    Context {V1 V2 : Type} (f : A -> B).
    
    Definition vmap {n} (M : mat r c) : @vec B n := f2v (fun i => f (v.[i])).

    (** (vmap f a).i = f (a.i) *)
    Lemma nth_vmap : forall {n} (v : vec n) i, i < r -> (vmap v).[i] = f (v.[i]).
    Proof. intros. unfold vmap. idx. Qed.

  End vmap.


  (* ======================================================================= *)
  (** ** Mapping of two matrixs *)
  Section vmap2.
    Context {V1 V2 C : Type} (f : A -> B -> C).
    
    Definition vmap2 {n} (v1 : @vec A n) (v2 : @vec B n) : @vec C n :=
      f2v (fun i => f v1.[i] v2.[i]).

    (** (vmap2 f v1 v2).i = f (v1.i) (v2.i) *)
    Lemma nth_vmap2 : forall {n} (v1 v2 : vec n) i,
        i < r -> (vmap2 v1 v2).[i] = f v1.[i] v2.[i].
    Proof. intros. unfold vmap2; auto. idx. Qed.

    (* vmap2 f v1 v2 = vmap id (fun i => f u.i v.i) *)
    Lemma vmap2_eq_vmap : forall {n} (v1 v2 : vec n),
        vmap2 v1 v2 = vmap (fun a => a) (f2v (fun i => f v1.[i] v2.[i])).
    Proof. intros. apply veq_iff; intros. rewrite nth_vmap2, nth_vmap; idx. Qed.
    
  End vmap2.


  (** vmap2 on same type *)
  Section vmap2_sametype.
    Context `{ASGroup}.

    (** vmap2 f v1 v2 = vmap2 f b a *)
    Lemma vmap2_comm : forall {n} (v1 v2 : vec n),
        vmap2 Aadd v1 v2 = vmap2 Aadd v2 v1.
    Proof.
      intros. apply veq_iff; intros. rewrite !nth_vmap2; idx. asemigroup.
    Qed.
    
    (** vmap2 f (vmap2 f v1 v2) v3 = vmap2 f v1 (vmap2 f v2 v3) *)
    Lemma vmap2_assoc : forall {n} (v1 v2 v3 : vec n),
        vmap2 Aadd (vmap2 Aadd v1 v2) v3 = vmap2 Aadd v1 (vmap2 Aadd v2 v3).
    Proof.
      intros. apply veq_iff; intros. rewrite !nth_vmap2; idx. asemigroup.
    Qed.
  End vmap2_sametype.


  (* ======================================================================= *)
  (** ** Set element of a matrix *)
  Section vset.
    Context {A} {Azero : A}.

    (* Lemma mset_eq : forall {n} (M : mat r c) (i j : nat) (x : A), *)
    (*     i < r -> vset v i x = f2v (fun j => if j ??= i then x else v.[j]). *)
    (* Proof. intros. apply veq_iff; intros. unfold vset. idx. Qed. *)

    (* (** (vset a i x).i = x *) *)
    (* Lemma nth_mset_eq : forall {n} (M : mat r c) (i j : nat) (x : A), *)
    (*     i < r -> (vset v i x).[i] = x. *)
    (* Proof. intros. unfold vset. idx. Qed. *)
    
    (** (vset a i x).j = a.[j *)
    Lemma nth_mset_neq : forall {n} (M : mat r c) (i j : nat) (x : A),
        i <> j -> i < r -> j < n -> (vset v i x).[j] = v.[j].
    Proof. intros. unfold vset. idx. Qed.
    
  End vset.


  (* ======================================================================= *)
  (** ** Swap two element of a matrix *)
  Section vswap.
    Context {A : Type}.
    
    (* Swap the i-th and j-th element of matrix `a` *)
    Definition vswap {n} (M : mat r c) (i j : nat) : @vec A n :=
      a <- i, (a$j) <- j, (a$i).

    Lemma vswap_eq : forall {n} (M : mat r c) (i j : nat),
        i < r -> j < n ->
        vswap a i j = 
          f2v (fun k => if k ??= i then a$j
                      else (if k ??= j then a$i else a$k)).
    Proof. intros. apply veq_iff; intros. unfold vswap. idx. idx_perm. Qed.

    Lemma nth_vswap_i : forall {n} (M : mat r c) (i j : nat),
        i < r -> j < n -> (vswap a i j).[i] = a.[j].
    Proof. intros. unfold vswap. idx. idx_perm. Qed.

    Lemma nth_vswap_j : forall {n} (M : mat r c) (i j : nat),
        j < n -> (vswap a i j).[j] = a.[i].
    Proof. intros. unfold vswap. idx. Qed.

    Lemma nth_vswap_other : forall {n} (M : mat r c) (i j k : nat),
        i <> k -> j <> k -> i < r -> j < n -> k < n -> (vswap a i j).[k] = a.[k].
    Proof. intros. unfold vswap. idx. Qed.

    Lemma vswap_vswap : forall {n} (M : mat r c) (i j : nat),
        i < r -> j < n -> vswap (vswap a i j) j i = a.
    Proof.
      intros. apply veq_iff; intros. unfold vswap.
      destruct (i ??= i0), (j ??= i0); idx.
    Qed.

  End vswap.


  (* ======================================================================= *)
  (** ** Insert element to a matrix *)
  Section vinsert.
    Context {A} {Azero : A}.
    (* Notation vzero := (vzero Azero). *)

    Definition vinsert {n} (M : mat r c) (i j : nat) (x : A) : @vec A (S n) :=
      f2v (fun j => if j ??< i then a.[j] else
                    if j ??= i then x
                    else (a.[(pred j)])).

    (** j < i -> (vinsert a i x).j = a.i *)
    Lemma nth_vinsert_lt : forall {n} (M : mat r c) (i j : nat) (x : A) (j : nat),
        j < i -> i < r -> j < n -> (vinsert a i x).[j] = a.[j].
    Proof. intros. unfold vinsert. idx. Qed.

    (** (vinsert a i x).i = x *)
    Lemma nth_vinsert_eq : forall {n} (M : mat r c) (i j : nat) (x : A),
        i <= n -> (vinsert a i x).[i] = x.
    Proof. intros. unfold vinsert. idx. Qed.
    
    (** i < j -> (vinsert a i x).j = a.(S i) *)
    Lemma nth_vinsert_gt : forall {n} (M : mat r c) (i j : nat) (x : A) (j : nat),
        i < j -> j <= n -> (vinsert a i x).[j]= a.[(pred j)].
    Proof. intros. unfold vinsert. idx. Qed.

    (** (vzero <<- Azero) = vzero *)
    Lemma vinsert_vzero_0 : forall {n} i,
        i < r -> @vinsert n (vzero Azero) i Azero = (vzero Azero).
    Proof.
      intros. apply veq_iff; intros. rewrite nth_vzero; auto.
      destruct (i0 ??< i).
      - rewrite nth_vinsert_lt; idx.
      - destruct (i0 ??= i).
        + subst. rewrite nth_vinsert_eq; idx.
        + rewrite nth_vinsert_gt; idx.
    Qed.

  (*
  (** (a <<- x) = vzero -> x = Azero *)
  Lemma vinsert_eq0_imply_x0 {AeqDec : Dec (@eq A)} : forall {n} (M : mat r c) i x,
      vinsert a i x = vzero -> x = Azero.
  Proof.
    intros. rewrite veq_iff in *. specialize (H i).
    rewrite nth_vzero in H. rewrite <- H.
    symmetry. apply nth_vinsert_eq.
  Qed.

  (** (a <<- x) = vzero -> a = vzero *)
  Lemma vinsert_eq0_imply_v0 {AeqDec : Dec (@eq A)} : forall {n} (M : mat r c) i x,
      vinsert a i x = vzero -> a = vzero.
  Proof.
    intros.
    pose proof (vinsert_eq0_imply_x0 a i x H). subst.
    rewrite !veq_iff in *. intros j.
    destruct (j ??< i).
    - specialize (H (fin2SuccRange j)).
      rewrite nth_vinsert_lt with (j:=j) in H; auto.
    - destruct (j ??> i).
      + specialize (H (fin2SuccRangeSucc j)).
        rewrite nth_vinsert_gt with (j:=j) in H; auto. lia. idx.
      + assert (fin2nat i = fin2nat j). lia. rewrite nth_vzero.
        rewrite vinsert_eq_vinsert' in H.
        unfold vinsert',f2v,f2ff,v2f,ff2f in H.
        specialize (H (fin2SuccRangeSucc j)).
        destruct i as [i Hi], j as [j Hj]; simpl in *.
        rewrite nth_vzero in H. subst. idx. rewrite <- H. f_equal. idx.
  Qed.

  (** (a <<- x) = vzero <-> a = vzero /\ x = Azero  *)
  Lemma vinsert_eq0_iff {AeqDec : Dec (@eq A)} : forall {n} (M : mat r c) i x,
      vinsert a i x = vzero <-> (a = vzero /\ x = Azero).
  Proof.
    intros. destruct (Aeqdec a vzero) as [Ha|Ha], (Aeqdec x Azero) as [Hx|Hx]; auto.
    - subst. split; intros; auto. apply vinsert_vzero_0.
    - subst. split; intros.
      + exfalso. rewrite veq_iff in H. specialize (H i).
        rewrite nth_vinsert_eq in H. cbv in H. easy.
      + destruct H. easy.
    - subst. split; intro.
      + split; auto. apply vinsert_eq0_imply_v0 in H; auto.
      + destruct H. subst. easy.
    - split; intros.
      + split. apply vinsert_eq0_imply_v0 in H; auto.
        apply vinsert_eq0_imply_x0 in H; auto.
      + destruct H; subst. apply vinsert_vzero_0.
  Qed.

  (** (a <<- x) <> vzero <-> a <> vzero \/ x <> Azero  *)
  Lemma vinsert_neq0_iff {AeqDec : Dec (@eq A)} : forall {n} (M : mat r c) i x,
      vinsert a i x <> vzero <-> (a <> vzero \/ x <> Azero).
  Proof. intros. rewrite vinsert_eq0_iff. tauto. Qed.
   *)
  End vinsert.

  Section test.
    Let n := 5.
    Let a : vec n := l2v 9 [1;2;3;4;5].
    (* Compute v2l (vinsert a (nat2finS 1) 7). *)
    (* Compute v2l (vinsert a (nat2finS 5) 7). *)
  End test.    


  (* ======================================================================= *)
  (** ** Matrix addition *)
  Section vadd.
    Context `{AMonoid}.
    Infix "+" := Aadd : A_scope.
    
    Notation vec := (@vec A).
    Notation vzero := (vzero Azero).

    Definition vadd {n} (v1 v2 : vec n) : vec n := vmap2 Aadd v1 v2.
    Infix "+" := vadd : vec_scope.

  End vadd.

  Compute @vrepeat _ 3 0. 0. 3 0.
  Require Import Reals.
  Definition vaddR := (@vadd _ Rplus).
  Definition vsumR := (@vsum _ Rplus R0).
  Extraction "PMatrix.ml" vaddR vsumR vrepeat.? vget vset mcreate vmake.


(** ** Matrix opposition *)
Section vopp.
  
  (* Let's have an Abelian-Group *)
  Context `{AGroup A Aadd Azero}.
  Notation "- a" := (Aopp a) : A_scope.
  
  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.

  Definition vopp {n} (v : vec n) : vec n := vmap Aopp a.
  Notation "- a" := (vopp a) : vec_scope.

  (** (- a).i = - (a.i) *)
  Lemma nth_vopp : forall {n} (v : vec n) i, (- a).[i] = (- (a.[i]))%A.
  Proof. intros. cbv. auto. Qed.

  (** - a + a = 0 *)
  Lemma vadd_vopp_l : forall {n} (v : vec n), (- a) + a = vzero.
  Proof. intros. apply veq_iff; intros. cbv. group. Qed.
  
  (** a + - a = 0 *)
  Lemma vadd_vopp_r : forall {n} (v : vec n), a + (- a) = vzero.
  Proof. intros. apply veq_iff; intros. cbv. group. Qed.

  (** <vadd,vzero,vopp> is an abelian group *)
  #[export] Instance vadd_AGroup : forall n, @AGroup (vec n) vadd vzero vopp.
  Proof.
    intros. repeat constructor; intros;
      try apply vadd_AMonoid;
      try apply vadd_vopp_l;
      try apply vadd_vopp_r.
  Qed.

  (* Now, we ca use group theory on this instance *)

  (** - (- a) = a *)
  Lemma vopp_vopp : forall {n} (v : vec n), - (- a) = a.
  Proof. intros. apply group_opp_opp. Qed.

  (** a = - b <-> - v1 == v2 *)
  Lemma vopp_exchange : forall {n} (v1 v2 : vec n), a = - b <-> - v1 == v2.
  Proof. intros. split; intros; subst; rewrite vopp_vopp; auto. Qed.

  (** - (vzero) = vzero *)
  Lemma vopp_vzero : forall {n:nat}, - (@Matrix.vzero _ Azero n) = vzero.
  Proof. intros. apply group_opp_0. Qed.

  (** - a = vzero <-> a = vzero *)
  Lemma vopp_eq0_iff : forall {n} (v : vec n), - a = vzero <-> a = vzero.
  Proof.
    intros. split; intros; rewrite veq_iff in *; intros;
      specialize (H0 i); rewrite nth_vzero, nth_vopp in *.
    - apply group_opp_eq0_iff; auto.
    - apply group_opp_eq0_iff; auto.
  Qed.
  
  (** - (a + b) = (- a) + (- b) *)
  Lemma vopp_vadd : forall {n} (v1 v2 : vec n), - (a + b) = (- a) + (- b).
  Proof. intros. rewrite group_opp_distr. apply commutative. Qed.

End vopp.


(** ** Matrix subtraction *)
Section vsub.

  (* Let's have an Abelian-Group *)
  Context `{AGroup A Aadd Azero}.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub v1 v2 := (a + (- b))%A.
  Infix "-" := Asub : A_scope.
  
  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  
  Definition vsub {n} (v1 v2 : vec n) : vec n := a + (- b).
  Infix "-" := vsub : vec_scope.

  (** (a - b).i = a.i - b.i *)
  Lemma nth_vsub : forall {n} (v1 v2 : vec n) i, (a - b).[i]= (a.[i]- b.[i])%A.
  Proof. intros. cbv. auto. Qed.

  (** a - b = - (b - a) *)
  Lemma vsub_comm : forall {n} (v1 v2 : vec n), a - b = - (b - a).
  Proof.
    intros. unfold vsub. rewrite group_opp_distr. rewrite group_opp_opp. auto.
  Qed.

  (** (a - b) - c = a - (b + c) *)
  Lemma vsub_assoc : forall {n} (v1 v2 c : vec n), (a - b) - c = a - (b + c).
  Proof.
    intros. unfold vsub. rewrite associative.
    f_equal. rewrite group_opp_distr. apply commutative.
  Qed.

  (** (a + b) - c = a + (b - c) *)
  Lemma vsub_assoc1 : forall {n} (v1 v2 c : vec n), (a + b) - c = a + (b - c).
  Proof. intros. unfold vsub. group. Qed.

  (** (a - b) - c = (a - c) - b *)
  Lemma vsub_assoc2 : forall {n} (v1 v2 c : vec n), (a - b) - c = (a - c) - b.
  Proof. intros. unfold vsub. group. f_equal. apply commutative. Qed.
  
  (** 0 - a = - a *)
  Lemma vsub_0_l : forall {n} (v : vec n), vzero - a = - a.
  Proof. intros. unfold vsub. group. Qed.
  
  (** a - 0 = a *)
  Lemma vsub_0_r : forall {n} (v : vec n), a - vzero = a.
  Proof. intros. unfold vsub. rewrite vopp_vzero. group. Qed.
  
  (** a - a = 0 *)
  Lemma vsub_self : forall {n} (v : vec n), a - a = vzero.
  Proof. intros. unfold vsub. group. Qed.

  (** a - b = 0 <-> v1 == v2 *)
  Lemma vsub_eq0_iff_eq : forall {n} (v1 v2 : vec n), a - b = vzero <-> v1 == v2.
  Proof. intros. apply group_sub_eq0_iff_eq. Qed.

End vsub.


(** ** Matrix scalar multiplication *)
Section vcmul.
  
  (* Let's have an Abelian-ring *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub v1 v2 := (a + (- b))%A.
  Infix "-" := Asub : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Infix "-" := vsub : vec_scope.
  
  Definition vcmul {n : nat} (x : A) (v : vec n) : vec n := vmap (fun y => Amul x y) a.
  Infix "\.*" := vcmul : vec_scope.

  (** (x .* a).i = x * a.i *)
  Lemma nth_vcmul : forall {n} (v : vec n) x i, (x \.* a).[i]= x * (a.[i]).
  Proof. intros. cbv. auto. Qed.

  (** x .* (y .* a) = (x * y) .* a *)
  Lemma vcmul_assoc : forall {n} (v : vec n) x y,
      x \.* (y \.* a) = (x * y)%A \.* a.
  Proof. intros. apply veq_iff; intros. cbv. ring. Qed.

  (** x .* (y .* a) = y .* (x .* a) *)
  Lemma vcmul_perm : forall {n} (v : vec n) x y,
      x \.* (y \.* a) = y \.* (x \.* a).
  Proof. intros. rewrite !vcmul_assoc. f_equal. ring. Qed.
  
  (** (x + y) .* a = (x .* a) + (y .* a) *)
  Lemma vcmul_add : forall {n} x y (v : vec n),
      (x + y)%A \.* a = (x \.* a) + (y \.* a).
  Proof. intros. apply veq_iff; intros. cbv. ring. Qed.

  (** x .* (a + b) = (x .* a) + (x .* b) *)
  Lemma vcmul_vadd : forall {n} x (v1 v2 : vec n),
      x \.* (a + b) = (x \.* a) + (x \.* b).
  Proof. intros. apply veq_iff; intros. cbv. ring. Qed.

  (** 0 .* a = vzero *)
  Lemma vcmul_0_l : forall {n} (v : vec n), Azero \.* a = vzero.
  Proof. intros. apply veq_iff; intros. cbv. ring. Qed.

  (** a .* vzero = vzero *)
  Lemma vcmul_0_r : forall {n} a, a \.* vzero = (@Matrix.vzero _ Azero n).
  Proof. intros. apply veq_iff; intros. cbv. ring. Qed.
  
  (** 1 .* a = a *)
  Lemma vcmul_1_l : forall {n} (v : vec n), Aone \.* a = a.
  Proof. intros. apply veq_iff; intros. cbv. ring. Qed.
  
  (** - 1 .* a = - a *)
  Lemma vcmul_neg1_l : forall {n} (v : vec n), (- Aone)%A \.* a = - a.
  Proof. intros. apply veq_iff; intros. cbv. ring. Qed.
  
  (** (- x) .* a = - (x .* a) *)
  Lemma vcmul_opp : forall {n} x (v : vec n), (- x)%A \.* a = - (x \.* a).
  Proof. intros. apply veq_iff; intros. cbv. ring. Qed.

  (* Tips: this proof shows a proof by computation, due to the Fin-Function 
     model. *)
  (** x .* (- a) = - (x .* a) *)
  Lemma vcmul_vopp : forall {n} x (v : vec n), x \.* (- a) = - (x \.* a).
  Proof. intros. apply veq_iff; intros. cbv. ring. Qed.

  (* Tips: this proof shows a proof by derivation *)
  (** (- x) .* (- a) = x .* a *)
  Lemma vcmul_opp_vopp : forall {n} x (v : vec n), (- x)%A \.* (- a) = x \.* a.
  Proof. intros. rewrite vcmul_vopp, vcmul_opp. rewrite vopp_vopp. auto. Qed.

  (** x .* (a - b) = (x .* a) - (x .* b) *)
  Lemma vcmul_vsub : forall {n} x (v1 v2 : vec n), x \.* (a - b) = (x \.* a) - (x \.* b).
  Proof. intros. unfold vsub. rewrite vcmul_vadd. rewrite vcmul_vopp. auto. Qed.

  (** <vadd,vzero,vopp> is an abelian group *)
  #[export] Instance vec_AGroup : forall n, @AGroup (vec n) vadd vzero vopp.
  Proof.
    intros. repeat constructor; intros;
      try apply vadd_AMonoid;
      try apply vadd_vopp_l;
      try apply vadd_vopp_r.
  Qed.
  
  (* If equip a `Dec` *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq A)}.

    (** a <> 0 -> b <> 0 -> x .* v1 == v2 -> x <> 0 *)
    Lemma vcmul_eq_imply_x_neq0 : forall {n} x (v1 v2 : vec n),
        a <> vzero -> b <> vzero -> x \.* v1 == v2 -> x <> Azero.
    Proof.
      intros. destruct (Aeqdec x Azero); auto. exfalso. subst.
      rewrite vcmul_0_l in H0. easy.
    Qed.
  End AeqDec.

  (* If equip a `Dec` and a `Field` *)
  Section Dec_Field.
    Context {AeqDec : Dec (@eq A)}.
    Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
    
    (** x .* a = 0 -> (x = 0) \/ (a = 0) *)
    Lemma vcmul_eq0_imply_x0_or_v0 : forall {n} x (v : vec n),
        x \.* a = vzero -> (x = Azero) \/ (a = vzero).
    Proof.
      intros. destruct (Aeqdec x Azero); auto. right.
      apply veq_iff; intros. rewrite veq_iff in H. specialize (H i).
      cbv in H. cbv. apply field_mul_eq0_iff in H; auto. tauto.
    Qed.

    (** x .* a = 0 -> a <> 0 -> x = 0 *)
    Corollary vcmul_eq0_imply_x0 : forall {n} x (v : vec n),
        x \.* a = vzero -> a <> vzero -> x = Azero.
    Proof. intros. apply (vcmul_eq0_imply_x0_or_v0 x a) in H; tauto. Qed.

    (** x .* a = 0 -> x <> 0 -> a = 0 *)
    Corollary vcmul_eq0_imply_v0 : forall {n} x (v : vec n),
        x \.* a = vzero -> x <> Azero -> a = vzero.
    Proof. intros. apply (vcmul_eq0_imply_x0_or_v0 x a) in H; tauto. Qed.

    (** x <> 0 -> a <> 0 -> x \.* a <> 0 *)
    Corollary vcmul_neq0_neq0_neq0 : forall {n} x (v : vec n),
        x <> Azero -> a <> vzero -> x \.* a <> vzero.
    Proof. intros. intro. apply vcmul_eq0_imply_x0_or_v0 in H1; tauto. Qed.
    
    (** x .* a = a -> x = 1 \/ a = 0 *)
    Lemma vcmul_same_imply_x1_or_v0 : forall {n} x (v : vec n),
        x \.* a = a -> (x = Aone) \/ (a = vzero).
    Proof.
      intros. destruct (Aeqdec x Aone); auto. right.
      apply veq_iff; intros. rewrite veq_iff in H. specialize (H i).
      cbv in H. cbv. apply field_mul_eq_imply_a1_or_b0 in H; auto. tauto.
    Qed.
    
    (** x = 1 \/ a = 0 -> x .* a = a *)
    Lemma vcmul_same_if_x1_or_v0 : forall {n} x (v : vec n),
        (x = Aone \/ a = vzero) -> x \.* a = a.
    Proof.
      intros. destruct H; subst. apply vcmul_1_l; auto. apply vcmul_0_r; auto.
    Qed.
    
    (** x .* a = a -> a <> 0 -> x = 1 *)
    Corollary vcmul_same_imply_x1 : forall {n} x (v : vec n),
        x \.* a = a -> a <> vzero -> x = Aone.
    Proof. intros. apply (vcmul_same_imply_x1_or_v0 x a) in H; tauto. Qed.
    
    (** x .* a = a -> x <> 1 -> a = 0 *)
    Corollary vcmul_same_imply_v0 : forall {n} x (v : vec n),
        x \.* a = a -> x <> Aone -> a = vzero.
    Proof. intros. apply (vcmul_same_imply_x1_or_v0 x a) in H; tauto. Qed.

    (** x .* a = y .* a -> (x = y \/ a = 0) *)
    Lemma vcmul_sameV_imply_eqX_or_v0 : forall {n} x y (v : vec n), 
        x \.* a = y \.* a -> (x = y \/ a = vzero).
    Proof.
      intros. destruct (Aeqdec x y); auto. right. rewrite veq_iff in H.
      rewrite veq_iff. intros. specialize (H i). rewrite !nth_vcmul in H.
      destruct (Aeqdec (a i) Azero); auto. apply field_mul_cancel_r in H; tauto.
    Qed.

    (** x .* a = y * a -> a <> 0 -> x = y *)
    Corollary vcmul_sameV_imply_eqX : forall {n} x y (v : vec n), 
        x \.* a = y \.* a -> a <> vzero -> x = y.
    Proof. intros. apply vcmul_sameV_imply_eqX_or_v0 in H; tauto. Qed.

    (** x .* a  = y .* a -> x <> y -> a = 0 *)
    Corollary vcmul_sameV_imply_v0 : forall {n} x y (v : vec n), 
        x \.* a = y \.* a -> x <> y -> a = vzero.
    Proof. intros. apply vcmul_sameV_imply_eqX_or_v0 in H; tauto. Qed.
  End Dec_Field.
  
End vcmul.


(** ** Dot product *)
Section vdot.
  
  (* Let's have an Abelian-ring *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub v1 v2 := (a + (- b))%A.
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone.
  Notation "a ²" := (a * a) : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation seqsum := (@seqsum _ Aadd Azero).
  Notation vsum := (@vsum _ Aadd Azero).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Infix "-" := vsub : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  
  Definition vdot {n : nat} (v1 v2 : vec n) : A := vsum (vmap2 Amul v1 v2).
  Notation "< a , b >" := (vdot v1 v2) : vec_scope.

  (** <a, b> = <b, a> *)
  Lemma vdot_comm : forall {n} (v1 v2 : vec n), <a, b> = <b, a>.
  Proof. intros. apply vsum_eq; intros. rewrite vmap2_comm; auto. Qed.

  (** <vzero, a> = vzero *)
  Lemma vdot_0_l : forall {n} (v : vec n), <vzero, a> = Azero.
  Proof.
    intros. unfold vdot,vsum. apply fseqsum_eq0; intros.
    rewrite nth_vmap2, nth_vzero. ring.
  Qed.
  
  (** <a, vzero> = vzero *)
  Lemma vdot_0_r : forall {n} (v : vec n), <a, vzero> = Azero.
  Proof. intros. rewrite vdot_comm, vdot_0_l; auto. Qed.

  (** <a + b, c> = <a, c> + <b, c> *)
  Lemma vdot_vadd_l : forall {n} (v1 v2 c : vec n), <a + b, c> = (<a, c> + <b, c>)%A.
  Proof. intros. unfold vdot. apply vsum_add; intros. cbv. ring. Qed.

  (** <a, b + c> = <a, b> + <a, c> *)
  Lemma vdot_vadd_r : forall {n} (v1 v2 c : vec n), <a, b + c> = (<a, b> + <a, c>)%A.
  Proof.
    intros. rewrite vdot_comm. rewrite vdot_vadd_l. f_equal; apply vdot_comm.
  Qed.

  (** <- a, b> = - <a, b> *)
  Lemma vdot_vopp_l : forall {n} (v1 v2 : vec n), < - a, b> = (- <a, b>)%A.
  Proof. intros. unfold vdot. apply vsum_opp; intros. cbv. ring. Qed.

  (** <a, - b> = - <a, b> *)
  Lemma vdot_vopp_r : forall {n} (v1 v2 : vec n), <a, - b> = (- <a, b>)%A.
  Proof. intros. rewrite vdot_comm, vdot_vopp_l, vdot_comm. auto. Qed.

  (** <a - b, c> = <a, c> - <b, c> *)
  Lemma vdot_vsub_l : forall {n} (v1 v2 c : vec n), <a - b, c> = (<a, c> - <b, c>)%A.
  Proof. intros. unfold vsub. rewrite vdot_vadd_l. f_equal. apply vdot_vopp_l. Qed.

  (** <a, b - c> = <a, b> - <a, c> *)
  Lemma vdot_vsub_r : forall {n} (v1 v2 c : vec n), <a, b - c> = (<a, b> - <a, c>)%A.
  Proof. intros. unfold vsub. rewrite vdot_vadd_r. f_equal. apply vdot_vopp_r. Qed.

  (** <x .* a, b> = x .* <a, b> *)
  Lemma vdot_vcmul_l : forall {n} (v1 v2 : vec n) x, <x \.* a, b> = x * <a, b>.
  Proof. intros. unfold vdot. apply vsum_cmul; intros. cbv. ring. Qed.
  
  (** <a, x .* b> = x .* <a, b> *)
  Lemma vdot_vcmul_r : forall {n} (v1 v2 : vec n) x, <a, x \.* b> = x * <a, b>.
  Proof.
    intros. rewrite vdot_comm. rewrite vdot_vcmul_l. f_equal; apply vdot_comm.
  Qed.
  
  (** <a, veye i> = a i *)
  Lemma vdot_veye_r : forall {n} (v : vec n) i, <a, veye 0 1 i> = a i.
  Proof.
    intros. apply vsum_unique with (i:=i).
    - rewrite nth_vmap2. rewrite nth_veye_eq. rewrite identityRight; auto.
    - intros. rewrite nth_vmap2. rewrite nth_veye_neq; auto.
      rewrite ring_mul_0_r; auto.
  Qed.

  (** <veye i, a> = a i *)
  Lemma vdot_veye_l : forall {n} (v : vec n) i, <veye 0 1 i, a> = a i.
  Proof. intros. rewrite vdot_comm. apply vdot_veye_r. Qed.
  
  (* If (@eq A) is decidable *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq A)}.

    (** <a, b> <> 0 -> a <> 0 *)
    Lemma vdot_neq0_imply_neq0_l : forall {n} (v1 v2 : vec n), <a, b> <> 0 -> a <> vzero.
    Proof.
      intros. destruct (Aeqdec a vzero); auto. subst. rewrite vdot_0_l in H. easy.
    Qed.
    
    (** <a, b> <> 0 -> b <> 0 *)
    Lemma vdot_neq0_imply_neq0_r : forall {n} (v1 v2 : vec n), <a, b> <> 0 -> b <> vzero.
    Proof.
      intros. destruct (Aeqdec b vzero); auto. subst. rewrite vdot_0_r in H. easy.
    Qed.
    
    (** (∀ c, <a, c> = <b, c>) -> v1 == v2 *)
    Lemma vdot_cancel_r : forall {n} (v1 v2 : vec n),
        (forall c : vec n, <a, c> = <b, c>) -> v1 == v2.
    Proof.
      intros. destruct (Aeqdec v1 v2) as [H1|H1]; auto. exfalso.
      apply vneq_iff_exist_nth_neq in H1. destruct H1 as [i H1].
      specialize (H (veye 0 1 i)). rewrite !vdot_veye_r in H. easy.
    Qed.
    
    (** (∀ c, <c, a> = <c, b>) -> v1 == v2 *)
    Lemma vdot_cancel_l : forall {n} (v1 v2 : vec n),
        (forall c : vec n, <c, a> = <c, b>) -> v1 == v2.
    Proof.
      intros. apply vdot_cancel_r. intros. rewrite !(vdot_comm _ c). auto.
    Qed.
    
  End AeqDec.


  (* If equip an ordered-abelian-ring *)
  Section OrderedARing.
    Context `{HOrderedARing : OrderedARing A Aadd Azero Aopp Amul Aone}.
    Infix "<" := Alt.
    Infix "<=" := Ale.
    
    (** 0 <= <a, a> *)
    Lemma vdot_ge0 : forall {n} (v : vec n), 0 <= (<a, a>).
    Proof.
      intros. unfold vdot, vsum, fseqsum, vmap2, ff2f. apply seqsum_ge0; intros.
      idx. apply sqr_ge0.
    Qed.

    (** <a, b> ² <= <a, a> * <b, b> *)
    Lemma vdot_sqr_le : forall {n} (v1 v2 : vec n), (<a, b> ²) <= <a, a> * <b, b>.
    Proof.
      intros. unfold vdot,vsum,vmap2. destruct n.
      - cbv. apply le_refl.
      - (* Convert dependent "vec" to non-dependent "nat -> A", by "Abstraction" *)
        remember (fun i => a (nat2finS i)) as f.
        remember (fun i => b (nat2finS i)) as g.
        replace (fseqsum (fun i => (a i * b i)))
          with (seqsum (fun i => f i * g i) (S n)); auto.
        2:{ rewrite ?Heqf,?Heqg. rewrite !fseqsum_eq_seqsum_succ. auto. }
        replace (fseqsum (fun i => a i * a i))
          with (seqsum (fun i => f i * f i) (S n)).
        2:{ rewrite ?Heqf,?Heqg. rewrite !fseqsum_eq_seqsum_succ. auto. }
        replace (fseqsum (fun i => b i * b i))
          with (seqsum (fun i => g i * g i) (S n)).
        2:{ rewrite ?Heqf,?Heqg. rewrite !fseqsum_eq_seqsum_succ. auto. }
        apply seqsum_SqrMul_le_MulSqr.
    Qed.

    (** (v i)² <= <a, a> *)
    Lemma nth_sqr_le_vdot : forall {n} (v : vec n) (i j : nat), (a i) ² <= <a, a>.
    Proof.
      intros. unfold vdot.
      pose ((fun i => (a$i) * (a$i)) : vec n) as u.
      replace (a i)² with (u i). replace (vmap2 Amul a a) with u.
      apply vsum_ge_any.
      - intros. unfold u. apply sqr_ge0.
      - unfold u. auto.
      - unfold u. auto.
    Qed.
    
  End OrderedARing.

  
  (* If equip an ordered-field and `Dec` *)
  Section OrderedField_Dec.
    Context {AeqDec : Dec (@eq A)}.
    Context `{HOrderedField : OrderedField A Aadd Azero Aopp Amul Aone}.
    Notation "/ a" := (Ainv a).
    Notation Adiv x y := (x * / y).
    Infix "/" := Adiv.
    Infix "<" := Alt.
    Infix "<=" := Ale.
    
    (** a = 0 -> <a, a> = 0 *)
    Lemma vdot_same_eq0_if_vzero : forall {n} (v : vec n), a = vzero -> <a, a> = 0.
    Proof. intros. subst. rewrite vdot_0_l; auto. Qed.
    
    (** <a, a> = 0 -> a = 0 *)
    Lemma vdot_same_eq0_then_vzero : forall {n} (v : vec n), <a, a> = 0 -> a = vzero.
    Proof.
      intros. unfold vdot,vsum,fseqsum in H. apply veq_iff; intros.
      apply seqsum_eq0_imply_seq0 with (i:=fin2nat i) in H.
      - rewrite nth_ff2f with (E:=fin2nat_lt _) in H.
        rewrite nat2fin_fin2nat in H. rewrite nth_vmap2 in H.
        apply field_sqr_eq0_reg in H; auto.
      - intros. rewrite nth_ff2f with (E:=H0). rewrite nth_vmap2. apply sqr_ge0.
      - apply fin2nat_lt.
    Qed.
    
    (** a <> vzero -> <a, a> <> 0 *)
    Lemma vdot_same_neq0_if_vnonzero : forall {n} (v : vec n), a <> vzero -> <a, a> <> 0.
    Proof. intros. intro. apply vdot_same_eq0_then_vzero in H0; auto. Qed.
    
    (** <a, a> <> 0 -> a <> vzero *)
    Lemma vdot_same_neq0_then_vnonzero : forall {n} (v : vec n), <a, a> <> 0 -> a <> vzero.
    Proof. intros. intro. apply vdot_same_eq0_if_vzero in H0; auto. Qed.
    
    (** 0 < <a, a> *)
    Lemma vdot_gt0 : forall {n} (v : vec n), a <> vzero -> Azero < (<a, a>).
    Proof.
      intros. apply vdot_same_neq0_if_vnonzero in H. pose proof (vdot_ge0 a).
      apply lt_if_le_and_neq; auto.
    Qed.

    (** <a, b>² / (<a, a> * <b, b>) <= 1. *)
    Lemma vdot_sqr_le_form2 : forall {n} (v1 v2 : vec n),
        a <> vzero -> b <> vzero -> <a, b>² / (<a, a> * <b, b>) <= 1.
    Proof.
      intros.
      pose proof (vdot_gt0 a H). pose proof (vdot_gt0 b H0).
      pose proof (vdot_sqr_le v1 v2).
      destruct (Aeqdec (<a, b>) 0) as [H4|H4].
      - rewrite H4. ring_simplify. apply le_0_1.
      - apply le_imply_div_le_1 in H3; auto. apply sqr_gt0. auto.
    Qed.

  End OrderedField_Dec.

End vdot.

Section vdot_extra.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  
  (** <<a,D>, b> = <a, <D,b> *)
  (* For example:
     (a1,a2,a3) [D11,D12] [b1]  记作 a*D*b，
                [D21,D22] [b2]
                [D31,D32]
     (a*D)*b = <a,col(D,1)> b1 + <a,col(D,2)> b2
             = (a1D11+a2D21+a3D31)b1 + (a1D12+a2D22+a3D32)b2
     a*(D*b) = a1 <row(D,1),b> + a2 <row(D,2),b> + a3 <row(D,3),b>
             = a1(D11b1+D12b2)+a2(D21b1+D22b2)+a3(D31b1+D32b2) *)
  
  Theorem vdot_assoc :
    forall {r c} (v : @vec A c) (D : @vec (@vec A r) c) (b : @vec A r),
      vdot (fun j => vdot a (fun i => D i j)) b = vdot a (fun i => vdot (D i) b).
  Proof.
    intros. unfold vdot. unfold vmap2.
    pose proof (vsum_vsum_exchg c r (fun i j => Amul (Amul (a i) (D i j)) (b j))).
    match goal with
    | H: ?a1 = ?a2 |- ?b1 = ?b2 => replace b1 with a2; [replace b2 with a1|]; auto
    end.
    - f_equal. extensionality i. apply vsum_cmul; intros. ring.
    - f_equal. extensionality i. rewrite commutative. apply vsum_cmul; intros. ring.
  Qed.

End vdot_extra.

(* ======================================================================= *)
(** ** Euclidean norm (L2 norm), Length of matrix *)
Section vlen.
  (* Euclidean norm == Euclidean length (distance) = L2 norm == L2 distance *)
  
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Context `{HConvertToR
      : ConvertToR A Aadd Azero Aopp Amul Aone Ainv Alt Ale Altb Aleb a2r}.

  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Infix "*" := Amul : A_scope.
  (* Notation "a ²" := (a * a) : A_scope. *)
  Notation "1" := Aone : A_scope.
  Notation "| a |" := (@Aabs _ 0 Aopp Aleb a) : A_scope.
  
  Notation vzero := (@vzero _ Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Infix "-" := vsub : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  Notation "< a , b >" := (vdot v1 v2) : vec_scope.

  (** Length (magnitude) of a matrix, is derived by inner-product *)
  Definition vlen {n} (v : vec n) : R := R_sqrt.sqrt (a2r (<a, a>)).
  Notation "|| a ||" := (vlen a) : vec_scope.

  (** ||vzero|| = 0 *)
  Lemma vlen_vzero : forall {n:nat}, @vlen n vzero = 0%R.
  Proof. intros. unfold vlen. rewrite vdot_0_l. rewrite a2r_0 at 1. ra. Qed.
  
  Section OrderedARing.
    Context `{HOrderedARing
        : OrderedARing A Aadd Azero Aopp Amul Aone Alt Ale Altb Aleb}.
    Infix "<" := Alt : A_scope.
    Infix "<=" := Ale : A_scope.
    
    (** 0 <= ||a|| *)
    Lemma vlen_ge0 : forall {n} (v : vec n), (0 <= ||a||)%R.
    Proof. intros. unfold vlen. ra. Qed.
    
    (** ||a|| = ||b|| <-> <a, a> = <b, b> *)
    Lemma vlen_eq_iff_dot_eq : forall {n} (v1 v2 : vec n), ||a|| = ||b|| <-> <a, a> = <b, b>.
    Proof.
      intros. unfold vlen. split; intros H; try rewrite H; auto.
      apply sqrt_inj in H.
      rewrite a2r_eq_iff in H; auto.
      apply a2r_ge0_iff; apply vdot_ge0.
      apply a2r_ge0_iff; apply vdot_ge0.
    Qed.

    (** <a, a> = ||a||² *)
    Lemma vdot_same : forall {n} (v : vec n), a2r (<a, a>) = (||a||²)%R.
    Proof.
      intros. unfold vlen. rewrite Rsqr_sqrt; auto.
      apply a2r_ge0_iff. apply vdot_ge0.
    Qed.

    (** |a i| <= ||a|| *)
    Lemma nth_le_vlen : forall {n} (v : vec n) (i j : nat),
        a <> vzero -> (a2r (|a i|%A) <= ||a||)%R.
    Proof.
      intros. apply Rsqr_incr_0_var.
      - rewrite <- vdot_same. unfold Rsqr. rewrite <- a2r_mul. apply a2r_le_iff.
        replace (|a i| * |a i|) with (a i * a i). apply nth_sqr_le_vdot.
        rewrite <- Aabs_mul. rewrite Aabs_right; auto. apply sqr_ge0.
      - apply vlen_ge0.
    Qed.

    (** ||a|| = 1 <-> <a, a> = 1 *)
    Lemma vlen_eq1_iff_vdot1 : forall {n} (v : vec n), ||a|| = 1%R <-> <a, a> = 1.
    Proof.
      intros. unfold vlen. rewrite sqrt_eq1_iff. rewrite a2r_eq1_iff. easy.
    Qed.

    (** ||- a|| = ||a|| *)
    Lemma vlen_vopp : forall n (v : vec n), ||- a|| = ||a||.
    Proof.
      intros. unfold vlen. f_equal. f_equal. rewrite vdot_vopp_l,vdot_vopp_r. ring.
    Qed.

    (** ||x .* a|| = |x| * ||a|| *)
    Lemma vlen_vcmul : forall n x (v : vec n), ||x \.* a|| = ((a2r (|x|))%A * ||a||)%R.
    Proof.
      intros. unfold vlen.
      rewrite commutative.
      replace (a2r (|x|)%A) with (|(a2r x)|)%R.
      2:{ rewrite a2r_Aabs. auto. }
      rewrite <- sqrt_square_abs. rewrite <- sqrt_mult_alt.
      - f_equal. rewrite vdot_vcmul_l, vdot_vcmul_r, <- associative.
        rewrite a2r_mul. rewrite commutative. f_equal. rewrite a2r_mul. auto.
      - apply a2r_ge0_iff. apply vdot_ge0.
    Qed.

    (** ||a + b||² = ||a||² + ||a||² + 2 * <a, b> *)
    Lemma vlen_sqr_vadd : forall {n} (v1 v2 : vec n),
        ||(a + b)||² = (||a||² + ||b||² + 2 * a2r (<a, b>))%R.
    Proof.
      intros. rewrite <- !vdot_same. rewrite !vdot_vadd_l, !vdot_vadd_r.
      rewrite (vdot_comm b a). rewrite !a2r_add. ring.
    Qed.

    (** ||a - b||² = ||a||² + ||b||² - 2 * <a, b> *)
    Lemma vlen_sqr_vsub : forall {n} (v1 v2 : vec n),
        ||(a - b)||² = (||a||² + ||b||² - 2 * a2r (<a, b>))%R.
    Proof.
      intros. rewrite <- !vdot_same. unfold vsub.
      rewrite !vdot_vadd_l, !vdot_vadd_r.
      rewrite !vdot_vopp_l, !vdot_vopp_r. rewrite (vdot_comm b a).
      rewrite !a2r_add, !a2r_opp at 1. ring.
    Qed.

    (* 柯西.许西尔兹不等式，Cauchy-Schwarz Inequality *)
    (** |<a, b>| <= ||a|| * ||b|| *)
    Lemma vdot_abs_le : forall {n} (v1 v2 : vec n), (|a2r (<a, b>)| <= ||a|| * ||b||)%R.
    Proof.
      intros. pose proof (vdot_sqr_le v1 v2).
      apply a2r_le_iff in H. rewrite !a2r_mul in H.
      rewrite (vdot_same a) in H. rewrite (vdot_same b) in H.
      replace (||a||² * ||b||²)%R with ((||a|| * ||b||)²) in H; [| cbv;ring].
      apply Rsqr_le_abs_0 in H.
      replace (|(||a|| * ||b||)|)%R with (||a|| * ||b||)%R in H; auto.
      rewrite !Rabs_right; auto.
      pose proof (vlen_ge0 a). pose proof (vlen_ge0 b). ra.
    Qed.

    (** <a, b> <= ||a|| * ||b|| *)
    Lemma vdot_le_mul_vlen : forall {n} (v1 v2 : vec n), (a2r (<a, b>) <= ||a|| * ||b||)%R.
    Proof. intros. pose proof (vdot_abs_le v1 v2). apply Rabs_le_rev in H. ra. Qed.

    (** - ||a|| * ||b|| <= <a, b> *)
    Lemma vdot_ge_mul_vlen_neg : forall {n} (v1 v2 : vec n),
        (- (||a|| * ||b||) <= a2r (<a, b>))%R.
    Proof. intros. pose proof (vdot_abs_le v1 v2). apply Rabs_le_rev in H. ra. Qed.

    (* 任意维度“三角形”的任意一边的长度小于等于两边长度之和 *)
    (** ||a + b|| <= ||a|| + ||a|| *)
    Lemma vlen_le_add : forall {n} (v1 v2 : vec n), (||(a + b)%V|| <= ||a|| + ||b||)%R.
    Proof.
      intros. apply Rsqr_incr_0_var.
      2:{ unfold vlen; ra. }
      rewrite Rsqr_plus. rewrite <- !vdot_same.
      replace (a2r (<a + b, a + b>))
        with (a2r (<a, a>) + a2r (<b, b>) + (2 * a2r (<a, b>)))%R.
      2:{ rewrite vdot_vadd_l,!vdot_vadd_r.
          rewrite (vdot_comm b a). rewrite !a2r_add at 1. ra. }
      apply Rplus_le_compat_l.
      rewrite !associative. apply Rmult_le_compat_l; ra.
      pose proof (vdot_abs_le v1 v2). unfold Rabs in H.
      destruct Rcase_abs; ra.
    Qed.

    (* 任意维度“三角形”的任意一边的长度大于等于两边长度之差 *)
    (** ||a|| - ||b|| <= ||a + b|| *)
    Lemma vlen_ge_sub : forall {n} (v1 v2 : vec n), ((||a|| - ||b||) <= ||(a + b)%V||)%R.
    Proof.
      intros. apply Rsqr_incr_0_var.
      2:{ unfold vlen; ra. }
      rewrite Rsqr_minus. rewrite <- !vdot_same.
      replace (a2r (<a + b, a + b>))
        with (a2r (<a, a>) + a2r (<b, b>) + (2 * a2r (<a, b>)))%R.
      2:{ rewrite vdot_vadd_l,!vdot_vadd_r.
          rewrite (vdot_comm b a). rewrite !a2r_add at 1. ra. }
      apply Rplus_le_compat_l.
      pose proof (vdot_abs_le v1 v2). unfold Rabs in H.
      destruct Rcase_abs; ra.
    Qed.

  End OrderedARing.

  Section OrderedField_Dec.
    Context `{HOrderedField
        : OrderedField A Aadd Azero Aopp Amul Aone Ainv Alt Ale}.
    Context {AeqDec : Dec (@eq A)}.
    Infix "<=" := Ale : A_scope.
    
    (** ||a|| = 0 <-> v = 0 *)
    Lemma vlen_eq0_iff_eq0 : forall {n} (v : vec n), ||a|| = 0%R <-> a = vzero.
    Proof.
      intros. unfold vlen. split; intros.
      - apply vdot_same_eq0_then_vzero. apply sqrt_eq_0 in H; auto.
        apply a2r_eq0_iff; auto. apply a2r_ge0_iff; apply vdot_ge0.
      - rewrite H. rewrite vdot_0_l. rewrite a2r_0 at 1. ra.
    Qed.
    
    (** ||a|| <> 0 <-> a <> 0 *)
    Lemma vlen_neq0_iff_neq0 : forall {n} (v : vec n), ||a|| <> 0%R <-> a <> vzero.
    Proof. intros. rewrite vlen_eq0_iff_eq0. easy. Qed.

    (** a <> vzero -> 0 < ||a|| *)
    Lemma vlen_gt0 : forall {n} (v : vec n), a <> vzero -> (0 < ||a||)%R.
    Proof. intros. pose proof (vlen_ge0 a). apply vlen_neq0_iff_neq0 in H; ra. Qed.
    
    (** 0 <= <a, a> *)
    Lemma vdot_same_ge0 : forall {n} (v : vec n), (Azero <= <a, a>)%A.
    Proof.
      intros. destruct (Aeqdec a vzero) as [H|H].
      - subst. rewrite vdot_0_l. apply le_refl.
      - apply le_if_lt. apply vdot_gt0; auto.
    Qed.
    
  End OrderedField_Dec.
  
End vlen.

#[export] Hint Resolve vlen_ge0 : vec.


(* ======================================================================= *)
(** ** Unit matrix *)

Section vunit.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Notation "1" := Aone.
  Notation vzero := (vzero Azero).
  Notation vopp := (@vopp _ Aopp).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation "< a , b >" := (vdot v1 v2) : vec_scope.
  
  (** A unit matrix `a` is a matrix whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable with the proof of vunit_spec. *)
  Definition vunit {n} (v : vec n) : Prop := <a, a> = 1.
  
  (** vunit a <-> vunit (vopp a). *)
  Lemma vopp_vunit : forall {n} (v : vec n), vunit (vopp a) <-> vunit a.
  Proof.
    intros. unfold vunit. rewrite vdot_vopp_l, vdot_vopp_r.
    rewrite group_opp_opp. easy.
  Qed.

  Section Field.
    Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
    
    (** The unit matrix cannot be zero matrix *)
    Lemma vunit_neq0 : forall {n} (v : vec n), vunit a -> a <> vzero.
    Proof.
      intros. intro. rewrite H0 in H. unfold vunit in H.
      rewrite vdot_0_l in H. apply field_1_neq_0. easy.
    Qed.
    
  End Field.

  Section ConvertToR.
    Context `{HConvertToR : ConvertToR A Aadd Azero Aopp Amul Aone Ainv Alt Ale}.

    Notation vlen := (@vlen _ Aadd Azero Amul a2r).
    Notation "|| a ||" := (vlen a) : vec_scope.

    (** Verify the definition is reasonable *)
    Lemma vunit_spec : forall {n} (v : vec n), vunit a <-> ||a|| = 1%R.
    Proof. intros. split; intros; apply vlen_eq1_iff_vdot1; auto. Qed.

  End ConvertToR.

(** If column of a and column of b all are unit, 
    then column of (a * b) is also unit *)
  (*   a : mat 2 2 *)
  (* a1 : vunit (mat2col a 0) *)
  (* a2 : vunit (mat2col a 1) *)
  (* a3 : vorth (mat2col a 0) (mat2col a 1) *)
  (* b1 : vunit (mat2col b 0) *)
  (* b2 : vunit (mat2col b 1) *)
  (* b3 : vorth (mat2col b 0) (mat2col b 1) *)
  (* ============================ *)
  (* vunit (mat2col (a * b) 0) *)
End vunit.


(* ======================================================================= *)
(** ** Orthogonal matrixs 正交的两个向量 *)
Section vorth.
  (* Two matrixs, u and v, in an inner product space v, are orthogonal (also called 
     perpendicular) if their inner-product is zero. It can be denoted as `u ⟂ v` *)
  
  (* Let's have an Abelian-ring *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub v1 v2 := (a + (- b))%A.
  Infix "-" := Asub : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Infix "-" := vsub : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  Notation "< a , b >" := (vdot v1 v2) : vec_scope.
  
  Definition vorth {n} (v1 v2 : vec n) : Prop := <a, b> = Azero.
  Infix "_|_" := vorth : vec_scope.

  (** a _|_ b -> b _|_ a *)
  Lemma vorth_comm : forall {n} (v1 v2 : vec n), a _|_ b -> b _|_ a.
  Proof. intros. unfold vorth in *. rewrite vdot_comm; auto. Qed.


  (* If equip a `Dec` and a `Field` *)
  Section Dec_Field.
    Context {AeqDec : Dec (@eq A)}.
    Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
    
    (** (x .* a) _|_ b <-> a _|_ b *)
    Lemma vorth_vcmul_l : forall {n} x (v1 v2 : vec n),
        x <> Azero -> ((x \.* a) _|_ b <-> a _|_ b).
    Proof.
      intros. unfold vorth in *. rewrite vdot_vcmul_l. split; intros.
      - apply field_mul_eq0_iff in H0. destruct H0; auto. easy.
      - rewrite H0. ring.
    Qed.
    
    (** a _|_ (x .* b) <-> a _|_ b *)
    Lemma vorth_vcmul_r : forall {n} x (v1 v2 : vec n),
        x <> Azero -> (a _|_ (x \.* b) <-> a _|_ b).
    Proof.
      intros. split; intros.
      - apply vorth_comm in H0. apply vorth_comm. apply vorth_vcmul_l in H0; auto.
      - apply vorth_comm in H0. apply vorth_comm. apply vorth_vcmul_l; auto.
    Qed.
  End Dec_Field.
  
End vorth.



(** ** Projection component of a matrix onto another *)
Section vproj.
  
  (* Let's have an field *)
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv}.
  Add Field field_inst : (make_field_theory F).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub v1 v2 := (a + (- b))%A.
  Infix "-" := Asub : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv v1 v2 := (a * (/ b))%A.
  Infix "/" := Adiv : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation vunit := (@vunit _ Aadd Azero Amul Aone).
  Notation vorth := (@vorth _ Aadd Azero Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Infix "-" := vsub : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  Notation "< a , b >" := (vdot v1 v2) : vec_scope.
  Infix "_|_" := vorth : vec_scope.
  
  (** The projection component of `a` onto `b` *)
  Definition vproj {n} (v1 v2 : vec n) : vec n := (<a, b> / <b, b>) \.* b.

  (** a _|_ b -> vproj v1 v2 = vzero *)
  Lemma vorth_imply_vproj_eq0 : forall {n} (v1 v2 : vec n), a _|_ b -> vproj v1 v2 = vzero.
  Proof.
    intros. unfold vorth in H. unfold vproj. rewrite H.
    replace (Azero * / (<b, b>)) with Azero. apply vcmul_0_l.
    rewrite ring_mul_0_l; auto.
  Qed.

  (** vunit b -> vproj v1 v2 = <a, b> .* b *)
  Lemma vproj_vunit : forall {n} (v1 v2 : vec n), vunit b -> vproj v1 v2 = <a, b> \.* b.
  Proof. intros. unfold vproj. f_equal. rewrite H. field. apply field_1_neq_0. Qed.

  (* If equip a `Field` *)
  Section OrderedField.
    Context `{HOrderedField : OrderedField A Aadd Azero Aopp Amul Aone Ainv}.
    
    (** vproj (a + b) c = vproj a c + vproj b c *)
    Lemma vproj_vadd : forall {n} (v1 v2 c : vec n),
        c <> vzero -> (vproj (a + b) c = vproj a c + vproj b c)%V.
    Proof.
      intros. unfold vproj. rewrite vdot_vadd_l. rewrite <- vcmul_add. f_equal.
      field. apply vdot_same_neq0_if_vnonzero; auto.
    Qed.
    
    (** vproj (x .* a) b = x .* (vproj v1 v2) *)
    Lemma vproj_vcmul : forall {n} (v1 v2 : vec n) x,
        b <> vzero -> (vproj (x \.* a) b = x \.* (vproj v1 v2))%V.
    Proof.
      intros. unfold vproj. rewrite vdot_vcmul_l. rewrite vcmul_assoc. f_equal.
      field. apply vdot_same_neq0_if_vnonzero; auto.
    Qed.
    
    (** vproj a a = a *)
    Lemma vproj_same : forall {n} (v : vec n), a <> vzero -> vproj a a = a.
    Proof.
      intros. unfold vproj. replace (<a, a> / <a, a>) with Aone; try field.
      apply vcmul_1_l. apply vdot_same_neq0_if_vnonzero; auto.
    Qed.
  End OrderedField.

End vproj.


(* ======================================================================= *)
(** ** Perpendicular component of a matrix respect to another *)
Section vperp.
  
  (* Let's have an field *)
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv}.
  Add Field field_inst : (make_field_theory F).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub v1 v2 := (a + (- b))%A.
  Infix "-" := Asub : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv v1 v2 := (a * (/ b))%A.
  Infix "/" := Adiv : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation vproj := (@vproj _ Aadd Azero Amul Ainv).
  Notation vorth := (@vorth _ Aadd Azero Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Infix "-" := vsub : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  Notation "< a , b >" := (vdot v1 v2) : vec_scope.
  Infix "_|_" := vorth : vec_scope.
  
  (** The perpendicular component of `a` respect to `b` *)
  Definition vperp {n} (v1 v2 : vec n) : vec n := a - vproj v1 v2.

  (** vperp v1 v2 = a - vproj v1 v2 *)
  Lemma vperp_eq_minus_vproj : forall {n} (v1 v2 : vec n), vperp v1 v2 = a - vproj v1 v2.
  Proof. auto. Qed.

  (** vproj v1 v2 = a - vperp v1 v2 *)
  Lemma vproj_eq_minus_vperp : forall {n} (v1 v2 : vec n), vproj v1 v2 = a - vperp v1 v2.
  Proof.
    intros. unfold vperp. unfold vsub. rewrite group_opp_distr.
    rewrite group_opp_opp. move2h (vproj v1 v2). group.
  Qed.

  (** (vproj v1 v2) + (vperp v1 v2) = a *)
  Lemma vproj_plus_vperp : forall {n} (v1 v2 : vec n), vproj v1 v2 + vperp v1 v2 = a.
  Proof. intros. unfold vperp. unfold vsub. move2h a. group. Qed.
  
