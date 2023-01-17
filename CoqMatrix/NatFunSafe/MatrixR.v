(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Real Matrices
  author    : ZhengPu Shi
  date      : 2021.12
  
  reference : https://www.cs.umd.edu/~rrand/vqc/Matrix.html
 *)

(** * Matrix: Lightweight Real Matrices *)

Require Import Psatz.
Require Import Setoid.
Require Import Arith.
Require Import Bool.
Require Import Program.
Require Import Reals.
Require Import List.
Require Export RExt.

Import ListNotations.

Arguments list {A}.


(* ################################################################# *)
(** * 对一个数列求和，将来用于矩阵乘法等运算 *)
Section Rsum.
  
  (* 定义求和运算 *)
  Fixpoint Rsum (f : nat -> R) (n : nat) : R := 
    match n with
    | O => 0
    | S n' => Rsum f n' +  f n'
    end.
  
  (* 各元素为0，则求和为0 *)
  Lemma Rsum_0 : forall (f : nat -> R) (n : nat),
      (forall x, (x < n)%nat -> f x = 0) -> 
      Rsum f n = 0.  
  Proof.
    intros. 
    induction n.  
    - reflexivity.  
    - simpl.  
      rewrite H by lia. 
      rewrite IHn. ring.  
      intros. apply H; lia.  
  Qed.

  (* 两个数列，对应元素相等，则求和也相等 *)
  Lemma Rsum_eq : forall (f g : nat -> R) (n : nat),
      (forall x, (x < n)%nat -> f x = g x) ->
      Rsum f n = Rsum g n.
  Proof. 
    intros f g n H. 
    induction n.
    + simpl. reflexivity.
    + simpl. 
      rewrite H by lia.
      rewrite IHn; auto.
  Qed.
  
  (* 若数列每个元素等于来自另外两个数列对应元素相加，则该数列求和等于
    另两个数列求和再相加 *)
  Lemma Rsum_plus : forall (f g : nat -> R) (n : nat),
      Rsum (fun x => f x + g x) n = Rsum f n + Rsum g n.  
  Proof. 
    intros f g n. induction n.  
    - simpl. ring.  
    - simpl. rewrite IHn. ring.  
  Qed.

  (* 数列求和的 c 倍，等于各自元素的 c 倍再求和 (左乘) *)
  Lemma Rsum_mult_l : forall c (f : nat -> R) (n : nat),
      c * Rsum f n = Rsum (fun x => c * f x) n.  
  Proof.  
    intros c f n. induction n.  
    - simpl; ring.  
    - simpl. ring_simplify. rewrite IHn. ring.
  Qed.

  (* 数列求和的 c 倍，等于各自元素的 c 倍再求和 (右乘) *)
  Lemma Rsum_mult_r : forall c (f : nat -> R) (n : nat),
      Rsum f n * c = Rsum (fun x => f x * c) n.  
  Proof.  
    intros c f n. induction n.  
    - simpl; ring.  
    - simpl. ring_simplify. rewrite IHn. ring.
  Qed.

  (* 数数列中只有某一项不为0，则求和结果就是这一项的值 *)
  Lemma Rsum_unique : forall (f : nat -> R) (k : R) (n x : nat), 
      (x < n)%nat ->
      f x = k ->
      (forall x', x <> x' -> f x' = 0) ->
      Rsum f n = k.
  Proof.
    (* 证明思路：
    1. 归纳主参数 n
    2. 关键条件 x =? n
     *)
    intros f k n. induction n.
    - intros. lia.
    - intros. simpl. destruct (x =? n)%nat eqn : E1.
      + apply Nat.eqb_eq in E1.
        assert (f n = k).
        { rewrite E1 in H0. auto. }
        assert (Rsum f n = 0).
        { apply Rsum_0. intros. apply H1. subst. lia. }
        rewrite H3. rewrite H2. ring.
      + apply Nat.eqb_neq in E1.
        assert (f n = 0).
        { apply H1. auto. }
        assert (Rsum f n = k).
        { apply IHn with x; auto. lia. }
        rewrite H3,H2. ring.
  Qed.
  
  (* 求和时拆分出最后一项 *)
  Lemma Rsum_extend_r : forall n f, Rsum f n + f n = Rsum f (S n).
  Proof.
    reflexivity.
  Qed.
  
  (* 求和时拆分出第一项 *)
  Lemma Rsum_extend_l : forall n f, f O + Rsum (fun x => f (S x)) n = Rsum f (S n).
  Proof.
    intros n f. induction n.
    + simpl; ring.
    + simpl. ring_simplify. rewrite IHn. simpl. ring.
  Qed.

  (* 求和拆分为两部分 *)
  Lemma Rsum_sum : forall m n f, Rsum f (m + n) = 
                                   Rsum f m + Rsum (fun x => f (m + x)%nat) n. 
  Proof.    
    intros m n f.
    induction m.
    + simpl.  ring_simplify. auto.
    + simpl.
      rewrite IHm.
      remember (fun y => f (m + y)%nat) as g.
      replace (f m) with (g O) by (subst; rewrite plus_0_r; reflexivity).
      replace (f (m + n)%nat) with (g n) by (subst; reflexivity).
      replace (Rsum (fun x : nat => f (S (m + x))) n) with
        (Rsum (fun x : nat => g (S x)) n).
      2:{ apply Rsum_eq. subst. intros. intros; rewrite <- plus_n_Sm. reflexivity. }
      replace (Rsum f m + Rsum g n + g n) with (Rsum f m + (Rsum g n + g n)).
      rewrite Rsum_extend_r.
      replace (Rsum f m + g 0%nat + Rsum (fun x => g (S x)) n)
        with (Rsum f m + (g 0%nat + Rsum (fun x => g (S x)) n)).
      rewrite Rsum_extend_l. auto. ring. ring.
  Qed.


  (* 求和再点积的一个等式：
    (1 + 2 + 3) * (4 + 5) =
    m = 3, n = 2, m * n = 6
    
    x   x/n   x%n   f(x/n)  f(x%n)  f(x/n)*f(x%n)
    0   0     0     1       4       1*4
    1   0     1     1       5       1*5
    2   1     0     2       4       2*4
    3   1     1     2       5       2*5
    4   2     0     3       4       3*4
    5   2     1     3       5       3*5
    所以，新的求和序列是
    = 1*4 + 1*5 + 2*4 + 2*5 + 3*4 + 3*5
    非常巧妙！
   *)
  Lemma Rsum_product : forall m n f g, n <> O ->
                                       Rsum f m * Rsum g n = 
                                         Rsum (fun x => f (x / n)%nat * g (x mod n)%nat) (m * n). 
  Proof.
    intros.
    induction m.
    + simpl; ring.
    + simpl. ring_simplify. rewrite IHm. clear IHm.
      rewrite Rsum_mult_l.    
      remember ((fun x : nat => f (x / n)%nat * g (x mod n)%nat)) as h.
      replace (Rsum (fun x : nat => f m * g x) n) with
        (Rsum (fun x : nat => h ((m * n) + x)%nat) n). 
      2:{
        subst.
        apply Rsum_eq.
        intros x Hx.
        rewrite Nat.div_add_l by assumption.
        rewrite Nat.div_small; trivial.
        rewrite plus_0_r.
        rewrite Nat.add_mod by assumption.
        rewrite Nat.mod_mul by assumption.
        rewrite plus_0_l.
        repeat rewrite Nat.mod_small; trivial. }
      rewrite <- Rsum_sum.
      rewrite plus_comm.
      reflexivity.
  Qed.

End Rsum.


(** * Matrix Definitions and Equivalence **)

(* Declare Scope matrix_scope. *)  (* Temporarily removed for 8.9 compatibility *)
Delimit Scope matrix_scope with M.
Open Scope matrix_scope.
Open Scope R_scope.
Open Scope nat_scope.

(** We define a _matrix_ as a simple function from to nats
    (corresponding to a row and a column) to a complex number. In many
    contexts it would make sense to parameterize matrices over numeric
    types, but our use case is fairly narrow, so matrices of complex
    numbers will suffice. *)

Definition Matrix (m n : nat) := nat -> nat -> R.

Bind Scope matrix_scope with Matrix.
Notation Vector n := (Matrix n 1).
Notation Square n := (Matrix n n).

(* Lists to Vectors / Matrices. *)
Definition l2V (l : list) : Vector (length l) :=
  (fun x y => nth x l 0)%R.

Definition l2M (l : @list list) : Matrix (length l) (length (hd [] l)) :=
  (fun x y => nth y (nth x l []) 0)%R.

(* Example *)
Section test.
  Example lst1 := [1;2;3]%R.
  Example lst2 := [4;5;6]%R.
  Example v1 := l2V lst1.
  Example v2 := l2V lst2.
  Example m1 := l2M [lst1;lst2].
  Compute v1.
  Compute m1 0 0.
  Compute m1 0 2.
End test.

Arguments l2V l i j /.
Arguments l2M l i j /.


(** Vectors / Matrices to Lists *)

(* Fetch a row *)

(* Aux function, cnt initial is 0 *)
Fixpoint MRow_aux (r c : nat) (ri : nat) (cnt : nat) (m : Matrix r c) 
  : list := match c with
            | O => nil
            | S c' => m ri cnt :: (MRow_aux r c' ri (S cnt) m)
            end.
Definition MRow {r c : nat} (ri : nat) (m : Matrix r c) := MRow_aux r c ri 0 m.
Compute MRow 0 m1.
Compute MRow 1 m1.
Compute MRow 2 m1.

(* Fetch a column *)

(* Aux function, cnt initial is 0 *)
Fixpoint MCol_aux (r c : nat) (ci : nat) (cnt : nat) (m : Matrix r c) 
  : list := match r with
            | O => nil
            | S r' => m cnt ci :: (MCol_aux r' c ci (S cnt) m)
            end.
Definition MCol {r c : nat} (ci : nat) (m : Matrix r c) := MCol_aux r c ci 0 m.
Compute MCol 0 m1.
Compute MCol 1 m1.
Compute MCol 2 m1.
Compute MCol 3 m1.

(* Vector to List *)
Definition V2l {n} (v : Vector n):= MCol 0 v. 
Compute V2l v1.
Compute V2l v2.

(* Matrix to list list *)
Fixpoint M2l_aux {r c : nat} (cnt : nat) (m : Matrix r c) : list := 
  match r with
  | O => nil
  | S r' => MRow cnt m :: (@M2l_aux r' c (S cnt) m)
  end.
Definition M2l {r c} (m : Matrix r c) := M2l_aux 0 m.
Compute M2l m1.

(** Note that the dimensions of the matrix aren't being used here. In
    practice, a matrix is simply a function on any two nats. However,
    we will used these dimensions to define equality, as well as the
    multiplication and kronecker product operations to follow. *)

(* If every element of corresponding elements of two matrices, then we called 
 they are mat_equiv. *)
Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop := 
  forall i j, i < m -> j < n -> A i j = B i j.

Infix "==" := mat_equiv (at level 70).

(** Let's prove some important notions about matrix equality. *)

Lemma mat_equiv_refl : forall {m n} (A : Matrix m n), A == A.
Proof.
  intros m n A i j Hi Hj. reflexivity.
Qed.

Lemma mat_equiv_sym : forall {m n} (A B : Matrix m n), A == B -> B == A.
Proof.
  intros m n A B H i j Hi Hj.
  rewrite H; easy.
Qed.

Lemma mat_equiv_trans : forall {m n} (A B C : Matrix m n),
    A == B -> B == C -> A == C.
Proof.
  intros m n A B C HAB HBC.
  (* a failure attempt *)
  Fail rewrite HAB.
  (* unfold it to accomplish the proof *)
  intros i j Hi Hj.
  rewrite HAB,HBC; trivial.
Qed.

(* Told to Coq that [==] is equivalence relation *)
Add Parametric Relation m n : (Matrix m n) (@mat_equiv m n)
    reflexivity proved by mat_equiv_refl
    symmetry proved by mat_equiv_sym
    transitivity proved by mat_equiv_trans
    as mat_equiv_rel.

(** Now we can use matrix equivalence to rewrite! *)

Lemma mat_equiv_trans2 : forall {m n} (A B C : Matrix m n),
    A == B -> B == C -> A == C.
Proof.
  intros m n A B C HAB HBC.
  rewrite HAB.
  apply HBC.
Qed.

(* ################################################################# *)
(** * Basic Matrices and Operations *)

Close Scope nat_scope.
Open Scope R_scope.

(** Because we will use these so often, it is good to have them in matrix scope. *)
Notation "m =? n" := (Nat.eqb m n) (at level 70) : matrix_scope.
Notation "m <? n" := (Nat.ltb m n) (at level 70) : matrix_scope.
Notation "m <=? n" := (Nat.leb m n) (at level 70) : matrix_scope.

Open Scope matrix_scope.

(* Identity Matrix *)
Definition I (n : nat) : Matrix n n := fun i j => if (i =? j)%nat then 1 else 0.

(* Zero Matrix *)
Definition Zero (m n : nat) : Matrix m n := fun _ _ => 0. 

(* Scalar multiplication *)
Definition Mscale {m n : nat} c (A : Matrix m n) : Matrix m n := 
  fun i j => c * A i j.

(* Addition *)
Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun i j => A i j + B i j.

Infix "+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix "*" := Mscale (at level 40, left associativity) : matrix_scope.

Lemma Mplus_assoc : forall {m n} (A B C : Matrix m n), (A + B) + C == A + (B + C).
Proof.
  intros m n A B C i j Hi Hj.
  unfold Mplus.
  lra.
Qed.

Lemma Mplus_comm : forall {m n} (A B : Matrix m n), A + B == B + A.
Proof.
  (* WORKED IN CLASS *)
  intros m n A B i j Hi Hj.
  unfold Mplus.
  lra.
Qed.

Lemma Mplus_0_l : forall {m n} (A : Matrix m n), Zero m n + A == A. 
Proof.
  (* WORKED IN CLASS *)
  intros m n A i j Hi Hj.
  unfold Zero, Mplus.
  lra.
Qed.

(* Let's try one without unfolding definitions. *)
Lemma Mplus_0_r : forall {m n} (A : Matrix m n), A + Zero m n == A. 
Proof.
  (* WORKED IN CLASS *)
  intros m n A.
  rewrite Mplus_comm.
  apply Mplus_0_l.
Qed.

Lemma Mplus3_first_try : forall {m n} (A B C : Matrix m n), (B + A) + C == A + (B + C).
Proof.
  (* WORKED IN CLASS *)
  intros m n A B C.
  Fail rewrite (Mplus_comm B A).
Abort.

(** What went wrong? While we can rewrite using [==], we don't
    know that [+] _respects_ [==]. That is, we don't know that if 
    [A == A'] and [B == B'] then [A + B == A' + B'] -- or at least, we
    haven't told Coq that.

   Let's take a look at an example of a unary function that doesn't
   respect [==] *)

Definition shift_right {m n} (A : Matrix m n) (k : nat) : Matrix m n :=
  fun i j => A i (j + k)%nat.

Lemma shift_unequal : exists m n (A A' : Matrix m n) (k : nat),
    A == A' /\ ~ (shift_right A k == shift_right A' k). 
Proof.
  set (A := (fun i j => if (j <? 2)%nat then 1 else 0) : Matrix 2 2).
  set (A' := (fun i j => if (j <? 3)%nat then 1 else 0) : Matrix 2 2).  
  exists _, _, A, A', 1%nat.
  split.
  - intros i j Hi Hj.
    unfold A, A'.  
    destruct j as [|[|]]; destruct i as [|[|]]; trivial; lia.
  - intros F.
    assert (1 < 2)%nat by lia.
    specialize (F _ _ H H).
    unfold A, A', shift_right in F.
    simpl in F.
    inversion F; lra.
Qed.

(** Let's show that [+] does respect [==] *)

Lemma Mplus_compat : forall {m n} (A B A' B' : Matrix m n),
    A == A' -> B == B' -> A + B == A' + B'.
Proof.
  (* WORKED IN CLASS *)
  intros m n A B A' B' HA HB.
  intros i j Hi Hj.
  unfold Mplus.
  rewrite HA by lia.
  rewrite HB by lia.
  reflexivity.
Qed.

Add Parametric Morphism m n : (@Mplus m n)
    with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mplus_mor.
Proof.
  intros A A' HA B B' HB.
  apply Mplus_compat; easy.
Qed.

(** Now let's return to that lemma... *)

Lemma Mplus3 : forall {m n} (A B C : Matrix m n), (B + A) + C == A + (B + C).
Proof.
  (* WORKED IN CLASS *)
  intros m n A B C.
  rewrite (Mplus_comm B A).
  apply Mplus_assoc.
Qed.

(** Mscale is similarly compatible with [==], but requires a slightly
    different lemma: *)

Lemma Mscale_compat : forall {m n} c c' (A A' : Matrix m n),
    c = c' -> A == A' -> c * A == c' * A'.
Proof.
  intros m n c c' A A' Hc HA.
  intros i j Hi Hj.
  unfold Mscale.
  rewrite Hc, HA; easy.
Qed.

Add Parametric Morphism m n : (@Mscale m n)
    with signature eq ==> mat_equiv ==> mat_equiv as Mscale_mor.
Proof.
  intros; apply Mscale_compat; easy.
Qed.

(** Let's move on to the more interesting matrix functions: *)

(* 迹 *)
Definition trace {n : nat} (A : Square n) := 
  Rsum (fun x => A x x) n.

(* 乘法 *)
Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o := 
  fun x z => Rsum (fun y => A x y * B y z)%R n.

Open Scope nat_scope.

(* 转置 *)
Definition transpose {m n} (A : Matrix m n) : Matrix n m := 
  fun x y => A y x.

(** We can derive the dot product and its complex analogue, the 
    _inner product_, from matrix multiplication. *)

(* 两个向量的点积。这里用矩阵乘法来定义点积，而我们之前是用点积来定义乘法 *)
Definition dot {n : nat} (A : Vector n) (B : Vector n) :=
  Mmult (transpose A) B 0 0.

Compute dot v1 v2.

Close Scope nat_scope.

Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope. 
Infix "∘" := dot (at level 40, left associativity) : matrix_scope.

(* ================================================================= *)
(** ** Compatibility lemmas *)

Lemma trace_compat : forall {n} (A A' : Square n),
    A == A' -> trace A = trace A'.
Proof.
  intros n A A' H.
  apply Rsum_eq.
  intros x Hx.
  rewrite H; easy.
Qed.

Add Parametric Morphism n : (@trace n)
    with signature mat_equiv ==> eq as trace_mor.
Proof.
  intros; apply trace_compat; easy.
Qed.

Lemma Mmult_compat : forall {m n o} (A A' : Matrix m n) (B B' : Matrix n o),
    A == A' -> B == B' -> A × B == A' × B'.
Proof.
  intros m n o A A' B B' HA HB i j Hi Hj.
  unfold Mmult.
  apply Rsum_eq; intros x Hx.
  rewrite HA, HB; easy.
Qed.

Add Parametric Morphism m n o : (@Mmult m n o)
    with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mmult_mor.
Proof.
  intros. apply Mmult_compat; easy.
Qed.

Lemma transpose_compat : forall {m n} (A A' : Matrix m n),
    A == A' -> A⊤ == A'⊤.
Proof.
  intros m n A A' H.
  intros i j Hi Hj.
  unfold transpose.
  rewrite H; easy.
Qed.

Add Parametric Morphism m n : (@transpose m n)
    with signature mat_equiv ==> mat_equiv as transpose_mor.
Proof.
  intros. apply transpose_compat; easy.
Qed.


(* ################################################################# *)
(** * Matrix Properties *)

(* 这个作者没给，可能是太平凡了 *)
Lemma Mtrans_trans : forall {m n : nat} (A : Matrix m n),
    transpose (transpose A) == A.
Proof.
  intros. unfold transpose. unfold mat_equiv. auto.
Qed.

(* 乘法结合律 *)
Theorem Mmult_assoc : forall {m n o p : nat} (A : Matrix m n) (B : Matrix n o) 
                             (C: Matrix o p), A × B × C == A × (B × C).
Proof.
  intros m n o p A B C i j Hi Hj.
  unfold Mmult.
  induction n.
  + simpl.
    clear B.  (* 丢掉一个前提。*)
    induction o. reflexivity.
    simpl. rewrite IHo. lra.
  + simpl. 
    rewrite <- IHn.
    simpl.
    rewrite Rsum_mult_l.
    rewrite <- Rsum_plus.
    apply Rsum_eq; intros.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_assoc.
    reflexivity.
Qed.


(* ################################################################# *)
(** * Matrix Automation *)

(** A useful tactic for solving A == B for concrete A, B *)

Ltac solve_end :=
  match goal with
  | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.

Ltac by_cell := 
  intros;
  let i := fresh "i" in 
  let j := fresh "j" in 
  let Hi := fresh "Hi" in 
  let Hj := fresh "Hj" in 
  intros i j Hi Hj; try solve_end;
  repeat (destruct i as [|i]; simpl; [|apply lt_S_n in Hi]; try solve_end); clear Hi;
  repeat (destruct j as [|j]; simpl; [|apply lt_S_n in Hj]; try solve_end); clear Hj.

Ltac lma := by_cell; compute; lra.

(** Let's test it! *)                                                     
Lemma scale0_concrete : 0 * I 10 == Zero _ _.
Proof.
  lma.
Qed.

(* ################################################################# *)
(** * Matrix Library *)

(* 数乘 0 *)
Lemma Mscale_0_l : forall {m n : nat} (A : Matrix m n), 0 * A == Zero m n.
Proof.
  intros. lma.
Qed.

Lemma Mscale_0_r : forall {m n : nat} c, c * Zero m n == Zero m n.
Proof.
  intros. lma.
Qed.

(* 数乘 1 *)
Lemma Mscale_1_l : forall {m n : nat} (A : Matrix m n), 1 * A == A.
Proof.
  intros. lma.
Qed.

Lemma Mscale_1_r : forall {n : nat} c,
    c * I n == fun x y => if (x =? y) then c else 0.
Proof.
  intros n c i j _ _.
  unfold I, Mscale; simpl. 
  destruct (i =? j); lra.
Qed.

(* 乘法 Zero *)
Lemma Mmult_0_l : forall {m n o : nat} (A : Matrix n o), Zero m n × A == Zero m o.
Proof.
  intros m n o A i j Hi Hj.
  unfold Mmult, Zero.
  rewrite Rsum_0. easy.
  intros. lra.
Qed.    

Lemma Mmult_0_r : forall {m n o : nat} (A : Matrix m n), A × Zero n o == Zero m o.
Proof.
  intros m n o A i j Hi Hj.
  unfold Mmult, Zero.
  rewrite Rsum_0. easy.
  intros. lra.
Qed.

(* 乘法 I *)
Lemma Mmult_1_l: forall {m n : nat} (A : Matrix m n), 
    I m × A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  eapply Rsum_unique. apply Hi.
  unfold I. rewrite Nat.eqb_refl. lra.
  intros x Hx.
  unfold I.
  apply Nat.eqb_neq in Hx. rewrite Hx.
  lra.
Qed.

Lemma Mmult_1_r: forall {m n : nat} (A : Matrix m n), 
    A × I n == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  eapply Rsum_unique. apply Hj.
  unfold I. rewrite Nat.eqb_refl. lra.
  intros x Hx.
  unfold I.
  apply Nat.eqb_neq in Hx. rewrite Nat.eqb_sym. rewrite Hx.
  lra.
Qed.

(* 单位阵转置 *)
Lemma id_transpose_eq : forall {n : nat}, (I n)⊤ == (I n).
Proof. 
  intros. by_cell. 
  unfold transpose, I.
  rewrite Nat.eqb_sym.
  reflexivity.
Qed.

Lemma zero_transpose_eq : forall {m n : nat}, (@Zero m n)⊤ == @Zero m n.
Proof.
  reflexivity.
Qed.


(* 数乘结合律 *)
Lemma Mscale_assoc : forall {m n : nat} (x y : R) (A : Matrix m n),
    x * (y * A) == (x * y)%R * A.
Proof.
  lma.
Qed.

(* 数乘对加法分配律 *)
Lemma Mscale_plus_dist_l : forall {m n : nat} (x y : R) (A : Matrix m n),
    (x + y)%R * A == x * A + y * A.
Proof.
  lma.
Qed.

Lemma Mscale_plus_dist_r : forall {m n : nat} (x : R) (A B : Matrix m n),
    x * (A + B) == x * A + x * B.
Proof.
  lma.
Qed.

(* 乘法对加法分配律 *)
Lemma Mmult_plus_dist_l : forall {m n o : nat} (A : Matrix m n) (B C : Matrix n o), 
    A × (B + C) == A × B + A × C.
Proof. 
  intros. intros i j _ _.
  unfold Mplus, Mmult.
  rewrite <- Rsum_plus.
  apply Rsum_eq_bounded; intros.
  rewrite Rmult_plus_dist_l. 
  reflexivity.
Qed.

Lemma Mmult_plus_dist_r : forall {m n o : nat} (A B : Matrix m n) (C : Matrix n o), 
    (A + B) × C == A × C + B × C.
Proof. 
  intros. intros i j _ _.
  unfold Mplus, Mmult.
  rewrite <- Rsum_plus.
  apply Rsum_eq_bounded; intros.
  rewrite Rmult_plus_dist_r. 
  reflexivity.
Qed.

(* 数乘对乘法分配 *)
Lemma Mscale_mult_dist_l : forall {m n o : nat} (x : R) (A : Matrix m n) (B : Matrix n o), 
    ((x * A) × B) == x * (A × B).
Proof. 
  intros. intros i j _ _.
  unfold Mscale, Mmult.
  rewrite Rsum_mult_l.
  apply Rsum_eq_bounded; intros.
  lra.
Qed.

Lemma Mscale_mult_dist_r : forall {m n o : nat} (x : R) (A : Matrix m n) (B : Matrix n o),
    (A × (x * B)) == x * (A × B).
Proof.
  intros. intros i j _ _.
  unfold Mscale, Mmult.
  rewrite Rsum_mult_l.
  apply Rsum_eq_bounded; intros.
  lra.
Qed.


(*******************************)
(* Automation *)
(*******************************)

Lemma double_mult : forall (n : nat), (n + n = 2 * n)%nat.
Proof.
  intros. lia.
Qed.

Lemma pow_two_succ_l : forall x, (2^x * 2 = 2 ^ (x + 1))%nat.
Proof.
  intros. rewrite mult_comm. rewrite <- Nat.pow_succ_r'. intuition.
Qed.

Lemma pow_two_succ_r : forall x, (2 * 2^x = 2 ^ (x + 1))%nat.
Proof.
  intros. rewrite <- Nat.pow_succ_r'. intuition.
Qed.

Lemma double_pow : forall (n : nat), (2^n + 2^n = 2^(n+1))%nat. 
Proof.
  intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity.
Qed.

Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> (a^m = b^n)%nat.
Proof.
  intuition.
Qed.

Ltac unify_pows_two :=
  repeat match goal with
    (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
    | [ |- context[ 4%nat ]]                  => replace 4%nat with (2^2)%nat by reflexivity
    | [ |- context[ (0 + ?a)%nat]]            => rewrite plus_0_l 
    | [ |- context[ (?a + 0)%nat]]            => rewrite plus_0_r 
    | [ |- context[ (1 * ?a)%nat]]            => rewrite Nat.mul_1_l 
    | [ |- context[ (?a * 1)%nat]]            => rewrite Nat.mul_1_r 
    | [ |- context[ (2 * 2^?x)%nat]]          => rewrite <- Nat.pow_succ_r'
    | [ |- context[ (2^?x * 2)%nat]]          => rewrite pow_two_succ_l
    | [ |- context[ (2^?x + 2^?x)%nat]]       => rewrite double_pow 
    | [ |- context[ (2^?x * 2^?y)%nat]]       => rewrite <- Nat.pow_add_r 
    | [ |- context[ (?a + (?b + ?c))%nat ]]   => rewrite plus_assoc 
    | [ |- (2^?x = 2^?y)%nat ]                => apply pow_components; try lia 
    end.

(** Restoring Matrix dimensions *)
Ltac is_nat_equality :=
  match goal with 
  | |- ?A = ?B => match type of A with
                  | nat => idtac
                  end
  end.

Lemma f_equal_gen : forall {A B} (f g : A -> B) a b, f = g -> a = b -> f a = g b.
Proof.
  intros. subst. reflexivity.
Qed.

Ltac unify_matrix_dims tac := 
  try reflexivity; 
  repeat (apply f_equal_gen; try reflexivity; 
          try (is_nat_equality; tac)).

Ltac restore_dims_rec A :=
  match A with
  (* special cases *)
  | ?A × I _          => let A' := restore_dims_rec A in 
                          match type of A' with 
                          | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (I n'))
                          end
  | I _ × ?B          => let B' := restore_dims_rec B in 
                          match type of B' with 
                          | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (I n')  B')
                          end
  | ?A × @Zero ?n ?n  => let A' := restore_dims_rec A in 
                          match type of A' with 
                          | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (@Zero n' n'))
                          end
  | @Zero ?n ?n × ?B  => let B' := restore_dims_rec B in 
                          match type of B' with 
                          | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero n' n') B')
                          end
  | ?A × @Zero ?n ?o  => let A' := restore_dims_rec A in 
                          match type of A' with 
                          | Matrix ?m' ?n' => constr:(@Mmult m' n' o A' (@Zero n' o))
                          end
  | @Zero ?m ?n × ?B  => let B' := restore_dims_rec B in 
                          match type of B' with 
                          | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero m n') B')
                          end
  | ?A + @Zero ?m ?n => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mplus m' n' A' (@Zero m' n'))
                        end
  | @Zero ?m ?n + ?B => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?m' ?n' => constr:(@Mplus m' n' (@Zero m' n') B')
                        end
  (* general cases *)
  | ?A == ?B  => let A' := restore_dims_rec A in 
                 let B' := restore_dims_rec B in 
                 match type of A' with 
                 | Matrix ?m' ?n' => constr:(@mat_equiv m' n' A' B')
                 end
  | ?A × ?B   => let A' := restore_dims_rec A in 
                  let B' := restore_dims_rec B in 
                  match type of A' with 
                  | Matrix ?m' ?n' =>
                      match type of B' with 
                      | Matrix ?n'' ?o' => constr:(@Mmult m' n' o' A' B')
                      end
                  end 
  | ?A + ?B => let A' := restore_dims_rec A in 
               let B' := restore_dims_rec B in 
               match type of A' with 
               | Matrix ?m' ?n' =>
                   match type of B' with 
                   | Matrix ?m'' ?n'' => constr:(@Mplus m' n' A' B')
                   end
               end
  | ?c * ?A => let A' := restore_dims_rec A in 
               match type of A' with
               | Matrix ?m' ?n' => constr:(@Mscale m' n' c A')
               end
  (* Handle functions applied to matrices *)
  | ?f ?A    => let f' := restore_dims_rec f in 
                let A' := restore_dims_rec A in 
                constr:(f' A')
  (* default *)
  | ?A       => A
  end.

Ltac restore_dims tac := 
  match goal with
  | |- ?A      => let A' := restore_dims_rec A in 
                  replace A with A' by unify_matrix_dims tac
  end.

(* 终于合成了两个可带或可不带参数的策略 *)
Tactic Notation "restore_dims" tactic(tac) := restore_dims tac.

Tactic Notation "restore_dims" := restore_dims (try ring; unify_pows_two; simpl; lia).

(*************************)
(* Matrix Simplification *)
(*************************)

(* 数据库名称可能的解释， U_db : User database *)
Hint Unfold Mplus Mmult Mscale I : U_db. 

Hint Rewrite @Mmult_1_l @Mmult_1_r @Mscale_1_l 
  @id_transpose_eq : M_db_light.
Hint Rewrite @Mmult_0_l @Mmult_0_r @Mplus_0_l @Mplus_0_r
  @Mscale_0_l @Mscale_0_r @zero_transpose_eq : M_db_light.

(* I don't like always doing restore_dims first, but otherwise sometimes leaves 
   unsolvable WF_Matrix goals. *)
Ltac Msimpl_light := restore_dims; autorewrite with M_db_light.

Ltac Msimpl := restore_dims; autorewrite with M_db_light.


(* Sun Jan 19 21:29:28 CST 2020 *)

(* ################################################################# *)
(** * Matrix Test *)

Module matrix_test.
  (* ref:
  https://en.wikipedia.org/wiki/Matrix_(mathematics)#Basic_operations
   *)
  
  Definition m1 := l2M [[1;3;1];[1;0;0]].
  Definition m2 := l2M [[0;0;5];[7;5;0]].
  Definition m3 := l2M [[1;3;6];[8;5;0]].
  Example mplus_m1_m2_eq_m3 : m1 + m2 == m3. lma. Qed.
  
  Definition m4 := l2M [[1;8;-3];[4;-2;5]].
  Definition m5 := l2M [[2;16;-6];[8;-4;10]].
  Example mscale_2_m4_eq_m5 : 2 * m4 == m5. lma. Qed.
  
  Definition m6 := l2M [[1;2;3];[0;-6;7]].
  Definition m7 := l2M [[1;0];[2;-6];[3;7]].
  Example mtrans_m6_eq_m7 : m6 ⊤ == m7. lma. Qed.
  
  Open Scope R.
  Parameter θ ψ φ : R.
  Definition Rx (α : R) : Matrix 3 3 := l2M
                                           [[1;  0;        0      ];
                                            [0;  cos α;    sin α ];
                                            [0;  -sin α;   cos α ]].

  Definition Ry (β : R) : Matrix 3 3 := l2M 
                                           [[cos β;  0;  -sin β];
                                            [0;      1;  0     ];
                                            [sin β;  0;  cos β ]].

  Definition Rz (γ : R) : Matrix 3 3 := l2M 
                                           [[cos γ;    sin γ;  0];
                                            [-sin γ;   cos γ;  0];
                                            [0;        0;       1]].
  
  Definition R_b_e_direct : Matrix 3 3 := l2M [
                                              [cos θ * cos ψ; 
                                               cos ψ * sin θ * sin φ - sin ψ * cos φ;
                                               cos ψ * sin θ * cos φ + sin φ * sin ψ];
                                              [cos θ * sin ψ; 
                                               sin ψ * sin θ * sin φ + cos ψ * cos φ;
                                               sin ψ * sin θ * cos φ - cos ψ * sin φ];
                                              [-sin θ; sin φ * cos θ; cos φ * cos θ]
                                            ].
  
  Open Scope M.
  Opaque cos sin.
  Lemma Rx_Ry_Rz_eq_Rbe : (Rz ψ)⊤ × (Ry θ)⊤ × (Rx φ)⊤ == R_b_e_direct. lma. Qed.
  
  
  
End matrix_test.


(* ################################################################# *)
(** * Vector Releated Definitions & Operations *)

(* 向量加法 *)
Definition vadd {n} (v1 v2 : Vector n) : Vector n :=
  Mplus v1 v2.

(* 向量数乘 *)
Definition vcmul {n} c (v : Vector n) : Vector n :=
  Mscale c v.
Definition vmulc {n} (v : Vector n) c : Vector n :=
  Mscale c v.

(* 零向量 *)
Definition vzero n : Vector n := fun r c => 0.

(* 取元素 *)
Definition vnth {n} i (v : Vector n) : R := v i 0%nat.

(* 指定维数的向量 *)
Definition V1 := Vector 1.
Definition V2 := Vector 2.
Definition V3 := Vector 3.
Definition V4 := Vector 4.

(* 指定分量个数的元组 *)
Definition T1 := R%type.
Definition T2 := (R * R)%type.
Definition T3 := (R * R * R)%type.
Definition T4 := (R * R * R * R)%type.

(* 元组、向量 互相构造 *)
Definition T3_to_V3 (t : T3) : V3 :=
  let '(x,y,z) := t in
  l2V [x;y;z].

Definition V3_to_T3 (v : V3) : T3 :=
  (v 0 0, v 1 0, v 2 0)%nat.

Compute T3_to_V3 (1,2,3).
Compute V3_to_T3 (T3_to_V3 (1,2,3)).

(* V3斜对称矩阵 *)
Definition skew_sym_mat_of_T3 (v : V3) : Matrix 3 3 :=
  let '(x,y,z) := V3_to_T3 v in
  l2M [[0;-z;y];[z;0;-x];[-y;x;0]].

(* 两个V3叉乘，向量积 *)
Definition v3cross (v1 v2 : V3) : Vector 3 :=
  (skew_sym_mat_of_T3 v1) × v2.

(* 3维零向量 *)
Definition v3zero : V3 := T3_to_V3 (0,0,0).

(* 矩阵转标量，取第 0 0 个元素 *)
Definition scalar_of_mat {r c} (m : Matrix r c) := (m 0 0)%nat.

