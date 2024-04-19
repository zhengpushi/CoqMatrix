
(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix with high performance (去掉NatFun，只使用 Bigarray)
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
Require Export Extraction Sequence.

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


(** * Matrix theory *)
Module MatrixTheory (E : MatrixElement).
  Export E.
  Notation seqsum := (@seqsum _ Aadd 0).

  (** ** abstract operations *)
  (* matrix type *)
  Parameter mat : forall (r c : nat), Type.

  (* Get rows *)
  Parameter mrows : forall {r c} (M : mat r c), nat.

  (* Get columnss *)
  Parameter mcols : forall {r c} (M : mat r c), nat.
  
  (* Get element *)
  Parameter mget : forall {r c} (M : mat r c) (i j : nat), A.
  Notation "M .[ i , j ]" := (mget M i j) : mat_scope.
  
  (* Set element *)
  Parameter mset : forall {r c} (M : mat r c) (i j : nat) (a : A), mat r c.
  Notation "M .[ i , j <- a ]" := (mset M i j a) : mat_scope.
  
  (* Create a matrix with default value *)
  Parameter mcreate : forall r c, mat r c.
  
  (* Create a matrix with a function *)
  Parameter minit : forall r c (f : nat -> nat -> A), mat r c.

  (* equality of two matrices *)
  Parameter meq : forall {r c} (M1 M2 : mat r c), Prop.
  Infix "==" := meq : mat_scope.


  (** ** specifications for abstract operations *)

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

  (** ** Extraction for abstract operations *)
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
  
  Recursive Extraction mget mcreate mset minit.
  Extraction "matrix.ml" mget mget mcreate mset minit.


  (** ** Matrix theory *)
  Open Scope A_scope.
  Open Scope mat_scope.
  
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

  Unset Extraction SafeImplicits.

  ?
  Extraction Implicit mtrans [r c].
  Recursive Extraction mtrans.
  Extraction Implicit mmul [r c s].
  Recursive Extraction mget mmul.
  Extraction Implicit mset [r c].
  Recursive Extraction mget mmul.
  Recursive Extraction mget mmul.
?
  Extract Constant mget => "fun m -> Bigarray.Array2.get m".

  Extraction Implicit mmul [r c s].
  Unset Extraction SafeImplicits.
  Recursive Extraction mget mmul.

End MatrixTheory.

  (* Extract Constant mget => "fun m -> Bigarray.Array2.get m". *)

Recursive Extraction MatrixElementR.
?
Extract Constant M.mat =>
            "(float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array2.t".
Extract Constant M.mget => "fun m -> Bigarray.Array2.get m".
Extract Constant M.mset =>
          "fun m i j a -> Bigarray.Array2.set m i j a; m".
Extraction Implicit M.mget [r c].
Extraction Implicit M.mset [r c].
Extract Constant M.mcreate => "Bigarray.Array2.create Float64 C_layout".
Extract Constant M.minit => "Bigarray.Array2.init Float64 C_layout".


Import MatrixR.
Check mget.

?


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
  Module test_Ocaml.
    Module ME := MatrixModel_Bigarray_Float64.
    Module Export MT := MatrixTheory MatrixElementR ME.
    Import ME.
    Import MT.
    Open Scope A_scope.
    Open Scope mat_scope.

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


