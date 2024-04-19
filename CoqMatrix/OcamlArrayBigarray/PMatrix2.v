(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix with high performance (直接在NatFun上开发，但又要映射到 Bigarray)
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


Require Export Extraction ExtrOcamlBasic ExtrOcamlNatInt MyExtrOCamlR.
Require Export Extraction NatExt ListExt Hierarchy QcExt RExt.

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

(* Try to rewrite *)
(* Ltac try_rw := *)
(*   match goal with *)
(*   | [H : ?a = ?b |- ?f ?a _ _ = ?f ?b _ _]     => rewrite H *)
(*   | [H : ?a = ?b |- ?f ?a _ = ?f ?b _]     => rewrite H *)
(*   | [H : ?a = ?b |- ?f ?a = ?f ?b ]     => rewrite H *)
(*   end. *)

(* Do logic works *)
Ltac logic :=
  repeat
    (match goal with
     | [|- _ -> _]              => intros
     | [H : _ /\ _ |- _]         => destruct H
     | [ |- _ /\ _ ]             => split
     | [H : _ |- _ <-> _ ]       => split; intros
     | [H : ?a = ?b |- _ ]      => try progress (rewrite H)
     | [H : ?a <> ?b |- False]       => destruct H
     end;
     auto).


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


(** * Matrix theory by natural-index-function *)
Module MatrixTheory (E : MatrixElement).
  Export E.

  (** ** Matrix model by natural-indexing-function *)
  (* matrix with natural-indexing-function and dimensions encoded by dependent type *)
  Inductive t (r c : nat) := mk_t (f : nat -> nat -> A).
  Arguments mk_t {r c}.
  
  (* convert matrix `x` to function *)
  (* Definition t2f {r c} (x : t r c) : nat -> nat -> A := let '(mk_t _ _ f) := x in f. *)
  (* Coercion t2f : t >-> Funclass. *)

  (** ** Core operations *)
  
  (* matrix type *)
  Definition mat (r c : nat) := t r c.
  Notation smat n := (mat n n).

  (* M.[i,j] *)
  Definition mget {r c} (M : mat r c) (i j : nat) : A :=
    let '(mk_t fM) := M in fM i j.
  Notation "M .[ i , j ]" := (mget M i j) : mat_scope.

  (* Convert from matrix to function *)
  Definition m2f {r c} (M : mat r c) : nat -> nat -> A := fun i j => M.[i,j].
  Coercion m2f : mat >-> Funclass.
  
  (* M.[i,j<-a] *)
  Definition mset {r c} (M : mat r c) (i j : nat) (a : A) : mat r c :=
    mk_t (fun i0 j0 => if (i0 =? i) && (j0 =? j) then a else M i0 j0).
  Notation "M .[ i , j <- a ]" := (mset M i j a) : mat_scope.
  
  (* Create a matrix with a function *)
  Definition minit r c (f : nat -> nat -> A) : mat r c := mk_t f.
  
  (* Convert from function to matrix *)
  Definition f2m {r c} (f : nat -> nat -> A) : mat r c := minit r c f.
  
  (* Create a matrix with default value *)
  Definition mcreate r c : mat r c := f2m (fun i0 j0 => 0).


  (** ** controlling extraction for (float64,c_layout) *)
  Extract Constant mat =>
            "(float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array2.t".
  Extract Constant mget => "Bigarray.Array2.get".
  Extract Constant mset => "fun m i j a -> Bigarray.Array2.set m i j a; m".
  Extract Constant minit => "Bigarray.Array2.init Float64 C_layout".
  Extract Constant mcreate => "Bigarray.Array2.create Float64 C_layout".
  Extraction Implicit mget [r c].
  Extraction Implicit mset [r c].
  Unset Extraction SafeImplicits.

(*   (* 在 functor 内部抽取的ocaml代码是正确的Bigarray，但在外部时抽取的就不是了 *) *)
(*   Recursive Extraction MatrixElementR mget mset minit mcreate. *)
(*   Extraction "matrix.ml" MatrixElementR mget mset minit mcreate. *)
(*   (* Recursive Extraction mget mset minit mcreate. *) *)
(*   (* Extraction "matrix.ml" mget mset minit mcreate. *) *)
(* End MatrixTheory. *)
(* Module M := MatrixTheory MatrixElementR. *)
(* Extract Constant M.mat => *)
(*           "(float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array2.t". *)
(* Recursive Extraction M. *)

  (** ** specification of core operations *)
  
  (* equality of two matrices *)
  Definition meq {r c} (M1 M2 : mat r c) : Prop :=
    forall i j, i < r -> j < c -> m2f M1 i j = M2 i j.
  Infix "==" := meq : mat_scope.
  
  (* meq is equivalent relation *)
  Lemma meq_equiv : forall {r c}, Equivalence (@meq r c).
  Proof.
    repeat constructor; repeat intro.
    rewrite H; auto. rewrite H, H0; auto.
  Qed.
  Existing Instance meq_equiv.
  
  Open Scope nat_scope.

  (*
  (* Get element of a matrix after update with same index return the new value *)
  Lemma mset_eq : forall {r c} (M : mat r c) (i j : nat) (a : A),
      i < r -> j < c -> (M.[i,j<-a]).[i,j] = a.
  Proof.
  (* Get element of a matrix after update with different index return the old value *)
  Lemma mset_neq_i : forall {r c} (M : mat r c) (i j i0 : nat) (a : A),
      i < r -> j < c -> i0 < r -> i <> i0 -> (M.[i,j<-a]).[i0,j] = M.[i0,j].
  Lemma mset_neq_j : forall {r c} (M : mat r c) (i j j0 : nat) (a : A),
      i < r -> j < c -> j0 < c -> j <> j0 -> (M.[i,j<-a]).[i,j0] = M.[i,j0].
  Lemma mset_neq_ij : forall {r c} (M : mat r c) (i j i0 j0 : nat) (a : A),
      i < r -> j < c -> i0 < r -> j0 < c -> i <> i0 -> j <> j0 ->
      (M.[i,j<-a]).[i0,j0] = M.[i,j].
  
  (* Update element with its own value won't change the matrix *)
  Lemma mset_same : forall {r c} (M : mat r c) (i j : nat) (a : A),
      i < r -> j < c -> M.[i,j<-M.[i,j]] == M.
  
  (* Update element twice at same position will only keep last operation *)
  Lemma mset_shadow : forall {r c} (M : mat r c) (i j : nat) (a b : A),
      i < r -> j < c -> M.[i,j<-a].[i,j<-b] == M.[i,j<-b].
  (* Update element twice at different position can exchange the operation *)
  Lemma mset_permute_i : forall {r c} (M : mat r c) (i j i0 : nat) (a b : A),
      i < r -> j < c -> i0 < r -> i <> i0 ->
      M.[i,j<-a].[i0,j<-b] == M.[i0,j<-b].[i,j<-a].
  Lemma mset_permute_j : forall {r c} (M : mat r c) (i j j0 : nat) (a b : A),
      i < r -> j < c -> j0 < c -> j <> j0 ->
      M.[i,j<-a].[i,j0<-b] == M.[i,j0<-b].[i,j<-a].
  Lemma mset_permute_ij : forall {r c} (M : mat r c) (i j i0 j0 : nat) (a b : A),
      i < r -> j < c -> i0 < r -> j0 < c -> i <> i0 -> j <> j0 ->
      M.[i,j<-a].[i0,j0<-b] == M.[i0,j0<-b].[i,j<-a].

  (* Get element from a new created matrix return zero *)
  Lemma mget_mcreate : forall {r c} (i j : nat),
      i < r -> j < c -> (mcreate r c).[i,j] = 0.
  (* Update element of a new created matrix with zero won't change it *)
  Lemma mset_mcreate_same : forall {r c} (i j : nat),
      i < r -> j < c -> (mcreate r c).[i,j<-0] == (mcreate r c).
  
  (* Get element from of a function-generated matrix yields its corresponding value *)
  Lemma mget_minit : forall {r c} f i j,
      i < r -> j < c -> (minit r c f).[i,j] = f i j.
  (* Generate matrix from function is injective *)
  Lemma minit_inj : forall {r c} (f g : nat -> nat -> A),
      minit r c f == minit r c g -> (forall i j, i < r -> j < c -> f i j = g i j).
  
   *)
  

  (** ** Matrix theories -- basic part *)

  Open Scope A_scope.
  
  Notation seqsum := (seqsum 0 Aadd).

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

  Recursive Extraction MatrixElementR madd.
  Extract Constant A => "float".
  Extract Constant E.A => "float".
  Extract Constant E.Azero => "0.".
  Recursive Extraction MatrixElementR l2m m2l madd.
  Extraction "matrix.ml" MatrixElementR l2m m2l madd.

End MatrixTheory.

Module M := MatrixTheory MatrixElementR.
Recursive Extraction M.
Extraction "matrix.ml" M.
(* 仍然有问题，在 functor 内部抽取时，E 仍然是抽象的，没有转换到 float 类型，
   使得 l2m 等函数抽取出的代码Ocaml报错。 *)
  
?  

  (** ** Matrix theories -- Gauss elimination *)

  (* ======================================================================= *)
  (** ** 行变换的抽象表示 *)
  
  (* 为避免逆矩阵计算时的大量计算，使用抽象表示，可提高计算效率 *)
  Inductive RowOp :=
  | ROnop
  | ROswap (i j : nat)
  | ROscale (i : nat) (c : A)
  | ROadd (i j : nat) (c : A).

  (** 行交换：矩阵 M 的第 x, y 两行互换 *)
  Definition mrowSwap {n} (x y : nat) (M : smat n) : smat n :=
    f2m (fun i j => if i =? x then M y j else (if i ??= y then M x j else M i j)).

  Definition mrowScale {n} (x : nat) (c : A) (M : smat n) : smat n :=
    f2m (fun i j => if i ??= x then (c * M i j)%A else M i j).
  
  (* ? *)
  (* (** 行变换列表转换为矩阵 *) *)
  (* Definition rowOps2mat {n} (l : list RowOp)) : smat (S n) := *)
  (*   fold_right (fun op M => *)
  (*                match op with *)
  (*                | ROnop => M *)
  (*                | ROswap i j => mrowSwap i j M *)
  (*                | ROscale i c => mrowScale i c M *)
  (*                | ROadd i j c => mrowAdd i j c M *)
  (*                end) mat1 l. *)

  (* Check mmul. *)

  (** ** Extracted to OCaml *)
  Extraction mget.
  Extraction Implicit mget [r c]. ?
  Extraction mget.
  Recursive Extraction mtrans madd mmul.
  Recursive Extraction M.
  ?
  Extraction "matrix.ml" M.

End MatrixTheory.

(** * Experiment *)


(** ** Extracted to OCaml *)
Module test_Ocaml.
  Module Export M := MatrixTheory MatrixElementR.
  ?

  Recursive Extraction mtrans madd mmul.
  Recursive Extraction M.
  ?
  Extraction "matrix.ml" M.
  
End test_Ocaml.


(** ** Numerical computation in Coq *)
Module test_Qc.
  Module Export MatrixQc := MatrixTheory_NatFun MatrixElementQc.
  
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
    
    (* [0;1] 
       [2;3] *)
    Let M1 := @l2m 2 2 (Q2Qc_dlist [[0;1];[2;3]]%Q).
    (* [0;1]    [0;2]
       [2;3] => [1;3] *)
    Compute m2l (M1\T).
    (* [0;1]   [0;1]   [0;2]
       [2;3] + [2;3] = [4;6] *)
    Compute m2l (M1 + M1).
    (* [0;1]   [0;1]   [2;3]
       [2;3] * [2;3] = [6;11] *)
    Compute m2l (M1 * M1).
  End algebraic.
End test_Qc.


(** ** Symbolic computation and proof in Coq *)
Module test_R.
  Module Export MatrixR := MatrixTheory_NatFun MatrixElementR.
  Open Scope R.
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
    
    (* [0;1] 
       [2;3] *)
    Let M1 := @l2m 2 2 [[0;1];[2;3]].
    (* [0;1]    [0;2]
       [2;3] => [1;3] *)
    Compute m2l (M1\T).
    (* [0;1]   [0;1]   [0;2]
       [2;3] + [2;3] = [4;6] *)
    Compute m2l (M1 + M1).
    (* [0;1]   [0;1]   [2;3]
       [2;3] * [2;3] = [6;11] *)
    Compute m2l (M1 * M1).
  End algebraic.
  
End test_R.
