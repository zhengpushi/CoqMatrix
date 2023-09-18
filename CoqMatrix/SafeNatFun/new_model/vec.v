(* 
   purpose  : SafeNatFun model which build matrix with vector, not vector with matrix.
   author   : ZhengPu Shi
   date     : 2023.09.18

   remark   :
   1. This new model is a variant of "SafeNatFun" model, but with better 
      extensionality.
   2. If we build matrix from vector, then their have no differences for row/column 
      vectors, and the matrix is build row by rows.
 *)

Require Import Nat.
Require Import List.
Import ListNotations.
Require Import Equivalence.

Declare Scope T_scope.
Declare Scope vec_scope.
Declare Scope mat_scope.

Open Scope T_scope.
Open Scope vec_scope.

Reserved Infix    "=="      (at level 70, no associativity).      (* equiv *)
Reserved Infix    "==?"     (at level 65, no associativity).      (* decidable *)
Reserved Infix    "<>?"     (at level 65, no associativity).      (* decidable right *)
Reserved Notation "a != b"  (at level 70, no associativity).      (* not equiv *)
Reserved Infix    "=?"      (at level 70, no associativity).      (* bool equal *)
Reserved Notation "v ! i"      (at level 20, i at next level).    (* nth of vec *)
Reserved Notation "v $ i"      (at level 20, i at next level).    (* nth of vec, raw *)
Reserved Notation "m \T"    (at level 32, left associativity).    (* transpose *)

(* list of lists type *)
Definition dlist A := list (list A).


(** * Basic Library *)

(** Loop shift of natural number *)
Section nat_loop_shift.

  (** Left loop shift. n is modulo, i is given number, k is shift offset *)
  Definition nat_lshl (n : nat) (i : nat) (k : nat) : nat :=
    Nat.modulo (i + k) n.

  (** Right loop shift. n is modulo, i is given number, k is shift offset *)
  Definition nat_lshr (n : nat) (i : nat) (k : nat) : nat :=
    Nat.modulo (i + (n - (Nat.modulo k n))) n.

  Compute List.map (fun i => nat_lshl 5 i 1) (List.seq 0 10).
  Compute List.map (fun i => nat_lshr 5 i 1) (List.seq 0 10).

End nat_loop_shift.


(** * Vector and Matrix Libraries *)


(** ** Definition of Types *)
Section Types.
  Inductive vec {T} (n:nat) := vmake (f:nat -> T).

  Definition mat {T} r c := @vec (@vec T c) r.
  Definition smat {T} n := @mat T n n.

  (* Fetch out the function in a vector *)
  Definition vecf {T} {n} (v:@vec T n) : nat -> T :=
    let '(vmake _ f) := v in f.
  
End Types.

Arguments vmake {T n}.

Notation "v $ i" := (vecf v i) : vec_scope.


(** ** Operations on vectors *)
Section VecOp.

  (* Equality of two vectors *)
  Section veq.
    Context {T:Type} {Teq:T->T->Prop} {Equiv:Equivalence Teq} {Tzero:T}.
    Infix "==" := Teq : T_scope.

    Definition veq {n:nat} (v1 v2:vec n) : Prop := 
      forall i, i < n -> v1$i == v2$i.
    Infix "==" := veq : vec_scope.
  End veq.

  (* Safe access (any index is accepted, but we will use valid index only) *)
  Definition vnth {T} {T0:T} {n} (v:vec n) (i:nat) : T :=
    if (i <? n) then v$i else T0.
  Notation "v ! i " := (vnth v i) : vec_scope.

  (* list to vector. *)
  Definition l2v {T} (T0:T) n (l:list T) : vec n :=
    vmake (fun i => if i <? n then nth i l T0 else T0).
  
  (* vector to list *)
  Definition v2l {T} {n} (v:vec n) : list T :=
    map (fun i => v$i) (seq 0 n).

  (** Add an element in the head of a vector *)
  Definition vcons {T} {n} (t:T) (v:vec n) : vec (S n) :=
    vmake (fun i => match i with 0 => t | S i' => v$i' end).

  (** Get a vector from a given vector by remove one element *)
  Definition vremove {T} {n:nat} (v:@vec T (S n)) (k:nat) : vec (S n) :=
    vmake (fun i => if i <? k then v$i else v$(S i)).

  (* Compute v2l (vremove (l2v 0 3 [1;2;3]) 2). *)

  (* Mapping of a vector *)
  Definition vmap {T1 T2} {n} (f:T1 -> T2) (v:@vec T1 n) : @vec T2 n :=
    vmake (fun i => f (v$i)).
  
  (* Mapping of two vectors *)
  Definition vmap2 {T1 T2 T3} {n} (f:T1->T2->T3) (v1:@vec T1 n) (v2:@vec T2 n)
    : @vec T3 n :=
    vmake (fun i => f (v1$i) (v2$i)).

  (* Folding of a vector *)
  Fixpoint vfold_aux {T1 T2} {n} (v:nat ->T1) (f:T1->T2->T2) (b0:T2) : T2 :=
    match n with
    | O => b0
    | S n' => @vfold_aux _ _ n' v f (f (v n') b0)
    end.
  Definition vfold {T1 T2} {n} (v:@vec T1 n) (f:T1->T2->T2) (b0:T2) : T2 :=
    @vfold_aux T1 T2 n (vecf v) f b0.

  (* Compute vfold (@vmake _ 5 (fun i => i)) Nat.add 0. *)

  (* Vector algebra *)
  Section Alg.
    Context {T} {T0:T} {Tadd Tmul:T->T->T} {Topp:T->T}.
    Let Tsub a b := Tadd a (Topp b).

    Definition vec0 (n:nat) : vec n := vmake (fun _ => T0).

    Definition vadd {n} (v1 v2:vec n) : vec n := vmap2 Tadd v1 v2.
    Definition vopp {n} (v:vec n) : vec n := vmap Topp v.
    Definition vsub {n} (v1 v2:vec n) : vec n := vmap2 Tsub v1 v2.

    Definition vcmul {n} (t:T) (v:vec n) : vec n := vmap (fun x=>Tmul t x) v.
    Definition vmulc {n} (v:vec n) (t:T) : vec n := vmap (fun x=>Tmul x t) v.

    (* Dot production of two vectors. *)
    Definition vdot {n:nat} (v1 v2:vec n) : T :=
      vfold (vmap2 Tmul v1 v2) Tadd T0.

  End Alg.

End VecOp.

Section VecOp_test.
  
  Compute @vdot _ 0 Nat.add Nat.mul 3 (vmake (fun i => i)) (vmake (fun i => i+1)).
  
End VecOp_test.


(** ** Operations on matrices *)
Section MatOp.

  (* Equality of two matrixs *)
  Section meq.
    Context {T:Type} {Teq:T->T->Prop} {Equiv:Equivalence Teq} {Tzero:T}.
    Infix "==" := Teq : T_scope.
    Infix "==" := (veq (Teq:=Teq)) : vec_scope.

    Definition meq {r c:nat} (m1 m2:mat r c) : Prop :=
      @veq (@vec T c) (veq (Teq:=Teq)) r m1 m2.
    Infix "==" := meq : mat_scope.
  End meq.

  (* Safe access (any index is accepted, but we will use valid index only) *)
  Definition mnth {T} {T0:T} {r c} (m:mat r c) (i j:nat) : T :=
    vnth (vnth m i (T0:=vec0 c (T0:=T0))) j (T0:=T0).
  Notation "v ! i " := (vnth v i) : vec_scope.

  (* dlist to matrix. *)
  Definition l2m {T} (T0:T) r c (l:dlist T) : mat r c :=
    l2v (@vec0 T T0 c) r (map (l2v T0 c) l).
  
  (* matrix to dlist *)
  Definition m2l {T} {r c} (m:@mat T r c) : dlist T := map v2l (v2l m).

  (* Get a row which row index is k *)
  Definition mrow {T} {r c:nat} (m:@mat T r c) (k:nat) : vec c := m $ k.

  (* Get a column which column index is k *)
  Definition mcol {T} {r c:nat} (m:@mat T r c) (k:nat) : @vec T r :=
    vmake (fun i => m $ i $ k).

  (* Fetch out the function of a matrix *)
  Definition matf {T} {r c} (m:@mat T r c) : nat->nat->T := fun i j => vecf (vecf m i) j.

  (* Make a matrix from a function *)
  Definition mmake {T} {r c} (f:nat->nat->T) : mat r c := vmake (fun i => vmake (f i)).
  
  (* Left shift column.
     Eg: [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;0];[5;6;0];[8;9;0] *)
  Definition mcshl {T} {r c} (m:@mat T r c) (k:nat) : mat r c :=
    mmake (fun i j => m $ i $ (j + k)).

  (* Right shift column.
     [[1;2;3];[4;5;6];[7;8;9] ==1==> [[0;1;2];[0;4;5];[0;7;8] *)
  Definition mcshr {T} {T0:T} {r c} (m:@mat T r c) (k:nat) : mat r c :=
    mmake (fun i j => if j <? k then T0 else (m $ i $ (j - k))).

  (** Left loop shift column.
      [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;1];[5;6;4];[8;9;7] *)
  Definition mclshl {T} {r c} (m:@mat T r c) (k:nat) : mat r c :=
    mmake (fun i j => m $ i $ (nat_lshl c j k)).

  (** Right loop shift column *)
  Definition mclshr {T} {r c} (m:@mat T r c) (k:nat) : mat r c :=
    mmake (fun i j => m $ i $ (nat_lshr c j k)).

  (* Mapping of a matrix *)
  Definition mmap {T1 T2} {r c} (f:T1 -> T2) (m:@mat T1 r c) : @mat T2 r c :=
    vmap (vmap f) m.
  
  (* Mapping of two matrixs *)
  Definition mmap2 {T1 T2 T3} {r c} (f:T1->T2->T3) (m1:@mat T1 r c)
    (m2:@mat T2 r c) : @mat T3 r c := vmap2 (vmap2 f) m1 m2.

  Definition mtrans {T} {r c} (m:@mat T r c): mat c r := mmake (fun i j => m$j$i).
  Notation "m \T" := (mtrans m) : mat_scope.

  (** Construct a matrix with a vector and a matrix by row *)
  Definition mconsr {T} {r c} (v:@vec T c) (m:@mat T r c) : @mat T (S r) c :=
    mmake (fun i j => match i with O => v $ j | S i' => m $ i' $ j end).
  
  (** Construct a matrix with a vector and a matrix by column *)
  Definition mconsc {T} {r c} (v:@vec T r) (m:@mat T r c) : @mat T r (S c) :=
    mmake (fun i j => match j with O => v $ i | S j' => m $ i $ j' end).
  
  (* Matrix algebra *)
  Section Alg.
    Context {T} {T0 T1:T} {Tadd Tmul:T->T->T} {Topp:T->T}.
    Let Tsub a b := Tadd a (Topp b).

    Definition mat0 {T} {T0:T} (r c:nat) : mat r c := @vec0 _ (@vec0 _ T0 c) r.

    (* Identity matrix *)
    Definition mat1 (n:nat) : mat n n := mmake (fun i j => if (i =? j)%nat then T1 else T0).

    Definition madd {r c} (m1 m2:mat r c) : mat r c := mmap2 Tadd m1 m2.
    Definition mopp {r c} (m:mat r c) : mat r c := mmap Topp m.
    Definition msub {r c} (m1 m2:mat r c) : mat r c := mmap2 Tsub m1 m2.

    Definition mcmul {r c} (t:T) (m:mat r c) : mat r c := mmap (fun x=>Tmul t x) m.
    Definition mmulc {r c} (m:mat r c) (t:T) : mat r c := mmap (fun x=>Tmul x t) m.

    (* Matrix multiplication *)
    Definition mmul {r c s:nat} (m1:@mat T r s) (m2:@mat T s c) : @mat T r c :=
      let vdot := @vdot T T0 Tadd Tmul s in
      mmake (fun i j => vdot (m1$i) ((mtrans m2)$j)).
  End Alg.

End MatOp.

Section MatOp_test.
  Let m1 : mat 2 3 := l2m 0 2 3 [[1;2;3];[4;5;6]].
  Compute v2l (mrow m1 2).
  Compute v2l (mcol m1 3).
  Let v1 : vec 3 := l2v 0 3 [7;8;9].
  Let v2 : vec 2 := l2v 0 2 [10;11].

  Compute m2l (mconsr v1 m1).
  Compute m2l (mconsc v2 m1).
  
End MatOp_test.
