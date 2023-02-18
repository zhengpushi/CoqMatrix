(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Inversion of square matrix
  author    : ZhengPu Shi
  date      : 2022.08
  
  remark    :
  1. There are three methods to compute the determinant,
     ref: https://zhuanlan.zhihu.com/p/435900775
     a. expand by row or column, then compute it with the algebraic remainder (代数
        余子式) 。Each expansion corresponds to a drop of one order.
        Note: expanding by rows/columns is a special case of Laplace's expansion 
        theorem.
     b. using primitive transformations (初等变换).
     c. with the help of inverse ordinal (逆序数) and permutation, i.e., by the 
        definition.
  2. Test the performance of inversion algorithm here which is an OCaml program 
     extracted from Coq.

     Test result:
          n=8, 1.1s;  n=9, 12s;  n=10, 120s

     Main issue:
     a. observed that, the CPU usage is too high, but memory usage is low.
     b. maybe caused by the index of nat type, and I think that int type should 
        better. So, maybe we need to write an implementation in OCaml directly.
     c. another reason is that the recursion of det function is too much.

     So, we should write several version in OCaml, to check which one resulting the 
     bad performane.
     a. version1, still use NatFun, but with index of int type.
     b. version2, use array
     c. version3, use matrix (bigarray)

     New test result:
     a. version1,
        n=8, 0.25s;  n=9, 2.4s;  n=10, 32s
        I think it is still slow, maybe causing by functional style
     b. version2,
        n=8, 1s;  n=9,7s; n=10, not tested yet
        This version is slower than original one, although we have used
        array structure, why? maybe too much foo loop? I'm not sure.
 *)


Require Import StrExt.

Require Export MatrixTheoryNF.

Open Scope nat_scope.
Open Scope A_scope.
Open Scope mat_scope.


(* ######################################################################### *)
(** * Properties of list *)

(** fold_left of list nat and add operation with different initial value *)
Lemma fold_left_nat_initial : forall (l : list nat) n,
    fold_left add l n = fold_left add l 0 + n.
Proof.
  induction l; intros; auto.
  simpl. rewrite IHl. rewrite (IHl a). lia.
Qed.

(** Length of concat operation *)
Lemma concat_length : forall A (l : list (list A)),
    length (concat l) = fold_left add (map (@length A) l) 0.
Proof.
  intros A l.
  induction l; simpl; auto.
  rewrite app_length. rewrite IHl. rewrite (fold_left_nat_initial _ (length a)).
  lia.
Qed.


(* ######################################################################### *)
(** * General tactics *)

(** Convert list equality to element equality *)
Ltac tac_listeq :=
  repeat match goal with
    | |- cons ?x1 ?l1 = cons ?x2 ?l2 => f_equal
    end.


(* ######################################################################### *)
(** * Full permutation (abbreviated as permutation) *)

Section perm.
  Context {A : Type} (A0 : A).
  
  (** Get k-th element and remaining elements from a list *)
  Fixpoint pick (l : list A) (k : nat) : A * list A :=
    match k with
    | 0 => (hd A0 l, tl l)
    | S k' =>
        match l with
        | [] => (A0, [])
        | x :: l' =>
            let (a,l0) := pick l' k' in
            (a, [x] ++ l0)
        end
    end.

  (** Auxiliary function for get permutation of a list *)
  Fixpoint perm_aux (n : nat) (l : list A) : list (list A) :=
    match n with
    | 0 => [[]]
    | S n' =>
        let d1 := map (fun i => pick l i) (seq 0 n) in
        let d2 :=
          map (fun k : A * list A =>
                 let (x, lx) := k in
                 let d3 := perm_aux n' lx in
                 map (fun l1 => [x] ++ l1) d3) d1 in
        concat d2
    end.

  (** Get permutation of a list *)
  Definition perm (l : list A) : list (list A) :=
    perm_aux (length l) l.

  (** Length of permutation *)
  Definition Pn (l : list A) := length (perm l).

  (** Pn of cons. 
      Example: Pn [a;b;c;d] = 4 * Pn [a;b;c] *)
  Lemma Pn_cons : forall (a : A) (l : list A), Pn (a :: l) = (length (a :: l)) * (Pn l).
  Proof.
    intros. simpl. unfold Pn.
    unfold perm. simpl. rewrite app_length. rewrite map_length. f_equal.
    rewrite map_map.
    rewrite concat_length.
    rewrite map_map.
    Admitted.

  (** Length of permutation equal to the factorial of the length *)
  Lemma Pn_eq : forall l, Pn l = fact (length l).
  Proof.
    induction l; simpl; auto.
    rewrite Pn_cons. rewrite IHl. simpl. auto.
  Qed.
  
End perm.

(* Compute perm 0 [1;2]. *)
(* Compute perm 0 [1;2;3]. *)
(* Compute perm 0 [1;2;3;4]. *)

(* Example l1 := [1;2;3;4]. *)
(* Compute Pn _ l1. *)
(* Compute fact (length l1). *)



(* ######################################################################### *)
(** * Inversion of square matrix *)
Module Inversion (E : DecidableFieldElementType).
  Export E.
  Module Export M := DecidableFieldMatrixTheoryNF E.

  Add Field field_inst : make_field_theory.

  (** Squaqre matrix *)
  Definition smat (n : nat) := mat n n.
  
  (* ======================================================================= *)
  (** ** Determinant. *)

  (** Get the sub square matrix which remove r-th row and c-th column
    from a square matrix. *)
  Definition submat {n} (m : smat (S n)) (r c : nat) : smat n :=
    fun i j =>
      let i' := (if ltb i r then i else S i) in
      let j' := (if ltb j c then j else S j) in
      m i' j'.
  
  (** Determinant *)
  (* Original verion *)
  (* Fixpoint det {n} : smat n -> A := *)
  (*   match n with *)
  (*   | 0 => fun _ => A1 *)
  (*   | S n' => *)
  (*       fun m => *)
  (*         fold_left Aadd (map (fun i => *)
  (*                                let s := if Nat.even i then A1 else (-A1)%A in *)
  (*                                let a := m 0 i in *)
  (*                                let d := det (submat m 0 i) in *)
  (*                                (s * a * d)%A) (seq 0 n)) A0 *)
  (*   end. *)
  
  (* Modified version, don't use local variable s *)
  Fixpoint det {n} : smat n -> A :=
    match n with
    | 0 => fun _ => A1
    | S n' =>
        fun m =>
          fold_left Aadd
            (map (fun i =>
                    let a := if Nat.even i then (m 0 i)%nat else (-(m 0 i)%nat)%A in
                    let d := det (submat m 0 i) in
                    (a * d)%A) (seq 0 n)) A0
    end.
  
  (** Verify formula for determinant of specify matrix *)
  Lemma det_1_1 : forall a, (det (mk_mat_1_1 a) == a)%A.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Lemma det_2_2 : forall a11 a12 a21 a22, 
      (det (mk_mat_2_2 a11 a12 a21 a22) == (a11 * a22 - a12 * a21))%A.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Lemma det_3_3 : forall a11 a12 a13 a21 a22 a23 a31 a32 a33, 
      (det (mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33) == 
        (a11*a22*a33 - a11*a23*a32 - 
           a12*a21*a33 + a12*a23*a31 + 
           a13*a21*a32 - a13*a22*a31))%A.
  Proof.
    intros. cbv. ring.
  Qed.
  
  (* ======================================================================= *)
  (** ** Cramer rule *)
  
  (** Exchange one column of a square matrix *)
  Definition mchgcol {n} (m : smat n) (k : nat) (v : mat n 1) : smat n :=
    fun i j => if (Nat.eqb j k) then (v i 0)%nat else m i j.
  
  (** Cramer rule, which can slving the equation with form of A*x=b.
      Note, the result is valid on when D is not zero *)
  Definition cramerRule {n} (A : smat n) (b : mat n 1) : mat n 1 :=
    let D := det A in
    (fun i j => let Di := det (mchgcol A i b) in Di / D).
  
  
  (* ======================================================================= *)
  (** ** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  (** That is: adj(A)[i,j] = algebraic remainder of A[j,i]. *)
  
  Definition madj {n} : smat n -> smat n := 
    match n with
    | O => fun m => m 
    | S n' =>
        fun m =>
        fun i j =>
          let s := if Nat.even (i + j) then A1 else (-A1)%A in
          let d := det (submat m j i) in 
          (s * d)%A
    end.
  
  
  (* ======================================================================= *)
  (** ** Inversion matrix of a matrix *)
  Definition minv {n} (m : smat n) := @mcmul n n (A1/det m) (madj m).
  
  (** Verify formula for inversion of specify matrix *)
  Lemma inv_1_1 : forall a, ~(a == A0)%A -> (m2l (minv (mk_mat_1_1 a)) == [[A1/a]])%dlist.
  Proof.
    intros. cbv. constructor; auto. constructor; auto.
    field. auto. 
  Qed.
  
  Lemma inv_2_2 : forall a11 a12 a21 a22 : A, 
      let d := (a11 * a22 - a12 * a21)%A in
      ~(d == A0)%A ->
      (m2l (minv (mk_mat_2_2 a11 a12 a21 a22)) ==
        ([[a22/d; -a12/d]; [-a21/d; a11/d]])%A)%dlist.
  Proof.
    intros. cbv.
    repeat constructor; auto; try field; auto.
  Qed.
  
  (* Note, this formula could be provided from matlab, thus avoiding manually *)
  Lemma inv_3_3 : forall a11 a12 a13 a21 a22 a23 a31 a32 a33, 
      let d := (a11*a22*a33 - a11*a23*a32 - a12*a21*a33 + 
                  a12*a23*a31 + a13*a21*a32 - a13*a22*a31)%A in
      ~(d == A0)%A ->
      (m2l (minv (mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33)) ==
        ([[(a22*a33 - a23*a32)/d; -(a12*a33 - a13*a32)/d; (a12*a23 - a13*a22)/d];
          [-(a21*a33 - a23*a31)/d; (a11*a33 - a13*a31)/d; -(a11*a23 - a13*a21)/d];
          [(a21*a32 - a22*a31)/d; -(a11*a32 - a12*a31)/d; (a11*a22 - a12*a21)/d]
        ])%A)%dlist.
  Proof.
    intros. cbv.
    repeat constructor; auto; try field; auto.
  Qed.
  
  (** Direct compute inversion of a symbol matrix of 1/2/3rd order. *)
  Section FindFormula.
    Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.
    Let m1 := mk_mat_1_1 a11.
    Let m2 := mk_mat_2_2 a11 a12 a21 a22.
    Let m3 := mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.
    
    (* Although this is correct, but the expression is too long.
       We will simplify it with RAST *)
    (* Compute (m2l (minv m1)). *)
    (* Compute (m2l (minv m2)). *)
    (* Compute (m2l (minv m3)). *)
    
  End FindFormula.

End Inversion.


(** Test for Inversion *)
Module Test_for_Inversion.

  Import QArith.
  Module Import InversionQ := Inversion DecidableFieldElementTypeQ.
  Open Scope Q.
  
  (* Symbols *)
  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : Q.
  Variable b1 b2 b3 : Q.
  
  (* Number/Symbol matrix of 2x2 *)
  Definition m20 := mk_mat_2_2 1 2 3 4.
  Definition m21 := mk_mat_2_2 a11 a12 a21 a22.
  
  (* Number/Symbol matrix of 3x3 *)
  Definition m30 := mk_mat_3_3 1 2 3 4 5 6 7 8 10.
  Definition m30_1 := mk_mat_3_3
                        1.25 3.47 4.86
                        8.12 9.85 12.34
                        21.34 0.73 2.35.
  Definition m31 := mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.
  
  (* Remainder (余子式) *)
  (* Compute (m2l (submat m30 0 1)). *)
  (* Compute (m2l (submat m31 2 1)). *)
  
  (* Determinant *)
  (* Compute det m20. *)
  (* Compute det m30. *)
  (* Eval cbn in det m21. *)
  (* Eval cbn in det m31. *)
  
  (* Cramer rule *)
  Definition v31 := mk_mat_3_1 b1 b2 b3.
  (* Compute (m2l m30). *)
  (* Compute (m2l (mchgcol m30 2 v31)). *)
  (* Eval cbn in det (mchgcol m30 2 v31). *)
  (* Eval cbn in cramerRule m30 v31. *)
  
  (* Adj *)
  (* Compute (m2l (madj m20)). *)
  (* Compute (m2l (madj m30)). (* too slow *) *)
  
  (* Inverse matrix *)
  Compute (m2l (minv m20)).
  Compute (m2l (minv m30)).
  Compute (m2l (minv m30_1)).
  (* matlab answer of "inv m30" is:
   -0.1109    0.0361    0.0396
   -1.9153    0.7902   -0.1885
    1.6018   -0.5735    0.1244
    our answer is corect too.
   *)
  
  Eval cbn in (m2l (minv m21)).
  Eval cbn in (m2l (minv m31)).
  
End Test_for_Inversion.


(** 同济大学，线性代数（第五版），page25, 习题一 *)
(** 数值矩阵部分，使用特定的域会便于计算，但涉及到符号时，会展开为复杂的表达式，
不便于符号矩阵的证明 *)
Module Exercise_Ch1_Number.

  (* 用Qc来测试，比较直观 *)
  Import QArith Qcanon.
  Module Import InversionQc := Inversion FieldQc.FieldDefQc.
  Open Scope Q.
  Open Scope Qc_scope.

  Coercion Q2Qc : Q >-> Qc.
  
  
  (** 同济大学，线性代数（第五版），page22, 例14 *)
  Section example14.
    Let D := mk_mat_4_4 
               2 1 (-5) 1
               1 (-3) 0 (-6)
               0 2 (-1) 2
               1 4 (-7) 6.
    Let b := mk_mat_4_1 8 9 (-5) 0.
    
    (*     Compute (m2l (cramerRule D b)). *)
  End example14.
  
  Section example15.
    Let D := mk_mat_4_4 
               1 1 1 1
               1 2 4 8
               1 3 9 27
               1 4 16 64.
    Let b := mk_mat_4_1 3 4 3 (-3).
    
    (*     Compute (m2l (cramerRule D b)). *)
  End example15.

  (** ex1 *)
  Section ex_1.
    (*     Compute (det (mk_mat_3_3 2 0 1 1 (-4) (-1) (-1) 8 3)). *)

    Variable a b c : Qc.
    (*     Eval cbn in det (mk_mat_3_3 a b c b c a c a b). *)
    (* ToDo: 不在证明模式时，如何利用Coq环境化简上述表达式？ *)
  End ex_1.
End Exercise_Ch1_Number.


(** 符号矩阵部分，在符号这一级方便证明 *)
Module Exercise_Ch1_Symbol.

  Declare Module F : FieldSig.
  Module Import InversionInst := Inversion F.
  
  Notation "2" := (1 + 1)%A.
  Notation "3" := (1 + 2)%A.
  
  (* A上的幂函数 *)
  Fixpoint Apow (a : A) (n : nat) :=
    match n with
    | 0 => A1
    | S n' => (a * (Apow a n'))%A
    end.
  Infix "^" := (Apow).
  
  Example ex6_1 : forall a b : A,
      let m := (mk_mat_3_3 (a*a) (a*b) (b*b) (2*a) (a+b) (2*b) 1 1 1)%A in
      det m = (a - b)^3.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Example ex6_2 : forall a b x y z : A,
      let m1 := (mk_mat_3_3
                   (a*x+b*y) (a*y+b*z) (a*z+b*x)
                   (a*y+b*z) (a*z+b*x) (a*x+b*y)
                   (a*z+b*x) (a*x+b*y) (a*y+b*z))%A in
      let m2 := mk_mat_3_3 x y z y z x z x y in
      det m1 = ((a^3 + b^3) * det m2)%A.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Example ex6_3 : forall a b e d : A,
      let m := (mk_mat_4_4
                  (a*a) ((a+1)^2) ((a+2)^2) ((a+3)^2)
                  (b*b) ((b+1)^2) ((b+2)^2) ((b+3)^2)
                  (e*e) ((e+1)^2) ((e+2)^2) ((e+3)^2)
                  (d*d) ((d+1)^2) ((d+2)^2) ((d+3)^2))%A in
      det m = 0.
  Proof.
    intros. cbv. ring.
  Qed.
  
  Example ex6_4 : forall a b e d : A,
      let m := (mk_mat_4_4
                  1 1 1 1
                  a b e d
                  (a^2) (b^2) (e^2) (d^2)
                  (a^4) (b^4) (e^4) (d^4))%A in
      det m = ((a-b)*(a-e)*(a-d)*(b-e)*(b-d)*(e-d)*(a+b+e+d))%A.
  Proof.
    intros. cbv. ring.
  Qed.
  
  (** 6.(5) 是无穷的，需要更多构造和证明，待以后补充 *)

End Exercise_Ch1_Symbol.

(** 使用实数的AST，看能否得到简化的逆矩阵表达式 *)
Module Simplify_by_RAST.
  
  Import RAST.
  Module Import InversionInst := Inversion FieldT.FieldDefT.
  
  Notation "0" := T0.
  Notation "1" := T1.
  Notation "2" := (1 + 1)%A.
  Notation "3" := (1 + 2)%A.
  Infix "+" := Tadd.
  Infix "-" := Tsub.
  Infix "*" := Tmul.
  
  (* simp 函数可以化简一个项，我们需要对 list 和 list list 进行化简 *)
  
  (** list (list T) 的化简 *)
  Definition dl_nsimp (dl : list (list T)) (n : nat) :=
    map (map (fun t => nsimp t n)) dl.
  
  (** list (list T) 上的 AST -> R 的转换 *)
  Definition dl_T2R (dl : list (list T)) : list (list R) :=
    map (map T2R) dl.
  
  (* 以计算 1/2/3阶符号矩阵的逆矩阵为例，测试 RAST 的化简效果 *)
  
  (* 第一版，大概测试一下 *)
  Section TestV1.
    (* 定义多个变量 *)
    Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.
    
    (* 构造1/2/3阶矩阵 *)
    Let m1 := mk_mat_1_1 a11.
    Let m2 := mk_mat_2_2 a11 a12 a21 a22.
    Let m3 := mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.

    (* 计算逆矩阵 *)
    Let l1 := Eval cbv in m2l (minv m1).
    Let l2 := Eval cbv in m2l (minv m2).
    Let l3 := Eval cbv in m2l (minv m3).
    
    (* 可以看到，结果确实有冗余 *)
  (*     Print l1.   (* [[(1 * (/ (0 + (a11 * 1)))) * (1 * 1)]] *)
    Print l2.
    Print l3. *)
    
    (* 可以看到，simp有一定的效果，但还不彻底，需要更强的 simp *)
    (*     Compute dl_nsimp l1 10. (* [[(/ (0 + (a11 * 1)))%T]] *) *)
    
  (* 再看 AST -> R 之后的结果，看到有未展开的函数抽象，可能与 a11 的定义方式
      有关。下一节准备用 TLit (r : R) 来构造，再次测试 *)
    (*     Compute T2R ((/ (0 + (a11 * 1)))%T). *)
  End TestV1.
  
  (** 第2版，改用 TLit (r : R) 来定义变量 *)
  Section TestV2.
    Open Scope R.
    Variable r11 r12 r13 r21 r22 r23 r31 r32 r33 : R.
    Let a11 := TLit r11. Let a12 := TLit r12. Let a13 := TLit r13.
    Let a21 := TLit r21. Let a22 := TLit r22. Let a23 := TLit r23.
    Let a31 := TLit r31. Let a32 := TLit r32. Let a33 := TLit r33.
    
    Let m1 := mk_mat_1_1 a11.
    Let m2 := mk_mat_2_2 a11 a12 a21 a22.
    Let m3 := mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33.

    (* 行列式表达式 *)
    (*     Compute T2R (nsimp (det m1) 10).  (* = r11 *)
    Compute T2R (nsimp (det m2) 10).  (* = (r11 * r22 + - r12 * r21)%R *)
    
    Compute (det m3).
    Compute T2R (det m3).
    Compute T2R (nsimp (det m3) 30).  (*
      r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + 
      - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31 *)
     *)    
    (* 逆矩阵表达式 *)
    Let l1 := Eval cbv in m2l (minv m1).
    Let l2 := Eval cbv in m2l (minv m2).
    Let l3 := Eval cbv in m2l (minv m3).
    (*     Compute l1. (* [[1 * / (0 + TLit r11 * 1) * (1 * 1)]] *)
    Compute dl_nsimp l1 10. (* [[(/ TLit r11)%T]] *)
    Compute T2R (/ TLit r11)%T. (* (/ r11)%R *)
    Compute dl_T2R (dl_nsimp l1 10). (*
      = [[(/ r11)%R]] *) *)
    
    (*     Compute l2.
    Compute dl_nsimp l2 20.
    Compute dl_T2R (dl_nsimp l2 20). (*
    = [[/ (r11 * r22 + - r12 * r21) * r22; - / (r11 * r22 + - r12 * r21) * r12];
       [- / (r11 * r22 + - r12 * r21) * r21; / (r11 * r22 + - r12 * r21) * r11]]
     *) *)
    
    (*     Compute dl_T2R (dl_nsimp l3 50). (* *)
      = [[/ (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r22 * r33 +
         / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r23 * r32;
        - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r12 * r33 +
        - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r13 * r32;
        / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r12 * r23 +
        / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r13 * r22];
       [- / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r21 * r33 +
        - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r23 * r31;
       / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r11 * r33 +
       / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r13 * r31;
       - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r11 * r23 +
       - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r13 * r21];
       [/ (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r21 * r32 +
        / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r22 * r31;
       - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r11 * r32 +
       - / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r12 * r31;
       / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r11 * r22 +
       / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r12 * r21]]
     : list (list R)
     *)
    (* 基本上得到与 Matlab一样的结果 *)
    
    (* 以第一项为例，可以得到证明 *)
    
    (* 先给出3x3矩阵行列式的表达式 *)
    Let det_m3_exp := r11*r22*r33 - r11*r23*r32 - r12*r21*r33 +
                        r12*r23*r31 + r13*r21*r32 - r13*r22*r31.
    
    (* 再证明该表达式确实等于行列式 *)
    Let det_m3_exp_ok : det_m3_exp = T2R (det m3).
    Proof.
      cbv. ring.
    Qed.
    
    (* 证明逆矩阵第一项，确实等于 Matlab 给出的那个结果 *)
    Let inv_a11_ok : T2R (det m3) <> 0 -> 
                     / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * r22 * r33 +
                       / (r11 * r22 * r33 + r11 * - r23 * r32 + - r12 * r21 * r33 + - r12 * - r23 * r31 + r13 * r21 * r32 + r13 * - r22 * r31) * - r23 * r32 
                     = (r22*r33 - r23*r32)/(r11*r22*r33 - r11*r23*r32 - r12*r21*r33 + r12*r23*r31 + r13*r21*r32 - r13*r22*r31).
    Proof.
      clear l1 l2 l3. intros. field.
      rewrite <- det_m3_exp_ok in H. auto.
    Qed.
    
  End TestV2.
  
  (** 任意纬度的测试，自动构造变量 *)
  Module TestV3_any_dim.
    
    Open Scope nat.

    (** 从 "a" 2 3 到 "a23" *)
    Definition nn2s (prefix:string) (i j:nat) : string :=
      (prefix ++ (nat2str i) ++ (nat2str j))%string.
    
    (** 构造矩阵需要的所有字符串变量 *)
    Definition mat_vars_s (r c:nat) : list (list string) :=
      map (fun i => map (nn2s "a" i) (seq 0 c)) (seq 0 r).
    
    (*     Compute mat_vars_s 3 4. *)
    
    (** 虚拟的环境，可以将 string 映射到 R *)
    Variable env_s2T : string -> T.
    
    Coercion env_s2T : string >-> T.
    
    (*     Check nth 0 (mat_vars_s 3 4).
    Check nth 0 (nth 0 (mat_vars_s 3 4) []) "".
    Compute nth 0 (nth 0 (mat_vars_s 3 4) []) "".
     *)    
    (** 矩阵的生成函数 *)
    Definition g' r c : MATData T := fun i j =>
                                       env_s2T (nth j (nth i (mat_vars_s r c) []) "").
    
    (* 当 200x200 规模时，计算一个元素，约 0.5 s *)
    (*     Time Compute g' 200 200 5 6. *)
    
    (* 手动设定阶数，行数、列数都等于它 *)
    Definition ORDERS := 6.
    Definition ROWS := ORDERS.
    Definition COLS := ORDERS.
    
    (* 事先算好字符串，节省时间。当100x100规模时，约 2.5s *) 
    Definition mat_vars_given := Eval cbv in (mat_vars_s ROWS COLS).

    (*     Print mat_vars_given. *)
    
    Definition g : MATData T := fun i j =>
                                  env_s2T (nth j (nth i mat_vars_given []) "").
    
    (* 此时，取出元素速度较快 *)
    (*     Compute g 1 9. *)
    
    Definition m := mk_mat ROWS COLS g.
    
    (*     Time Compute minv m. *)
    (*     Time Compute (m2l (minv m)). *)
  (*     Time Definition m' := Eval cbv in (minv m).
    Time Definition dl := Eval cbv in (m2l m').
    Time Definition dl1 := Eval cbv in (dl_nsimp dl 2).
    
    Check dl1.
    Check (hd [] dl1).
    Check (hd T0 (hd [] dl1)).
    Compute (hd T0 (hd [] dl1)).
    Compute (hd T0 (hd [] (dl_nsimp dl 3))).
    Let t1 := Eval cbv in (hd T0 (hd [] (dl_nsimp dl 0))).
    Print t1. *)
  (* 注意，这里继续优化反而有问题，因为 nsimp 为是 TLit 而写的，
    这里的类型可能不适合 *)
    
    (* 重新写一版，针对 TLit 的*)
    
  End TestV3_any_dim.
  
  (* 几乎与 TestV3_any_dim 一样，只不过使用 TLit *)
  Module TestV4_any_dim_TLit.
    
    Open Scope nat.

    (** 从 "a" 2 3 到 "a23" *)
    Definition nn2s (prefix:string) (i j:nat) : string :=
      (prefix ++ (nat2str i) ++ (nat2str j))%string.
    
    (** 构造矩阵需要的所有字符串变量 *)
    Definition mat_vars_s (r c:nat) : list (list string) :=
      map (fun i => map (nn2s "a" i) (seq 0 c)) (seq 0 r).
    
    (*     Compute mat_vars_s 3 4. *)
    
    (** 虚拟的环境，可以将 string 映射到 R *)
    Variable env_s2R : string -> R.
    
    Coercion env_s2R : string >-> R.
    
    (*     Check nth 0 (mat_vars_s 3 4).
    Check nth 0 (nth 0 (mat_vars_s 3 4) []) "".
    Compute nth 0 (nth 0 (mat_vars_s 3 4) []) "". *)
    
    (** 矩阵的生成函数 *)
    Definition g' r c : MATData T :=
      fun i j => (TLit (env_s2R (nth j (nth i (mat_vars_s r c) []) ""))).
    
    Coercion TLit : R >-> T.
    
    (* 当 200x200 规模时，计算一个元素，约 0.5 s *)
    (*     Time Compute g' 200 200 5 6. *)
    
    (* 手动设定阶数，行数、列数都等于它 *)
    Definition ORDERS := 6.
    Definition ROWS := ORDERS.
    Definition COLS := ORDERS.
    
    (* 事先算好字符串，节省时间。当100x100规模时，约 2.5s *) 
    Definition mat_vars_given := Eval cbv in (mat_vars_s ROWS COLS).

    (*     Print mat_vars_given. *)
    
    Definition g : MATData T :=
      fun i j => (TLit (env_s2R (nth j (nth i mat_vars_given []) ""))).
    
    (* 此时，取出元素速度较快 *)
    (*     Compute g 1 9. *)
    
    Definition m := mk_mat ROWS COLS g.
    
    (*     Time Compute minv m. *)
    (*     Time Compute (m2l (minv m)). *)
  (*     Time Definition m' := Eval cbv in (minv m).
    Time Definition dl := Eval cbv in (m2l m').
    Time Definition dl1 := Eval cbv in (dl_nsimp dl 2). *)
    
  (*     Check dl1.
    Check (hd [] dl1).
    Check (hd T0 (hd [] dl1)).
    Compute (hd T0 (hd [] dl1)).
    Compute (hd T0 (hd [] (dl_nsimp dl 3))).
    Let t1 := Eval cbv in (hd T0 (hd [] (dl_nsimp dl 0))).
    Print t1.
    Let t2 := Eval cbv in (hd T0 (hd [] (dl_nsimp dl 5))).
    Print t2. *)
  (* 还是不行，越优化效果越差。
    下次，从 4 阶开始查 优化算法。*)
    
  End TestV4_any_dim_TLit.

End Simplify_by_RAST.


