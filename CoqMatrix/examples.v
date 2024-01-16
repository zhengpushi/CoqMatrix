(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Examples for usage of CoqMatrix library.
  author    : ZhengPu Shi
  date      : 2023.01
*)

From CoqMatrix Require MatrixAll VectorAll.
From CoqMatrix Require MatrixNat MatrixZ MatrixQ MatrixQc MatrixR VectorR.


(** * Matrix over natural numbers *)
Module Example4Nat.

  Import MatrixNat.

  (** Then, all functions, theorems, notations are available *)
  Example dl := [[1;2;3];[4;5;6]].
  Example m1 : mat 2 3 := @l2m 2 3 dl.
  (* Compute (m2l m1). (* = [[1; 2; 3]; [4; 5; 6]] : list (list A) *) *)
  (* Compute (mnth m1 0 1). (* = 2 : A *) *)
  (* Compute (m2l (m1\T)). (* = [[1; 4]; [2; 5]; [3; 6]] : list (list A) *) *)
  Goal mmap S m1 == l2m [[2;3;4];[5;6;7]].
  Proof. lma. Qed.

  (** Check that if A is nat really *)
  (* Print A. (* A = nat : Type *) *)

  (** You can mixed use all models *)
  Import MatrixAllNat. (* all models *)
  (* Compute @DL.l2m 2 3 dl. *)
  (* Compute @DP.l2m 2 3 dl. *)
  (* Compute @DR.l2m 2 3 dl. *)
  (* Compute @NF.l2m 2 3 dl. *)
  
End Example4Nat.


(** * Matrix over rational numbers *)

Module Example4Q.

  Import MatrixQ.
  Import FuncExt.

  (** Q is setoid equal, not leibniz equal *)
  Goal 6/4 <> 1.5. Proof. easy. Qed.
  Goal (6/4 == 1.5)%Q. Proof. easy. Qed.

  (** We can then see that our matrix theory works well for elements of rational 
      type due to its support for setoid equality. *)
  Example m1 : mat 2 3 := l2m [[6/4;10/4;7/2];[4;5;6]].
  Example m2 : mat 2 3 := l2m [[1.5;2.5;3.5];[4;5;6]].
  Example eq0 : m1 <> m2.
  Proof.
    cbv. intro H. inv H.
    (* convert "λx.f x = λy.g y" to "∀x.(f x=g x)" *)
    rewrite fun_eq_iff_forall_eq2 in H1.
    specialize (H1 0 0)%nat. simpl in H1. easy.
  Qed.
  
  Example eq1 : m1 == m2. Proof. lma. Qed.

  (** Proof by ltac or by using properties *)
  Definition mat1 {n} := mat1 n.
  Goal m1 * mat1 == m2. Proof. lma. Qed.
  Goal m1 * mat1 == m2. Proof. rewrite mmul_1_r. apply eq1. Qed.
  
End Example4Q.


Module Example4R.
  
  Import MatrixR.

  Goal forall r s t (m1 : mat r s) (m2 : mat s t) (c : R),
      (c c* m1) * m2 == m1 * (c c* m2).
  Proof.
    intros.
    rewrite <- mcmul_mul_assoc.
    rewrite <- mcmul_mul_perm.
    easy.
  Qed.

End Example4R.



(** * Mutual conversion and mixed use between multiple models *)
Module Example4Cvt.
  
  (** Import library needed to use *)
  Import MatrixZ MatrixAllZ.
  Import Coq.Vectors.Vector VectorNotations.
  (* Import Coq.Vectors.Vector VectorNotations. (* notations for Coq.Vector *) *)
  (* Open Scope Z. *)
  (* Open Scope mat_scope. *)

  (** convert from one model to other models *)
  Example m : NF.mat 2 2 := NF.mk_mat_2_2 1 2 3 4.
  (* Compute nf2dl m. (* = [[1; 2]; [3; 4]]%vector : DL.mat 2 2 *) *)
  (* Compute nf2dp m. (* = (1, (2, tt), (3, (4, tt), tt)) : DP.mat 2 2 *) *)
  (* Compute nf2dr m. (* = {| mdata := [[1;2];[3;4]]; .. |} : DR.mat 2 2 *) *)
  
  (* Note!! next evaluation on FF is crashed! *)
  (* Compute nf2ff m. *)
  
  (** prove that {SF -> DL -> DP -> DR -> NF -> SF} return back *)
  Goal forall r c (m1 : SF.mat r c),
    let m2 : DL.mat r c := sf2dl m1 in
    let m3 : DP.mat r c := dl2dp m2 in
    let m4 : DR.mat r c := dp2dr m3 in
    let m5 : NF.mat r c := dr2nf m4 in
    let m6 : SF.mat r c := nf2sf m5 in
    m6 == m1.
  Proof.
    intros. unfold m6,m5,m4,m3,m2,dl2dp,dp2dr,dr2nf,nf2sf,sf2dl.
    rewrite DR.m2l_l2m_id; auto with mat.
    rewrite DL.m2l_l2m_id; auto with mat.
    rewrite NF.m2l_l2m_id; auto with mat.
    rewrite DP.m2l_l2m_id; auto with mat.
    rewrite SF.l2m_m2l_id; auto with mat.
    reflexivity.
  Qed.
  
End Example4Cvt.

Module Example4CoordinateSystem.
  
  Import MatrixR.
  Open Scope R.
  
  Variable ψ θ φ: R.
  Let Rx := mk_mat_3_3 1 0 0 0 (cos φ) (sin φ) 0 (-sin φ) (cos φ).
  Let Ry := mk_mat_3_3 (cos θ) 0 (-sin θ) 0 1 0 (sin θ) 0 (cos θ).
  Let Rz := mk_mat_3_3 (cos ψ) (sin ψ) 0 (-sin ψ) (cos ψ) 0 0 0 1.
  Let Rbe := mk_mat_3_3
    (cos θ * cos ψ) (cos ψ * sin θ * sin φ - sin ψ * cos φ)
    (cos ψ * sin θ * cos φ + sin φ * sin ψ) (cos θ * sin ψ)
    (sin ψ * sin θ * sin φ + cos ψ * cos φ)
    (sin ψ * sin θ * cos φ - cos ψ * sin φ)
    (-sin θ) (sin φ * cos θ) (cos φ * cos θ).
  Lemma Rbe_ok : (Rbe == Rz\T * Ry\T * Rx\T)%mat.
  Proof. lma. Qed.
    
End Example4CoordinateSystem.

(** another version *)
Module Example4CoordinateSystem_Version2.
  Import MatrixR.
  
  Open Scope R. Open Scope mat_scope.
  Variable ψ θ φ: R.
  Let rx : list (list R) := [[1;0;0]; [0;cos φ;sin φ]; [0;-sin φ;cos φ]]%R.
  Let ry : list (list R) := [[cos θ;0;-sin θ]; [0;1;0]; [sin θ;0;cos θ]]%R.
  Let rz : list (list R) := [[cos ψ;sin ψ;0]; [-sin ψ;cos ψ;0]; [0;0;1]]%R.
  Let rbe : list (list R) := [
      [cos θ * cos ψ; cos ψ * sin θ * sin φ - sin ψ * cos φ;
       cos ψ * sin θ * cos φ + sin φ * sin ψ];
      [cos θ * sin ψ; sin ψ * sin θ * sin φ + cos ψ * cos φ;
       sin ψ * sin θ * cos φ - cos ψ * sin φ];
      [-sin θ; sin φ * cos θ; cos φ * cos θ]]%R.

  Import MatrixR_DL.
  Lemma Rbe_ok_DL :
    let Rx : mat 3 3 := l2m rx in
    let Ry : mat 3 3 := l2m ry in
    let Rz : mat 3 3 := l2m rz in
    let Rbe : mat 3 3 := l2m rbe in
    Rbe == Rz\T * Ry\T * Rx\T.
  Proof. lma. Qed.

  Import MatrixR_DP.
  Lemma Rbe_ok_DP :
    let Rx : mat 3 3 := l2m rx in
    let Ry : mat 3 3 := l2m ry in
    let Rz : mat 3 3 := l2m rz in
    let Rbe : mat 3 3 := l2m rbe in
    Rbe == Rz\T * Ry\T * Rx\T.
  Proof. lma. Qed.

  Import MatrixR_DR.
  Lemma Rbe_ok_DR :
    let Rx : mat 3 3 := l2m rx in
    let Ry : mat 3 3 := l2m ry in
    let Rz : mat 3 3 := l2m rz in
    let Rbe : mat 3 3 := l2m rbe in
    Rbe == Rz\T * Ry\T * Rx\T.
  Proof. lma. Qed.

  Import MatrixR_NF.
  Lemma Rbe_ok_NF :
    let Rx : mat 3 3 := l2m rx in
    let Ry : mat 3 3 := l2m ry in
    let Rz : mat 3 3 := l2m rz in
    let Rbe : mat 3 3 := l2m rbe in
    Rbe == Rz\T * Ry\T * Rx\T.
  Proof. lma. Qed.

  Import MatrixR_SF.
  Lemma Rbe_ok_SF :
    let Rx : mat 3 3 := l2m rx in
    let Ry : mat 3 3 := l2m ry in
    let Rz : mat 3 3 := l2m rz in
    let Rbe : mat 3 3 := l2m rbe in
    Rbe == Rz\T * Ry\T * Rx\T.
  Proof. lma. Qed.
    
End Example4CoordinateSystem_Version2.


Module Example4VectorTheory.
  
  Import VectorR.

  (** create vector from a list, convert back, get element *)
  Let l1 := [1;2;3;4;5].
  Let v1 : vec 5 := l2v l1.
  Let l2 := v2l v1.
  (* Compute vnth v1 1. (* = (R1 + R1)%R : A *) *)

  (** Next, we can prove equation using theorems in CoqMatrix *)
  Goal forall (n : nat) (v1 v2 v3 : vec n),
      (v1 + v2) + (v3 + vec0) == 1 c* v2 + (v1 + v3).
  Proof. lma. Qed.
  
End Example4VectorTheory.


(** This example shows that, typeclass could simplify the proof *)
Module Example4SimplifyProofByTypeclass.

  Import HierarchySetoid.
  Import SetoidListExt.
  
  (** New proof. *)
  Section NEW_proof.
    Context `{M : Monoid}.
    Infix "==" := (eqlistA Aeq) : list_scope.
    
    (** 0 + l = l *)
    Example ladd_zero_l : forall l n,
        length l = n -> ladd (Aadd:=Aadd) (lzero Azero n) l == l.
    Proof.
      induction l; intros.
      - simpl in H. subst. easy.
      - simpl in *. destruct n. easy. simpl. rewrite IHl; auto.
        f_equiv. monoid_simpl.
    Qed.

  End NEW_proof.

  (** Old proof. *)
  Section OLD_proof.

    (* first, these declarations are too long *)
    Variable (A:Type) (Azero:A) (Aeq:relation A) (Aadd:A -> A -> A).
    Variable (Equiv_Aeq:Equivalence Aeq).
    Variable (add_0_l:forall a:A, Aeq (Aadd Azero a) a).
    Infix "==" := (eqlistA Aeq) : list_scope.
    
    (** 0 + l = l *)
    Example ladd_zero_l' : forall l n,
        length l = n -> ladd (Aadd:=Aadd) (lzero Azero n) l == l.
    Proof.
      induction l; intros.
      - simpl in H. subst. easy.
      - simpl in *. destruct n. easy. simpl. rewrite IHl; auto.
        f_equiv. apply add_0_l. (* second, we cannot use support for monoid *)
    Qed.

  End OLD_proof.

End Example4SimplifyProofByTypeclass.
