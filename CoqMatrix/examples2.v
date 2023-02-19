(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : More examples for usage of CoqMatrix library.
  author    : ZhengPu Shi
  date      : 2023.02
*)

From CoqMatrix Require MatrixAll VectorAll.

(** * Multi-input multi-output state-space expressions *)
Module MIMO_statespace.
  Import MatrixAll MatrixR_SF.

  

End MIMO_statespace.

(** * Matrix over natural numbers *)
Module Example4Nat.
  (** import the library needed to use *)
  Import MatrixAll MatrixNat_DR. (* model: DepRec *)

  (** Then, all functions, theorems, notations are available *)
  Example dl := [[1;2;3];[4;5;6]].
  Example m1 : mat 2 3 := @l2m 2 3 dl.
  Compute (m2l m1). (* = [[1; 2; 3]; [4; 5; 6]] : list (list A) *)
  Compute (mnth m1 0 1). (* = 2 : A *)
  Compute (m2l (m1\T)). (* = [[1; 4]; [2; 5]; [3; 6]] : list (list A) *)
  Goal mmap S m1 == l2m [[2;3;4];[5;6;7]].
  Proof. cbv. reflexivity. Qed.

  (** Check that if A is nat really *)
  Print A. (* A = nat : Type *)

  (** You can mixed use all models *)
  Import MatrixAllNat. (* all models *)
  Compute @DL.l2m 2 3 dl.
  Compute @DP.l2m 2 3 dl.
  Compute @DR.l2m 2 3 dl.
  Compute @NF.l2m 2 3 dl.
End Example4Nat.


(** * Matrix over rational numbers *)
Module Example4Q.

  (** Import library needed *)
  Import MatrixAll MatrixQ_DL. (* model: DepList *)
  Open Scope Q.
  Open Scope mat_scope.

  (** Q is setoid equal, not leibniz equal *)
  Goal 6/4 <> 1.5. Proof. easy. Qed.
  Goal (6/4 == 1.5)%Q. Proof. easy. Qed.

  (** We can then see that our matrix theory works well for elements of rational 
      type due to its support for setoid equality. *)
  Example m1 : mat 2 3 := l2m [[6/4;10/4;7/2];[4;5;6]].
  Example m2 : mat 2 3 := l2m [[1.5;2.5;3.5];[4;5;6]].
  Example eq0 : m1 <> m2. Proof. easy. Qed.
  Example eq1 : m1 == m2. Proof. repeat constructor. Qed.

  (** Proof by compute or by using properties *)
  Definition mat1 {n} := mat1 n.
  Goal m1 * mat1 == m2. Proof. cbn;repeat constructor. Qed.
  Goal m1 * mat1 == m2. Proof. rewrite mmul_1_r. apply eq1. Qed.
  
End Example4Q.


(** * Mutual conversion and mixed use between multiple models *)
Module Example4Cvt.
  
  (** Import library needed to use *)
  Import MatrixAll MatrixAllZ. (* all models *)
  Import MatrixZ_DL. (* notations on DL *)
  Import Coq.Vectors.Vector VectorNotations. (* notations for Coq.Vector *)
  Open Scope Z.
  Open Scope mat_scope.

  (** convert from one model to other models *)
  Example m : NF.mat 2 2 := NF.mk_mat_2_2 1 2 3 4.
  Compute nf2dl m. (* = [[1; 2]; [3; 4]]%vector : DL.mat 2 2 *)
  Compute nf2dp m. (* = (1, (2, tt), (3, (4, tt), tt)) : DP.mat 2 2 *)
  Compute nf2dr m. (* = {| mdata := [[1;2];[3;4]]; .. |} : DR.mat 2 2 *)
  (* Compute nf2ff m. *)
  (* The evaluation on FF is crashed! *)

  (** prove that {DL -> DP -> DR -> NF -> DL} return back *)
  Goal forall r c (m1 : DL.mat r c),
    let m2 : DP.mat r c := dl2dp m1 in
    let m3 : DR.mat r c := dp2dr m2 in
    let m4 : NF.mat r c := dr2nf m3 in
    let m5 : DL.mat r c := nf2dl m4 in
    m5 == m1.
  Proof.
    intros. unfold m5,m4,m3,m2,dl2dp,dp2dr,dr2nf,nf2dl.
    rewrite NF.m2l_l2m_id; auto with mat.
    rewrite DP.m2l_l2m_id; auto with mat.
    rewrite DR.m2l_l2m_id; auto with mat.
    rewrite DL.l2m_m2l_id; auto with mat.
    reflexivity.
  Qed.
  
End Example4Cvt.

Module Example4CoordinateSystem.
  
  Import MatrixAll MatrixR_DL. (* DP/DR/NF/FF *)
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
  Proof.
    cbv. repeat constructor; ring.
  Qed.
    
End Example4CoordinateSystem.

(** another version *)
Module Example4CoordinateSystem_Version2.
  
  Import MatrixAll MatrixAllR.
  Open Scope R. Open Scope mat_scope.
  Variable ψ θ φ: R.
  Let rx : list (list R) := [[1;0;0]; [0;cos φ;sin φ]; [0;-sin φ;cos φ]].
  Let ry : list (list R) := [[cos θ;0;-sin θ]; [0;1;0]; [sin θ;0;cos θ]].
  Let rz : list (list R) := [[cos ψ;sin ψ;0]; [-sin ψ;cos ψ;0]; [0;0;1]].
  Let rbe : list (list R) := [
      [cos θ * cos ψ; cos ψ * sin θ * sin φ - sin ψ * cos φ;
       cos ψ * sin θ * cos φ + sin φ * sin ψ];
      [cos θ * sin ψ; sin ψ * sin θ * sin φ + cos ψ * cos φ;
       sin ψ * sin θ * cos φ - cos ψ * sin φ];
      [-sin θ; sin φ * cos θ; cos φ * cos θ]].

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
    
End Example4CoordinateSystem_Version2.


Module Example4VectorTheory.
  (** import library *)
  Import VectorAll VectorR_DR.
  Open Scope R.
  Open Scope vec_scope.

  (** create vector from a list, convert back, get element *)
  Let l1 := [1;2;3;4;5].
  Let v1 : vec 5 := l2v l1.
  Let l2 := v2l v1.
  Compute vnth v1 1. (* = (R1 + R1)%R : A *)

  (** Next, we can prove equation using theorems in CoqMatrix *)
  Goal forall (n : nat) (v1 v2 v3 : vec n),
      (v1 + v2) + (v3 + vec0) == 1 c* v2 + (v1 + v3).
  Proof.
    intros. rewrite vadd_0_r, vcmul_1_l, <- vadd_assoc.
    f_equiv. apply vadd_comm.
  Qed.
  
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
    Let ladd_zero_l : forall l n,
        length l = n -> ladd (Aadd:=Aadd) (lzero A0 n) l == l.
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
    Variable (A:Type) (A0:A) (Aeq:relation A) (Aadd:A -> A -> A).
    Variable (Equiv_Aeq:Equivalence Aeq).
    Variable (add_0_l:forall a:A, Aeq (Aadd A0 a) a).
    Infix "==" := (eqlistA Aeq) : list_scope.
    
    (** 0 + l = l *)
    Let ladd_zero_l : forall l n,
        length l = n -> ladd (Aadd:=Aadd) (lzero A0 n) l == l.
    Proof.
      induction l; intros.
      - simpl in H. subst. easy.
      - simpl in *. destruct n. easy. simpl. rewrite IHl; auto.
        f_equiv. apply add_0_l. (* second, we cannot use support for monoid *)
    Qed.

  End OLD_proof.


End Example4SimplifyProofByTypeclass.
