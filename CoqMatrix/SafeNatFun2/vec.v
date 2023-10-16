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

Require Export TupleExt HierarchySetoid SetoidListListExt.
Require Export Sequence.

Generalizable Variable A B C Aeq Beq Ceq Azero Aone Aadd Aopp Amul Ainv.

Open Scope A_scope.
Open Scope vec_scope.
Open Scope mat_scope.

(* list of lists type *)
Definition dlist A := list (list A).

(** * nat missing *)
Section nat_missing.

  (* A transparent definition for Nat.eqb_eq *)
  Lemma nat_eqb_eq : forall (n m : nat), Nat.eqb n m = true -> n = m.
  Proof.
    induction n; destruct m; simpl; auto; intros; easy.
  Defined.

  (** Coq.Arith.Lt.lt_S_n is deprecated since Coq 8.16.
    1. although coqc suggest us to use Nat.succ_lt_mono,
       but that is a  a bidirectional version, not exactly same as lt_S_n.
    2. from Coq 8.16, there is a same lemma Arith_prebase.lt_S_n,
       but it not exist in Coq 8.13,8.14.
   *)
  Definition lt_S_n: forall n m : nat, S n < S m -> n < m.
  Proof.
    intros. apply Nat.succ_lt_mono. auto.
  Qed.
  
End nat_missing.


(** * Automation *)

(** Solve i < 0 *)
Ltac solve_end :=
  match goal with
  | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.

(** Convert vector equality to pointwise element equalities, and solve i >= n *)
Ltac solve_idx :=
  let i := fresh "i" in
  let Hi := fresh "Hi" in
  intros i Hi; simpl; try solve_end;
  repeat (
      destruct i as [|i]; simpl;
      [|apply lt_S_n in Hi];
      try solve_end
    ).

(** Linear vector arithmetic, especially for real numbers *)
Ltac lva :=
  intros; solve_idx; try ring.

(* Solve contradictory order relations on natural number. Such as:
   {H1:i < n, H2: i <? n = false} 
 *)
Ltac solve_nat_ord_contr :=
  match goal with
  | H:(?i <? ?n) = false, H1:?i < ?n |- _ => apply Nat.ltb_ge in H; lia
  end.


(** * Basic Library *)

(** Loop shift of natural number *)
Section nat_loop_shift.

  (** Left loop shift. n is modulo, i is given number, k is shift offset *)
  Definition nat_lshl (n : nat) (i : nat) (k : nat) : nat :=
    Nat.modulo (i + k) n.

  (** Right loop shift. n is modulo, i is given number, k is shift offset *)
  Definition nat_lshr (n : nat) (i : nat) (k : nat) : nat :=
    Nat.modulo (i + (n - (Nat.modulo k n))) n.

  (* Compute List.map (fun i => nat_lshl 5 i 1) (List.seq 0 10). *)
  (* Compute List.map (fun i => nat_lshr 5 i 1) (List.seq 0 10). *)

End nat_loop_shift.


(** * Vector and Matrix Libraries *)


(** ** Definition of vector types *)
Section vec_type.
  Inductive vec {A} (n:nat) := vmake (f:nat -> A).

  (* Fetch out the function in a vector *)
  Definition vecf {A} {n} (v:@vec A n) : nat -> A :=
    let '(vmake _ f) := v in f.

  Notation "v $ i" := (vecf v i) : vec_scope.

  (* Equality of two vectors *)
  Section veq.
    Context {A} {Aeq:A->A->Prop} {Aeq_equiv:Equivalence Aeq}.
    
    Definition veq {n:nat} (v1 v2:vec n) : Prop := 
      forall i, i < n -> Aeq (v1$i) (v2$i).
    
    Infix "==" := veq : vec_scope.

    Lemma veq_refl : forall n (v : vec n), v == v.
    Proof. intros; intro; intros. reflexivity. Qed.
    
    Lemma veq_sym : forall {n} (v1 v2 : vec n), v1 == v2 -> v2 == v1.
    Proof. intros; intro; intros. unfold veq in H; rewrite H; auto. reflexivity.
    Qed.

    Lemma veq_trans : forall {n} (v1 v2 v3 : vec n),  v1 == v2 -> v2 == v3 -> v1 == v3.
    Proof. intros; intro; intros. unfold veq in H; rewrite H; auto. Qed.

    Global Instance veq_equiv : forall n : nat, Equivalence (@veq n).
    Proof.
      constructor; intro; intros.
      apply veq_refl. apply veq_sym; auto. apply veq_trans with y; auto.
    Qed.

    (** veq is decidable *)
    Lemma veq_dec {Dec_Aeq : Decidable Aeq} : forall {n}, Decidable (@veq n).
    Proof. intros. constructor. intros. apply seqeq_dec. Qed.
  End veq.

End vec_type.

Arguments vmake {A}.

Notation "v $ i" := (vecf v i) : vec_scope.

Module test.
  Definition v1 : vec 3 := vmake _ (fun i => i).
  Definition v2 : vec 3 := vmake _ (fun i => i+2).
  
  Goal veq (Aeq:=eq) v1 v1. Proof. lva. Qed.
End test.


(** ** Definition of matrix types *)
Section mat_type.

  Definition mat {A} r c := @vec (@vec A c) r.
  Definition smat {A} n := @mat A n n.

  (* Equality of two matrices *)
  Definition meq {A} {Aeq:A->A->Prop} {r c : nat} (m1 m2 : mat r c) : Prop :=
    veq (Aeq:=veq (Aeq:=Aeq)) m1 m2.

  Section meq_equiv.
    Context {A} {Aeq:A->A->Prop} {Aeq_equiv:Equivalence Aeq}.
    Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
    
    Lemma meq_refl : forall {r c} (m : mat r c), m == m.
    Proof. intros. apply veq_refl. Qed.
    
    Lemma meq_sym : forall {r c} (m1 m2 : mat r c), m1 == m2 -> m2 == m1.
    Proof. intros. apply veq_sym. auto. Qed.

    Lemma meq_trans : forall {r c} (m1 m2 m3 : mat r c),
        m1 == m2 -> m2 == m3 -> m1 == m3.
    Proof. intros. apply veq_trans with m2; auto. Qed.

    Lemma meq_equiv : forall r c : nat, Equivalence (@meq _ Aeq r c).
    Proof. intros. apply veq_equiv. Qed.

    Global Existing Instance meq_equiv.
    
    (** Meq is decidable *)
    Lemma meq_dec {Dec_Aeq : Decidable Aeq} : forall {r c}, Decidable (@meq _ Aeq r c).
    Proof. intros. refine veq_dec. apply veq_dec. Qed.
    
  End meq_equiv.

  (* Parameter vmakei : forall {A} (n:nat) (t:A), @vec A n. *)
  
End mat_type.


(** ** Operations on vectors *)
Section VecOp.

  Context {A} {Azero:A} {Aeq:A->A->Prop} {Aeq_equiv:Equivalence Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.

  (* Safe access (any index is accepted, but we will use valid index only) *)
  Definition vnth {n} (v:vec n) (i:nat) : A :=
    if (i <? n) then v$i else Azero.
  Notation "v ! i " := (vnth v i) : vec_scope.

  (** v i = v ! i *)
  Theorem vnth_eq : forall {n} (v:@vec A n) (i:nat), i < n -> vecf v i = vnth v i.
  Proof. intros. unfold vnth, vecf. apply Nat.ltb_lt in H. rewrite H. auto. Qed.

  (** v1 = v2 -> v1[i] = v2[i] *)
  Lemma veq_iff_vnth : forall {n : nat} (v1 v2 : vec n),
      v1 == v2 <-> (forall i, i < n -> (v1!i == v2!i)%A).
  Proof.
    intros. unfold veq. split; intros.
    - rewrite <- ?vnth_eq in *; auto. 
    - specialize (H i H0). rewrite <- ?vnth_eq in H; auto.
  Qed.
  
  (* list to vector. *)
  Definition l2v {A} (Azero:A) n (l:list A) : vec n :=
    vmake _ (fun i => if i <? n then nth i l Azero else Azero).
  
  (* vector to list *)
  Definition v2l {A} {n} (v:vec n) : list A :=
    map (fun i => v$i) (seq 0 n).

  Lemma v2l_length : forall {A} {n} (v:@vec A n), length (v2l v) = n.
  Proof. intros. unfold v2l. rewrite map_length, seq_length; auto. Qed.

  Lemma v2l_l2v_id : forall {n} (l : list A),
      length l = n -> (@v2l _ n (@l2v _ Azero n l) == l)%list.
  Proof.
    intros. unfold l2v,v2l. simpl.
    rewrite (list_eq_iff_nth Azero n); auto.
    - intros. rewrite ?nth_map_seq; auto.
      rewrite ?Nat.add_0_r. apply Nat.ltb_lt in H0. rewrite H0; simpl. easy.
    - rewrite map_length, seq_length; auto.
  Qed.

  Lemma l2v_v2l_id : forall {n} (v : vec n), l2v Azero n (v2l v) == v.
  Proof.
    intros. destruct v as [v].
    unfold l2v,v2l. simpl. lva.
    destruct (Nat.ltb_spec0 i n); try easy.
    rewrite ?nth_map_seq; auto.
    rewrite Nat.add_0_r. easy.
  Qed. 
  
  (* ==================================== *)
  (** ** Make concrete vector *)
  Definition mk_vec2 (a0 a1 : A) : vec 2 := l2v Azero 2 [a0;a1].
  Definition mk_vec3 (a0 a1 a2 : A) : vec 3 := l2v Azero 3 [a0;a1;a2].
  Definition mk_vec4 (a0 a1 a2 a3 : A) : vec 4 := l2v Azero 4 [a0;a1;a2;a3].

  (* ==================================== *)
  (** ** Convert between tuples and vector *)
  Definition t2v_2 (t : @T2 A) : vec 2 :=
    let '(a,b) := t in l2v Azero 2 [a;b].
  Definition t2v_3 (t : @T3 A) : vec 3 :=
    let '(a,b,c) := t in l2v Azero 3 [a;b;c].
  Definition t2v_4 (t : @T4 A) : vec 4 :=
    let '(a,b,c,d) := t in l2v Azero 4 [a;b;c;d].

  Definition v2t_2 (v : vec 2) : @T2 A := (v$0, v$1).
  Definition v2t_3 (v : vec 3) : @T3 A := (v$0, v$1, v$2).
  Definition v2t_4 (v : vec 4) : @T4 A := (v$0, v$1, v$2, v$3).

  Lemma v2t_t2v_id_2 : forall (t : A * A), v2t_2 (t2v_2 t) = t.
  Proof.
    intros. destruct t. simpl. unfold v2t_2. f_equal.
  Qed.

  Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v.
  Proof.
    intros. apply veq_iff_vnth. intros i Hi. simpl.
    repeat (try destruct i; auto; try lia); easy.
  Qed.

  
  (** Add an element in the head of a vector *)
  Definition vcons {A} {n} (t:A) (v:vec n) : vec (S n) :=
    vmake _ (fun i => match i with 0 => t | S i' => v$i' end).

  (** Get a vector from a given vector by remove one element *)
  Definition vremove {A} {n:nat} (v:@vec A (S n)) (k:nat) : vec (S n) :=
    vmake _ (fun i => if i <? k then v$i else v$(S i)).

  (* Compute v2l (vremove (l2v 3 99 [1;2;3]) 2). *)

  (* Mapping of a vector *)
  Definition vmap {A1 A2} {n} (f:A1 -> A2) (v:@vec A1 n) : @vec A2 n :=
    vmake _ (fun i => f (v$i)).
  
  (* Mapping of two vectors *)
  Definition vmap2 {A1 A2 A3} {n} (f:A1->A2->A3) (v1:@vec A1 n) (v2:@vec A2 n)
    : @vec A3 n :=
    vmake _ (fun i => f (v1$i) (v2$i)).

  (* Folding of a vector *)
  Fixpoint vfold_aux {A1 A2} {n} (v:nat ->A1) (f:A1->A2->A2) (b0:A2) : A2 :=
    match n with
    | O => b0
    | S n' => @vfold_aux _ _ n' v f (f (v n') b0)
    end.
  Definition vfold {A1 A2} {n} (v:@vec A1 n) (f:A1->A2->A2) (b0:A2) : A2 :=
    @vfold_aux A1 A2 n (vecf v) f b0.

  (* Folding a vector with a function of fin -> A2 -> A2 *)
  (* Fixpoint vfoldi_aux {A1 A2} {n} (v:nat ->A1) (f:fin n->A2) (b0:A2) : A2 := *)
  (*   match n with *)
  (*   | O => b0 *)
  (*   | S n' => @vfold_aux _ _ n' v f (f (v n') b0) *)
  (*   end. *)
  (* Definition vfoldi {A1 A2} {n} (v:vec A1 n) (f:fin n->A2) : A2. *)
  (*   Check  *)
  (*   vmake (fun i => f (finof n i)). *)

  (* Compute vfold (vmake 5 (fun i => i)) Nat.add 0. *)


  (* Vector algebra *)
  Section Alg.
    Context `{AG : AGroup A Aadd Azero Aopp Aeq}.
    Infix "+" := Aadd : A_scope.
    Infix "+" := (ladd (Aadd:=Aadd)) : list_scope.
    Notation "- a" := (Aopp a) : A_scope.
    Infix "-" := (fun a b => a + (-b)) : A_scope.
    Infix "==" := Aeq : A_scope.
    Infix "==" := (eqlistA Aeq) : list_scope.

    Definition vec0 {n:nat} : @vec A n := vmake _ (fun _ => Azero).

    (** *** Vector addition *)

    Definition vadd {n} (v1 v2:@vec A n) : @vec A n := vmap2 Aadd v1 v2.
    Infix "+" := vadd : vec_scope.

    (** v1 + v2 = v2 + v1 *)
    Lemma vadd_comm : forall {n} (v1 v2 : vec n), (v1 + v2) == (v2 + v1).
    Proof. repeat lva. amonoid_simpl. Qed.

    (** (v1 + v2) + v3 = v1 + (v2 + v3) *)
    Lemma vadd_assoc : forall {n} (v1 v2 v3 : vec n), (v1 + v2) + v3 == v1 + (v2 + v3).
    Proof. repeat lva. monoid_simpl. Qed.

    (** vec0 + v = v *)
    Lemma vadd_0_l : forall {n} (v : vec n), vec0 + v == v.
    Proof. repeat lva. monoid_simpl. Qed.

    (** v + vec0 = v *)
    Lemma vadd_0_r : forall {n} (v : vec n), v + vec0 == v.
    Proof. repeat lva. monoid_simpl. Qed.
    
    (** *** Vector opposite *)
  
    Definition vopp {n} (v:@vec A n) : @vec A n := vmap Aopp v.
    Notation "- v" := (vopp v) : vec_scope.

    (** v + (- v) = vec0 *)
    Lemma vadd_opp : forall {n} (v : vec n), v + (- v) == vec0.
    Proof. repeat lva. group_simpl. Qed.

    
    (** *** Vector subtraction *)
    
    Definition vsub {n} (v1 v2:@vec A n) : @vec A n := v1 + (-v2).
    Infix "-" := vsub : vec_scope.

    (** *** Below, we need a ring structure *)
    Context `{R : Ring A Aadd Azero Aopp Amul Aone Aeq}.
    Infix "*" := Amul : A_scope.
    
    Add Ring ring_inst : make_ring_theory.

    (** *** Vector scalar multiplication *)

    Definition vcmul {n} (t:A) (v:@vec A n) : @vec A n := vmake n (fun i => t*v$i).
    Definition vmulc {n} (v:@vec A n) (t:A) : @vec A n := vmake n (fun i => v$i*t).
    (* Definition vmulc {n} (v:@vec A n) (t:A) : @vec A n := vmap (fun x=>Amul x t) v. *)
    Infix "c*" := vcmul : vec_scope.
    Infix "*c" := vmulc : vec_scope.

    (** v *c a = a c* v *)
    Lemma vmulc_eq_vcmul : forall {n} a (v : vec n), (v *c a) == (a c* v).
    Proof. repeat lva. Qed.

    (** a c* (b c* v) = (a * b) c* v *)
    Lemma vcmul_assoc : forall {n} a b (v : vec n), a c* (b c* v) == (a * b)%A c* v.
    Proof. repeat lva. Qed.

    (** a c* (b c* v) = b c* (a c* v) *)
    Lemma vcmul_perm : forall {n} a b (v : vec n), a c* (b c* v) == b c* (a c* v).
    Proof. repeat lva. Qed.

    (** (a + b) c* v = (a c* v) + (b c* v) *)
    Lemma vcmul_add_distr_l : forall {n} a b (v : vec n),
        (a + b)%A c* v == (a c* v) + (b c* v).
    Proof. repeat lva. Qed.

    (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
    Lemma vcmul_add_distr_r : forall {n} a (v1 v2 : vec n), 
        a c* (v1 + v2) == (a c* v1) + (a c* v2).
    Proof. repeat lva. Qed.

    (** 1 c* v = v *)
    Lemma vcmul_1_l : forall {n} (v : vec n), Aone c* v == v.
    Proof. repeat lva. Qed.

    (** 0 c* v = vec0 *)
    Lemma vcmul_0_l : forall {n} (v : vec n), Azero c* v == vec0.
    Proof. repeat lva. Qed.
    
    (** *** Vector dot product *)
    
    (* Dot production of two vectors. *)
    (* Definition vdot {n:nat} (v1 v2:@vec A n) : A := vfold (vmap2 Amul v1 v2) Aadd Azero. *)
    Definition vdot {n:nat} (v1 v2:@vec A n) : A
      := fold_left Aadd (map (fun i => v1$i*v2$i) (seq 0 n)) Azero.
      (* := vfold (vmap2 Amul v1 v2) Aadd Azero. *)
    Infix "⋅" := vdot : vec_scope.

      (** vdot is a proper morphism respect to Aeq *)
      Lemma vdot_aeq_mor {n} :
        Proper (veq (Aeq:=Aeq) ==> veq (Aeq:=Aeq) ==> Aeq) (@vdot n).
      Proof.
        repeat (hnf; intros).
        apply fold_left_aeq_mor; try easy.
      (*   rewrite (veq_iff_vnth (Azero:=Azero)) in H,H0. *)
      (*   rewrite (list_eq_iff_nth Azero n); auto. *)
      (*   - intros. rewrite !nth_map_seq; auto. *)
      (*     rewrite Nat.add_0_r. rewrite <- ?(vnth_eq_vnth_raw (Azero:=Azero)); auto. *)
      (*     rewrite H,H0; auto. easy. *)
      (*   - rewrite map_length, seq_length; auto. *)
      (*   - rewrite map_length, seq_length; auto. *)
        (* Qed. *)
      Admitted.
      Global Existing Instance vdot_aeq_mor.

      (** dot production is commutative *)
      Lemma vdot_comm : forall {n} (v1 v2 : vec n), (v1 ⋅ v2 == v2 ⋅ v1)%A.
      Proof.
        intros. unfold vdot.
        apply fold_left_aeq_mor; try easy.
        apply SetoidListExt.map_ext. intros. ring.
      Qed.

      (** 0 * v = 0 *)
      Lemma vdot_0_l : forall {n} (v : vec n), (vec0 ⋅ v == Azero)%A.
      Proof.
        intros.
        unfold vdot. cbn.
      (*   destruct v as [v]; simpl. *)
      (*   assert (map (fun i => Azero * v i 0) (seq 0 n) == map (fun i => Azero) (seq 0 n))%list. *)
      (*   { apply SetoidListExt.map_ext. intros. ring. } *)
      (*   rewrite H. clear H. *)
      (*   induction n; simpl; try easy. *)
      (*   rewrite <- seq_shift. rewrite map_map. monoid_rw. auto. *)
        (* Qed. *)
      Admitted.

      (** v * 0 = 0 *)
      Lemma vdot_0_r : forall {n} (v : vec n), (v ⋅ vec0 == Azero)%A.
      Proof. intros. rewrite vdot_comm, vdot_0_l. easy. Qed.

  End Alg.

End VecOp.

Arguments vec0 {A}.


Section VecOp_test.

  (* <[0,1,2], [1,2,3]> = 2+6 = 8 *)
  (* Compute @vdot _ 0 Nat.add Nat.mul 3 (vmake _ (fun i => i)) (vmake _ (fun i => i+1)). *)
  
End VecOp_test.


(** ** Operations on matrices *)
Section MatOp.

  Context `{Equiv_Aeq : Equivalence A Aeq} {Azero : A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.

  (* Unsafe access (caller must assure the index manually) *)
  Notation "m $ i $ j " := (vecf (vecf m i) j) : mat_scope.

  (* Safe access (any index is accepted, but we will use valid index only) *)
  Definition mnth {r c} (m:mat r c) (i j:nat) : A :=
    vnth (Azero:=Azero) (vnth (Azero:=vec0 Azero c) m i) j.
  Notation "m ! i ! j " := (mnth m i j) : mat_scope.
  
  Lemma mnth_eq_mnthRaw : forall {r c : nat} (m : mat r c),
      (forall i j, i < r -> j < c -> m!i!j == m$i$j)%A.
  Proof.
    intros. unfold mnth. unfold vnth.
    destruct (Nat.ltb_spec0 i r), (Nat.ltb_spec0 j c); auto; try easy.
  Qed.
  
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> (forall i j, i < r -> j < c -> (m1!i!j == m2!i!j)%A).
  Proof.
    intros. split; intros.
    - unfold meq,veq,mnth,vnth in *.
      destruct (Nat.ltb_spec0 i r), (Nat.ltb_spec0 j c); simpl; auto; try easy.
    - unfold meq,veq,mnth,vnth in *.
      intros. rename i0 into j. specialize (H i j H0 H1).
      destruct (Nat.ltb_spec0 i r), (Nat.ltb_spec0 j c); simpl; auto; try easy.
  Qed.

  Lemma meq_iff_mnthRaw : forall {r c : nat} (m1 m2 : mat r c),
      m1 == m2 <-> 
        (forall i j, i < r -> j < c -> (m1$i$j == m2$i$j)%A).
  Proof.
    intros. rewrite meq_iff_mnth.
    split; intros.
    rewrite <- ?mnth_eq_mnthRaw; auto.
    rewrite ?mnth_eq_mnthRaw; auto.
  Qed.

  (* dlist to matrix. *)
  Definition l2m {r c} (dl:dlist A) : mat r c :=
    l2v (vec0 Azero c) r (map (l2v Azero c) dl).
  
  (* matrix to dlist *)
  Definition m2l {r c} (m:@mat A r c) : dlist A := map v2l (v2l m).

  Lemma m2l_length : forall {r c} (m : @mat A r c), length (m2l m) = r.
  Proof. intros. unfold m2l. rewrite map_length, v2l_length; auto. Qed.
  
  Lemma m2l_width : forall {r c} (m : @mat A r c), width (m2l m) c.
  Proof.
    intros. unfold width,m2l.
    apply Forall_map.
    apply Forall_nth. intros. rewrite v2l_length; auto.
  Qed.

  Lemma l2m_m2l_id : forall {r c} (m : @mat A r c), (l2m (m2l m)) == m.
  Proof.
    intros. unfold l2m, m2l.
  Admitted.

  Lemma m2l_l2m_id : forall {r c} (dl : list (list A)),
      (length dl = r) -> (width dl c) -> (m2l (@l2m r c dl) == dl)%dlist.
  Proof.
    intros. unfold l2m,m2l.
    (*   unfold mnth. simpl. *)
    (*   rewrite (dlist_eq_iff_nth_nth r c (Azero:=Azero)); auto. *)
    (*   - intros. rewrite ?nth_map_seq; auto. rewrite ?Nat.add_0_r. solve_mnth. *)
    (*   - rewrite map_length, seq_length; auto. *)
    (*   - apply width_map. intros. rewrite map_length, seq_length; auto. *)
    (* Qed. *)
  Admitted.

  Lemma l2m_inj : forall {r c} (d1 d2 : list (list A)),
      length d1 = r -> width d1 c -> length d2 = r -> width d2 c ->
      ~(d1 == d2)%dlist -> ~(@l2m r c d1 == l2m d2).
  Proof.
    (*   intros. unfold l2m. intro. unfold meq in *. simpl in *. destruct H3. *)
    (*   rewrite (dlist_eq_iff_nth_nth r c (Azero:=Azero)); auto. *)
    (*   intros. specialize (H4 i j H3 H5). solve_mnth. *)
    (* Qed. *)
  Admitted.
  
  Lemma l2m_surj : forall {r c} (m : mat r c), (exists d, l2m d == m).
  Proof.
    intros. exists (@m2l r c m). apply l2m_m2l_id.
  Qed.
  
  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), ~(m1 == m2) -> ~(m2l m1 == m2l m2)%dlist.
  Proof.
    (*   intros. destruct m1 as [m1], m2 as [m2]. unfold meq in *; simpl in *. *)
    (*   unfold m2l. unfold mnth. simpl. intro. *)
    (*   destruct H. intros. *)
    (*   rewrite (dlist_eq_iff_nth_nth r c (Azero:=Azero)) in H0; *)
    (*     autorewrite with list; auto. *)
    (*   - specialize (H0 i j H H1). *)
    (*     rewrite ?nth_map_seq in H0; auto. rewrite ?Nat.add_0_r in H0. solve_mnth. *)
    (*   - apply width_map. intros. autorewrite with list; auto. *)
    (*   - apply width_map. intros. autorewrite with list; auto. *)
    (* Qed. *)
  Admitted.
  
  Lemma m2l_surj : forall {r c} (d : list (list A)),
      length d = r -> width d c -> (exists m, (@m2l r c m == d)%dlist).
  Proof.
    intros. exists (@l2m r c d). apply m2l_l2m_id; auto.
  Qed.
  

  (* Get a row which row index is k *)
  Definition mrow {r c:nat} (k:nat) (m:@mat A r c) : @vec A c := m $ k.

  (* Get a column which column index is k *)
  Definition mcol {r c:nat} (m:@mat A r c) (k:nat) : @vec A r :=
    vmake r (fun i => m $ i $ k).

  (* Fetch out the function of a matrix *)
  Definition matf {r c} (m:@mat A r c) : nat->nat->A := fun i j => vecf (vecf m i) j.

  (* Make a matrix from a function *)
  Definition mmake {r c} (f:nat->nat->A) : @mat A r c := vmake _ (fun i => vmake _ (f i)).
  
  (* Left shift column.
     Eg: [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;0];[5;6;0];[8;9;0] *)
  Definition mcshl {r c} (m:mat r c) (k:nat) : mat r c :=
    mmake (fun i j => m $ i $ (j + k)).

  (* Right shift column.
     [[1;2;3];[4;5;6];[7;8;9] ==1==> [[0;1;2];[0;4;5];[0;7;8] *)
  Definition mcshr {r c} (m:mat r c) (k:nat) : mat r c :=
    mmake (fun i j => if j <? k then Azero else (m $ i $ (j - k))).

  (** Left loop shift column.
      [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;1];[5;6;4];[8;9;7] *)
  Definition mclshl {r c} (m:mat r c) (k:nat) : mat r c :=
    mmake (fun i j => m $ i $ (nat_lshl c j k)).

  (** Right loop shift column *)
  Definition mclshr {r c} (m:mat r c) (k:nat) : mat r c :=
    mmake (fun i j => m $ i $ (nat_lshr c j k)).

  Definition mtrans {r c} (m:mat r c): mat c r := mmake (fun i j => m$j$i).
  Notation "m \T" := (mtrans m) : mat_scope.

  (** Transpose twice keep unchanged. *)
  Lemma mtrans_trans : forall {r c} (m : @mat A r c), m \T \T == m.
  Proof.
    unfold mtrans. simpl. intros.
    apply meq_iff_mnthRaw. intros. simpl. reflexivity.
  Qed.

  (** Construct a matrix with a vector and a matrix by row *)
  Definition mconsr {r c} (v:vec c) (m:mat r c) : mat (S r) c :=
    mmake (fun i j => match i with O => v $ j | S i' => m $ i' $ j end).
  
  (** Construct a matrix with a vector and a matrix by column *)
  Definition mconsc {r c} (v:vec r) (m:mat r c) : mat r (S c) :=
    mmake (fun i j => match j with O => v $ i | S j' => m $ i $ j' end).

End MatOp.

(** ** Build concrete matrix *)
Section SpecifyDims.
  Context {A : Type} {Azero : A}.

  Notation mat := (@mat A).
  Notation l2m := (l2m (Azero:=Azero)).
  
  Definition mk_mat_0_c c : mat 0 c := l2m [].

  Definition mk_mat_1_1 (a11 : A) : mat 1 1 := l2m [[a11]].
  Definition mk_mat_1_2 (a11 a12 : A) : mat 1 2 := l2m [[a11;a12]].
  Definition mk_mat_1_3 (a11 a12 a13 : A) : mat 1 3 := l2m [[a11;a12;a13]].
  Definition mk_mat_1_4 (a11 a12 a13 a14 : A) : mat 1 4 := l2m [[a11;a12;a13;a14]].
  Definition mk_mat_1_c c (l : list A) : mat 1 c := l2m [l].
  
  Definition mk_mat_r_0 r : mat r 0 := l2m [].

  Definition mk_mat_2_1 (a11 a21 : A) : mat 2 1 := l2m [[a11];[a21]].
  Definition mk_mat_2_2 (a11 a12 a21 a22 : A) : mat 2 2 := l2m [[a11;a12];[a21;a22]].
  
  Definition mk_mat_3_1 (a11 a21 a31 : A) : mat 3 1 := l2m [[a11];[a21];[a31]].
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A) : mat 3 3 :=
    l2m [[a11;a12;a13]; [a21;a22;a23]; [a31;a32;a33]].

  Definition mk_mat_4_1 (a11 a21 a31 a41 : A) : mat 4 1 :=
    l2m [[a11];[a21];[a31];[a41]].
  Definition mk_mat_4_4 (a11 a12 a13 a14 a21 a22 a23 a24
                           a31 a32 a33 a34 a41 a42 a43 a44 : A) : mat 4 4 :=
    l2m [[a11;a12;a13;a14]; [a21;a22;a23;a24];[a31;a32;a33;a34]; [a41;a42;a43;a44]].
  
  Definition mk_mat_r_1 r (l : list A) : mat r 1 :=
    mmake (fun i j : nat => if (j =? 0)%nat then (nth i l Azero) else Azero).
  
End SpecifyDims.


Section Map.
  (* Mapping of a matrix *)
  Definition mmap {A1 A2} {r c} (f:A1 -> A2) (m:@mat A1 r c) : @mat A2 r c :=
    vmap (vmap f) m.

  (* Mapping of two matrixs *)
  Definition mmap2 {A1 A2 A3} {r c} (f:A1->A2->A3) (m1:@mat A1 r c)
    (m2:@mat A2 r c) : @mat A3 r c := vmap2 (vmap2 f) m1 m2.

  Section props.
    Context `{Equiv_Aeq : Equivalence A Aeq} {Azero : A}.
    Infix "==" := Aeq : A_scope.
    Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
    
    Lemma mmap2_comm : forall {r c} (f : A -> A -> A)
                         (f_comm : forall a b : A, (f a b == f b a)%A)
                         (m1 m2 : mat r c), 
        mmap2 f m1 m2 == mmap2 f m2 m1.
    Proof.
      intros r c f H1. intros m1 m2.
      unfold mmap2, meq. intros i j Hi Hj. apply H1.
    Qed.
    
    Lemma mmap2_assoc : forall {r c} (f : A -> A -> A)
                          (f_assoc : forall a b c, (f (f a b) c == f a (f b c))%A)
                          (m1 m2 m3 : mat r c), 
        mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
    Proof.
      intros r c f H1. intros m1 m2 m3.
      unfold mmap2, meq, mnth; simpl. intros i j Hi Hj.
      simpl. apply H1.
    Qed.

  End props.

End Map.

(* ==================================== *)
(** ** Zero matrirx and identity matrix *)
Section mat0_mat1.
  Context `{Equiv_Aeq : Equivalence A Aeq} (Azero Aone : A).
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  Notation "m \T" := (mtrans m) : mat_scope.
  
  Definition mat0 (r c:nat) : mat r c := vec0 (vec0 Azero c) r.

  (* Identity matrix *)
  Definition mat1 (n:nat) : smat n :=
    mmake (fun i j => if (i =? j)%nat then Aone else Azero).

End mat0_mat1.

(* Matrix algebra *)
Section Alg.
  Context `{AG : AGroup}.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := (fun a b => a + (-b)) : A_scope.
  Infix "==" := Aeq : A_scope.

  (* Infix "+" := (ladd (Aadd:=Aadd)) : list_scope. *)
  Infix "+" := (vadd (Aadd:=Aadd)) : vec_scope.
  (* Infix "==" := (eqlistA Aeq) : list_scope. *)

  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
  Notation "m $ i $ j " := (vecf (vecf m i) j) : vec_scope.
  Notation "m ! i ! j " := (mnth (Azero:=Azero) m i j) : mat_scope.

  (** *** Matrix addition *)
  Definition madd {r c} (m1 m2:mat r c) : mat r c := mmap2 Aadd m1 m2.
  Infix "+" := madd : mat_scope.

  (** m1 + m2 = m2 + m1 *)
  Lemma madd_comm : forall {r c} (m1 m2 : mat r c), m1 + m2 == (m2 + m1).
  Proof. repeat lva. amonoid_simpl. Qed.

  (** (m1 + m2) + m3 = m1 + (m2 + m3) *)
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 + m2) + m3 == m1 + (m2 + m3).
  Proof. repeat lva. monoid_simpl. Qed.

  (** mat0 + m = m *)
  Lemma madd_0_l : forall {r c} (m : mat r c), mat0 Azero r c + m == m. 
  Proof. repeat lva. monoid_simpl. Qed.

  (** m + mat0 = m *)
  Lemma madd_0_r : forall {r c} (m : mat r c), m + mat0 Azero r c == m. 
  Proof. repeat lva. monoid_simpl. Qed.
  
  (** Get element of addition with two matrics equal to additon of 
      corresponded elements. *)
  Lemma madd_nth : forall {r c} (m1 m2 : mat r c) i j,
      ((m1 + m2)%mat ! i ! j == (m1!i!j) + (m2!i!j))%A.
  Proof.
    intros. unfold mnth,vnth,madd,mmap2,vmap2. simpl.
    destruct (c >? j), (r >? i); try monoid_simpl.
  Qed.

  (** (m1 + m2)[i] = m1[i] + m2[i] *)
  Lemma mrow_madd : forall {r c} i (m1 m2 : mat r c),
      (i < r) -> (mrow i (m1 + m2)%mat == (mrow i m1) + (mrow i m2))%vec.
  Proof.
    intros. unfold mrow.
  (*   rewrite (list_eq_iff_nth Azero c). *)
  (*   - intros. unfold ladd. *)
  (*     pose proof (map2_nth (Aadd:=Aadd) *)
  (*                   (map (fun j : nat => m1$i$j) (seq 0 c)) *)
  (*                   (map (fun j : nat => m2$i$j) (seq 0 c)) i0 Azero). *)
  (*     rewrite H1. *)
  (*     + rewrite ?nth_map_seq; auto. *)
  (*       rewrite Nat.add_0_r. solve_mnth. *)
  (*     + autorewrite with list; auto. *)
  (*     + autorewrite with list; auto. *)
  (*   - autorewrite with list; auto. *)
  (*   - apply ladd_length; autorewrite with list; auto. *)
    (* Qed. *)
  Admitted.
  
  (** *** Matrix opposition *)

  Definition mopp {r c} (m:mat r c) : mat r c := mmap Aopp m.
  Notation "- a" := (mopp a) : mat_scope.

  (** - (- m) = m *)
  Lemma mopp_opp : forall {r c} (m : mat r c), - (- m) == m.
  Proof. repeat lva. apply group_inv_inv. Qed.
  
  
  (** *** Matrix subtraction *)

  Definition msub {r c} (m1 m2:mat r c) : mat r c := m1 + (-m2).
  Infix "-" := msub : mat_scope.


  (** m1 - m2 = -(m2 - m1) *)
  Lemma msub_comm : forall {r c} (m1 m2 : mat r c), m1 - m2 == - (m2 - m1).
  Proof. repeat lva. rewrite group_inv_distr,group_inv_inv. f_equiv. Qed.

  (** (m1 - m2) - m3 = m1 - (m2 + m3) *)
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c), (m1 - m2) - m3 == m1 - (m2 + m3).
  Proof. repeat lva. rewrite group_inv_distr.
    monoid_simpl. f_equiv. amonoid_simpl.
  Qed.

  (** mat0 - m = - m *)
  Lemma msub_0_l : forall {r c} (m : mat r c), (mat0 Azero r c) - m == - m.
  Proof. repeat lva. monoid_simpl. Qed.

  (** m - mat0 = m *)
  Lemma msub_0_r : forall {r c} (m : mat r c), m - (mat0 Azero r c) == m.
  Proof. repeat lva. rewrite group_opp_zero_eq_zero. monoid_simpl. Qed.

  (** m + (-m) = mat0 *)
  Lemma madd_opp : forall r c (m : mat r c), m + (-m) == mat0 Azero r c.
  Proof. repeat lva. group_simpl. Qed.

  (** m - m = mat0 *)
  Lemma msub_self : forall {r c} (m : mat r c), m - m == (mat0 Azero r c).
  Proof. repeat lva. group_simpl. Qed.


  (** *** Below, we need a ring structure *)
  Context `{R : Ring A Aadd Azero Aopp Amul Aone Aeq}.
  Infix "*" := Amul : A_scope.
  
  Add Ring ring_inst : make_ring_theory.
  
  
  (** *** Scalar multiplication of matrix *)

  (** Left scalar multiplication of matrix *)
  Definition mcmul {r c} (t:A) (m:mat r c) : mat r c := mmake (fun i j => t*m$i$j).
  Infix "c*" := mcmul : mat_scope.
  
  (** Right scalar multiplication of matrix *)
  Definition mmulc {r c} (m:mat r c) (t:A) : mat r c := mmake (fun i j => m$i$j*t).
  Infix "*c" := mmulc : mat_scope.

  (** mcmul is a proper morphism *)
  Lemma mcmul_aeq_mor : forall r c: nat,
      Proper (Aeq ==>
                meq (Aeq:=Aeq)(r:=r)(c:=c) ==>
                meq (Aeq:=Aeq)(r:=r)(c:=c)) mcmul.
  Proof.
    simp_proper. repeat lva.
    rewrite (meq_iff_mnth (Azero:=Azero)) in H0.
    specialize (H0 i i0 Hi Hi0).
    rewrite <- ?(mnth_eq_mnthRaw (Azero:=Azero)); auto. rewrite H,H0. easy.
  Qed.

  Global Existing Instance mcmul_aeq_mor.

  (** m *c a = a c* m *)
  Lemma mmulc_eq_mcmul : forall {r c} (a : A) (m : mat r c), m *c a == a c* m.
  Proof. repeat lva. Qed.

  (** 0 c* m = mat0 *)
  Lemma mcmul_0_l : forall {r c} (m : mat r c), Azero c* m == mat0 Azero r c.
  Proof. repeat lva. Qed.

  (** a c* mat0 = mat0 *)
  Lemma mcmul_0_r : forall {r c} a, a c* mat0 Azero r c == mat0 Azero r c.
  Proof. repeat lva. Qed.

  (** 1 c* m = m *)
  Lemma mcmul_1_l : forall {r c} (m : mat r c), Aone c* m == m.
  Proof. repeat lva. Qed.

  (** a c* mat1 equal to a diagonal matrix which main diagonal elements all are a *)
  Lemma mcmul_1_r : forall {n} a,
      a c* mat1 Azero Aone n == mmake (fun i j => if (i =? j)%nat then a else Azero).
  Proof. repeat lva. destruct (i =? i0); ring. Qed.

  (** a c* (b c* m) = (a * b) c* m *)
  Lemma mcmul_assoc : forall {r c} (a b : A) (m : mat r c), a c* (b c* m) == (a * b) c* m.
  Proof. repeat lva. Qed.

  (** a c* (b c* m) = b c* (a c* m) *)
  Lemma mcmul_perm : forall {r c} (a b : A) (m : mat r c), a c* (b c* m) == b c* (a c* m).
  Proof. repeat lva. Qed.

  (** a c* (m1 + m2) = (a c* m1) + (a c* m2) *)
  Lemma mcmul_add_distr_l : forall {r c} (a : A) (m1 m2 : mat r c), 
      a c* (m1 + m2) == (a c* m1) + (a c* m2).
  Proof. repeat lva. Qed.
  
  (** (a + b) c* m = (a c* m) + (b c* m) *)
  Lemma mcmul_add_distr_r : forall {r c} (a b : A) (m : mat r c), 
      (a + b)%A c* m == (a c* m) + (b c* m).
  Proof. repeat lva. Qed.


  (* Matrix multiplication *)
  Definition mmul {r c t:nat} (m1:mat r c) (m2:mat c t) : mat r t :=
    mmake (fun i k => seqsum (Aadd:=Aadd)(Azero:=Azero) (fun j => m1$i$j * m2$j$k) c).
  Infix "*" := mmul : mat_scope.

  (** (m1 * m2) * m3 = m1 * (m2 * m3) *)
  Lemma mmul_assoc : forall {r c s t : nat} (m1 : mat r c) (m2 : mat c s) (m3: mat s t), 
      (m1 * m2) * m3 == m1 * (m2 * m3).
  Proof.
    repeat lva. destruct m1 as [m1], m2 as [m2], m3 as [m3]. simpl.
    induction c; simpl.
    - intros. apply seqsum_seq0. intros. ring.
  (*   - intros. rewrite <- IHc. rewrite seqsum_cmul_l. rewrite <- seqsum_add. *)
  (*     apply seqsum_eq; intros. ring. *)
  (*     apply agroupComm. *)
      (* Qed. *)
  Admitted.

  (** m1 * (m2 + m3) = m1 * m2 + m1 * m3 *)
  Lemma mmul_add_distr_l : forall {r c s : nat} (m1 : mat r c) (m2 m3 : mat c s), 
      m1 * (m2 + m3) == m1 * m2 + m1 * m3.
  Proof.
    repeat lva. unfold mmul,mnth,madd.
    rewrite <- seqsum_add. apply seqsum_eq; intros. ring.
    apply agroupComm.
  Qed.
  
  (** (m1 + m2) * m3 = m1 * m3 + m2 * m3 *)
  Lemma mmul_add_distr_r : forall {r c s : nat} (m1 m2 : mat r c) (m3 : mat c s),
      (m1 + m2) * m3 == m1 * m3 + m2 * m3.
  Proof.
    repeat lva. unfold mmul,mnth,madd.
    rewrite <- seqsum_add. apply seqsum_eq; intros. ring.
    apply agroupComm.
  Qed.

  (** mat0 * m = mat0 *)
  Lemma mmul_0_l : forall {r c s} (m : mat c s), (mat0 Azero r c) * m == mat0 Azero r s.
  Proof.
    repeat lva. unfold mmul,mat0. apply seqsum_seq0. intros. ring.
  Qed.

  (** m * mat0 = mat0 *)
  Lemma mmul_0_r : forall {r c s} (m : mat r c), m * (mat0 Azero c s) == mat0 Azero r s.
  Proof.
    repeat lva. unfold mmul,mat0. apply seqsum_seq0. intros. ring.
  Qed.

  (** mat1 * m = m *)
  Lemma mmul_1_l : forall {r c : nat} (m : mat r c), mat1 Azero Aone r * m == m.
  Proof.
    repeat lva.
    apply (seqsum_unique _ _ _ i); auto.
    - rewrite Nat.eqb_refl. ring.
    - intros. bdestruct (i =? j). lia. ring.
  Qed.

  (** m * mat1 = m *)
  Lemma mmul_1_r : forall {r c : nat} (m : mat r c), m * mat1 Azero Aone c == m.
  Proof.
    repeat lva. unfold mmul,mat1.
    apply (seqsum_unique _ _ _ i0); auto.
    - rewrite Nat.eqb_refl. ring.
    - intros. bdestruct (j =? i0). lia. ring.
  Qed.
  
  (* a c* (m1 * m2) = (a c* m1) * m2. *)
  Lemma mcmul_mul_assoc : forall {r c s} (a : A) (m1 : mat r c) (m2 : mat c s), 
      a c* (m1 * m2) == (a c* m1) * m2.
  Proof.
    repeat lva. unfold mcmul,mmul.
    rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
  Qed.
  
  (** m1 * (a c* m2) = a c* (m1 * m2). *)
  Lemma mcmul_mul_perm : forall {r c s} (a : A) (m1 : mat r c) (m2 : mat c s), 
      a c* (m1 * m2) == m1 * (a c* m2).
  Proof.
    repeat lva. unfold mcmul,mmul.
    rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
  Qed.

End Alg.

Section MatOp_test.
  Let m1 : mat 2 3 := @l2m nat 0 2 3 [[1;2;3];[4;5;6]].
  (* Compute v2l (mrow m1 1). *)
  (* Compute v2l (mcol m1 1). *)
  
  Let v1 : vec 3 := l2v 0 3 [7;8;9].
  Let v2 : vec 2 := l2v 0 2 [10;11].

  (* Compute m2l (mconsr v1 m1). *)
  (* Compute m2l (mconsc v2 m1). *)
  
End MatOp_test.


(* ==================================== *)
(** ** Other OPs and PROPs *)

(** Convert between tuples and matrix *)
Section t2m_m2t.
  Context `{Equiv_Aeq : Equivalence A Aeq} {Azero:A}.
  (* Notation "m ! i ! j " := (mnth (Azero:=Azero) m i j) : mat_scope. *)
  Notation "m $ i $ j " := (vecf (vecf m i) j) : mat_scope.
  
  (** Tuples 3x3 -> mat_3x3 *)
  Definition t2m_3x3 (t : @T_3x3 A) : @mat A 3 3.
  Proof.
    destruct t as ((t1,t2),t3).
    destruct t1 as ((a11,a12),a13).
    destruct t2 as ((a21,a22),a23).
    destruct t3 as ((a31,a32),a33).
    exact (mk_mat_3_3 (Azero:=Azero) a11 a12 a13 a21 a22 a23 a31 a32 a33).
  Defined.

  (** mat_3x3 -> tuple 3x3. That is: ((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) *)
  Definition m2t_3x3 (m : mat 3 3) : @T_3x3 A :=
    ((m$0$0, m$0$1, m$0$2),
      (m$1$0, m$1$1, m$1$2),
      (m$2$0, m$2$1, m$2$2)).

  (** m[0,0]: mat_1x1 -> A *)
  Definition scalar_of_mat (m : @mat A 1 1) := m$0$0.

End t2m_m2t.

