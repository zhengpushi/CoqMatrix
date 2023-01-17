(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : Matrix based on array.
  author      : ZhengPu Shi
  date        : 2022.05
  
  remark      :
  1. [Matrix A r c] is [array (array A c) r]
  2. use FieldType to simplify the proof of algebric operations.
*)


From MyStdLibExt 
Require Export FieldType.     (* Field Type *)

From MyStdLibExt 
Require Export FieldTypeR.    (* Field Type of R *)

From MyStdLibExt 
Require Export ListExt.ListList.    (* Extension for list list *)

Require Export Array.

Open Scope nat.



(** Two lists equal iff, hd_error and tl all equal *)
Lemma list_eq_iff_hd_error_tl : forall A (l1 l2 : list A),
  l1 = l2 <-> (hd_error l1 = hd_error l2) /\ (tl l1 = tl l2).
Proof.
  intros. gd l2. induction l1; intros; split; intros; subst; simpl; try easy.
  - destruct H. destruct l2; auto; simpl in *. easy.
  - destruct H. destruct l2; auto; simpl in *. easy. inversion H. subst; auto.
Qed.

(** Two lists equal iff, hd and tl all equal *)
Lemma list_eq_iff_hd_tl : forall A A0 (l1 l2 : list A),
  l1 = l2 <-> (hd A0 l1 = hd A0 l2) /\ (tl l1 = tl l2) /\ length l1 = length l2.
Proof.
  intros. split.
  - induction l1; intros; simpl in *; subst; try easy.
  - intros [H3 [H4 H5]]. destruct l1,l2; simpl in *; auto. easy. easy.
    subst; auto.
Qed.


(* ######################################################################### *)
(** * Matrix Theory *)
Module Matrix (E : FieldType).
  
  Import E. (* notations, ring etc. *)
  
  (** New scope *)
  Declare Scope mat_scope.
  Delimit Scope mat_scope with mat.
  Open Scope mat_scope.
  
  
  (* ======================================================================= *)
  (** ** Definition of matrix *)
  Section Defs.
  
    Definition mat {r c} := @array (@array E.A c) r.
  
  End Defs.
  
  
  (* ======================================================================= *)
  (** ** Matrix which column is 0 has unique form *)
  Section MatCols0_Unique.
  
    Lemma mat_cols0_uniq : forall r (m : @mat r 0),
      m = mkarray (repeat (array_length0) r) (repeat_length _ _).
    Proof.
      intros. apply aeq_iff. simpl. destruct m as [dl H]. simpl.
      gd r. induction dl.
      - intros. simpl in *; subst; simpl; auto.
      - intros. destruct r. easy. simpl. f_equal.
        apply array_length0_eq. apply IHdl. auto.
    Qed.
    
  End MatCols0_Unique.
  
  
  (* ======================================================================= *)
  (** ** Row cons of matrix *)
  Section MatCons.
    
    Definition mconsr {r c} (v : @array E.A c) (m : @mat r c) : @mat (S r) c.
      refine (mkarray (v :: adata m) _).
      simpl. f_equal. apply adata_length.
      Defined.
  
  End MatCons.
  
  
  (* ======================================================================= *)
  (** ** Append two matrices *)
  Section MatApp.
    
    Definition mappr {r1 r2 c} (m1 : @mat r1 c) (m2 : @mat r2 c) 
      : @mat (r1 + r2) c.
      refine (mkarray (adata m1 ++ adata m2) _).
      rewrite app_length. rewrite ?adata_length. auto.
      Defined.
    
  End MatApp.
  

  (* ======================================================================= *)
  (** ** Conversion between list list and matrix *)
  Section ListList_Mat.
    
    Definition m2l {r c} (m : @mat r c) : list (list E.A) :=
      map (fun a => adata a) (adata m).
    
    Lemma m2l_mconsr {r c} v (m : @mat r c) :
      m2l (mconsr v m) = (adata v) :: m2l m.
    Proof. unfold m2l. simpl. auto. Qed.
    
    (** Automatic shape version, lost data will be filled with A0 *)
    Fixpoint l2m (r c : nat) (dl : list (list E.A)) : @mat r c :=
      match r with
      | 0 => l2a_pf 0 [] eq_refl
      | S r => match dl with
        | [] => let v := azero E.A0 c in
          mkarray (repeat v (S r)) (repeat_length _ _)
        | l :: dl =>
          mconsr (l2a_fix c l E.A0) (l2m r c dl)
        end
      end.
    
    (** Fixed shape version, given data must have specify shape *)
    Fixpoint l2m_fix {r c} (dl : list (list E.A)) (H1 : length dl = r) :
      (width dl c) -> @mat r c.
      intros H2.
      destruct r.
      - exact (l2a_pf 0 [] eq_refl).
      - destruct dl.
        + discriminate.
        + simpl in *. 
          injection H1 as H1. destruct H2 as [H2 H3].
          pose (l2m_fix r c dl H1 H3) as m.
          pose (l2a_pf c l H2) as v.
          refine (acast _ _ _ (mconsr v m)). reflexivity.
      Defined.
    
    Lemma m2l_l2m_id : forall {r c} (dl : list (list E.A)) 
      (H1 : length dl = r) (H2: width dl c), m2l (@l2m r c dl) = dl.
    Proof.
      induction r; intros.
      - apply length_zero_iff_nil in H1. subst. auto.
      - destruct dl; try easy. simpl in *.
        injection H1 as H1. destruct H2 as [H2 H3].
        rewrite m2l_mconsr. f_equal.
        + simpl. apply list_to_listN_eq; auto.
        + apply IHr; auto.
    Qed.
    
    Lemma l2m_m2l_id : forall {r c} (m : @mat r c), l2m r c (m2l m) = m.
    Proof.
      intros. apply aeq_iff. destruct m as [dl H]. simpl.
      (* adata (l2m (m2l {| dl |})) = dl *)
      gd H. gd dl. gd c. induction r; intros.
      - simpl. apply length_zero_iff_nil in H; auto.
      - destruct dl; try easy. simpl in *. inversion H. f_equal.
        + apply l2a_fix_adata.
        + replace (map _ dl) with (m2l {| adata := dl; acond := H1|}).
          * replace ((@length (@array E.A c) dl)) with r; apply IHr.
          * unfold m2l. simpl. auto.
    Qed.
    
  End ListList_Mat.
  

  (* ======================================================================= *)
  (** ** Get n-th element *)
  Section Nth.
    
    (** Get n-th element *)
    Definition mnth {r c} (m : @mat r c) (ri ci : nat) : E.A :=
      aget E.A0 (aget (azero E.A0 c) m ri) ci.
  
  End Nth.
  

  (* ======================================================================= *)
  (** ** Specific matrix *)
  Section SpecificMat.
  
    Definition mat_1_1 (a11 : E.A) : @mat 1 1 := [l2a [a11]].
    
    Definition mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : E.A) 
      : @mat 3 3 := [l2a [a11;a12;a13]; l2a [a21;a22;a23]; l2a [a31;a32;a33]].
    
  End SpecificMat.
  

  (* ======================================================================= *)
  (** ** Matrix with all elements are 0 *)
  Section MatZero.

    Definition mat0 r c : mat := azero (azero E.A0 c) r.
  
  End MatZero.
  
  
  (* ======================================================================= *)
  (** *** Unit matrix *)
  Section UnitMatrix.
    
    Let gen_lst c := fun i => list_unit E.A0 E.A1 c i.
    
    Let gen_array c (ci : nat) : @array E.A c :=
      mkarray (gen_lst c ci) (list_unit_length E.A E.A0 E.A1 c ci).
    
    (* error: Row sequence is reversed! *)
    Let Fixpoint gen_mat1_aux' r c : @mat r c :=
      match r with
      | 0 => mat0 0 c
      | S r => 
        let a := gen_array c r in
          mconsr a (gen_mat1_aux' r c)
      end.
    
    (* fixed the "Row sequence" error  *)
    Let Fixpoint gen_mat1_aux r c : @mat r c :=
      match r with
      | 0 => mat0 0 c
      | S r => 
        let a := gen_array c r in
        let m' : @mat 1 c := mkarray [a] eq_refl in
          acast _ _ (Nat.add_1_r _) (mappr (gen_mat1_aux r c) m')
      end.
    
    Definition mat1' n := gen_mat1_aux n n.
    
    (* another version, using map, fold *)
    Definition mat1 n : @mat n n.
      refine (mkarray (map (fun i => gen_array n i) (seq 0 n)) _).
      rewrite map_length. apply seq_length.
    Defined.
    
  End UnitMatrix.
  
  
  (* ======================================================================= *)
  (** *** Mapping of matrix *)
  Section Map.
    
    Variable r c : nat.
    Variable f : E.A -> E.A.
    
    Definition mmap (m : @mat r c) : @mat r c := amap (amap f) m.

  End Map.
  
  Arguments mmap {r c}.
  
  
  (* ======================================================================= *)
  (** *** Properties of mmap *)
  Section MapProps.
    
    Variable r c : nat.
    Variable f : E.A -> E.A.
    Variable g : E.A -> E.A.
    Variable f_eq_g : forall a : A, f a = g a.
    
    Lemma mmap_ext : forall m : @mat r c, mmap f m = mmap g m.
    Proof.
      intros. apply aeq_iff. simpl. apply map_ext. apply amap_ext. auto.
    Qed.
    
  End MapProps.
  
  
  (* ======================================================================= *)
  (** *** Mapping of two matrices *)
  Section Map2.
    
    Variable r c : nat.
    Variable f : E.A -> E.A -> E.A.
    Variable f_comm : forall a b, f a b = f b a.
    Variable f_assoc : forall a b c, f a (f b c) = f (f a b) c.
    
    Definition mmap2 (m1 m2 : @mat r c) : @mat r c := amap2 (amap2 f) m1 m2.
    
    Lemma mmap2_comm : forall (m1 m2 : @mat r c), 
      mmap2 m1 m2 = mmap2 m2 m1.
    Proof. apply amap2_comm. apply amap2_comm. auto. Qed.
    
    Lemma mmap2_assoc : forall (m1 m2 m3 : @mat r c), 
      mmap2 (mmap2 m1 m2) m3 = mmap2 m1 (mmap2 m2 m3).
    Proof. apply amap2_assoc. apply amap2_assoc. auto. Qed.
    
  End Map2.
  
  Arguments mmap2 {r c}.
  
  
  (* ======================================================================= *)
  (** ** Matrix addition *)
  Section Madd.
  
    Definition madd {r c} (m1 m2 : @mat r c) : @mat r c := mmap2 E.Aadd m1 m2.
    
    Infix "+" := madd : mat_scope.
    
    Lemma madd_comm : forall {r c} (m1 m2 : @mat r c), m1 + m2 = m2 + m1.
    Proof. intros. apply mmap2_comm. intros; ring. Qed.
    
    Lemma madd_assoc : forall {r c} (m1 m2 m3 : @mat r c), 
      (m1 + m2) + m3 = m1 + (m2 + m3).
    Proof. intros. apply mmap2_assoc. intros; ring. Qed.
  
    Lemma madd_0_l : forall {r c} (m : @mat r c), madd (mat0 r c) m = m.
    Proof.
      intros. apply aeq_iff. destruct m as [d H]. simpl.
      gd d. gd c. induction r; intros.
      - simpl. apply length_zero_iff_nil in H. auto.
      - destruct d. easy. simpl in *. f_equal; auto.
        apply amap2_zero_l. intros; ring.
    Qed.
    
    Lemma madd_0_r : forall {r c} (m : @mat r c), madd m (mat0 r c) = m.
    Proof. intros. rewrite madd_comm. apply madd_0_l. Qed.
    
  End Madd.
  
  Arguments madd {r c}.
  
  Infix "+" := madd : mat_scope.
  
  
  (* ======================================================================= *)
  (** ** Matrix subtraction *)
  Section Msub.
  
    Definition mopp {r c} (m : @mat r c) : @mat r c := mmap E.Aopp m.
    
    Notation "- m" := (mopp m) : mat_scope.

    (** - 0 = 0 *)
    Lemma mopp_0 : forall {r c}, mopp (mat0 r c) = mat0 r c.
    Proof.
      intros. apply aeq_iff. simpl. gd c. induction r; intros; auto. simpl.
      f_equal; auto. apply amap_zero. ring.
    Qed.
    
    
    Definition msub {r c} (m1 m2 : @mat r c) : @mat r c := m1 + (-m2).
    
    Infix "-" := msub : mat_scope.
    
    (** - (- m) = m *)
    Lemma mopp_mopp : forall {r c} (m : @mat r c), - (- m) = m.
    Proof.
      intros. apply aeq_iff. destruct m as [d]. simpl.
      rewrite map_map. rewrite <- map_id. apply map_ext.
      intros. apply aopp_aopp. intros; ring.
    Qed.
    
    (** m1 - m2 = m2 - m1 *)
    Lemma msub_comm : forall {r c} (m1 m2 : @mat r c), m1 - m2 = - (m2 - m1).
    Proof.
      intros. apply aeq_iff. destruct m1 as [d1 H1], m2 as [d2 H2]. simpl.
      rewrite <- map2_map_hom.
      - rewrite map2_comm.
        + f_equal. rewrite map_map. rewrite <- map_id at 1. apply map_ext.
          intros. rewrite aopp_aopp; auto. intros; ring.
        + intros. apply amap2_comm. intros; ring.
      - clear. intros v1 v2. apply amap2_amap_homo. intros; ring.
    Qed.
    
    (** (m1 - m2) - m3 = m1 - (m2 + m3) *)
    Lemma msub_assoc : forall {r c} (m1 m2 m3 : @mat r c),
      (m1 - m2) - m3 = m1 - (m2 + m3).
    Proof.
      intros. apply aeq_iff.
      destruct m1 as [d1 H1], m2 as [d2 H2], m3 as [d3 H3]. simpl. clear.
      rewrite map2_assoc.
      - f_equal. apply map2_map_hom. intros.
        apply amap2_amap_homo. intros; ring.
      - intros. apply amap2_assoc. intros; ring.
    Qed.
    
    (** 0 - m = - m *)
    Lemma msub_0_l : forall {r c} (m : @mat r c), (mat0 r c) - m = mopp m.
    Proof.
      intros. apply aeq_iff. destruct m as [d H]. simpl.
      gd d. gd c. induction r; intros.
      - apply length_zero_iff_nil in H. subst; auto.
      - destruct d. easy. simpl. inversion H. f_equal.
        + apply amap2_zero_l. intros; ring.
        + rewrite H1. apply IHr. auto.
    Qed.
    
    (** m - 0 = m *)
    Lemma msub_0_r : forall {r c} (m : @mat r c), m - (mat0 r c) = m.
    Proof. intros. unfold msub. rewrite mopp_0. apply madd_0_r. Qed.
    
    (** m - m = 0 *)
    Lemma msub_self : forall {r c} (m : @mat r c), m - m = (mat0 r c).
    Proof.
      intros. apply aeq_iff. destruct m as [d H]. simpl. gd c.
      induction r; intros.
      - apply length_zero_iff_nil in H; subst; auto.
      - destruct d. easy. simpl. inversion H. f_equal; auto.
        + apply amap2_amap_r. intros; ring.
        + rewrite H1. apply IHr. auto.
    Qed.
    
  End Msub.
  
  
  (* ======================================================================= *)
  (** ** Matrix scalar multiplication *)
  Section Mcmul_Mmulc.
    
    Definition mcmul {r c} (a : A) (m : @mat r c) : @mat r c :=
      mmap (fun x => a * x) m.
    
    Definition mmulc {r c} (m : @mat r c) (a : A) : @mat r c :=
      mmap (fun x => x * a) m.
    
    Lemma mmulc_eq_mcmul : forall {r c} (a : A) (m : @mat r c), 
      mmulc m a = mcmul a m.
    Proof. intros. apply mmap_ext. intros; ring. Qed.
     
    Lemma mcmul_assoc1 : forall {r c} (a b : A) (m : @mat r c), 
      mcmul a (mcmul b m) = mcmul (Amul a b) m.
    Proof.
      intros. apply aeq_iff. simpl. rewrite map_map. apply map_ext.
      intros. rewrite amap_amap. apply amap_ext. intros; ring.
    Qed.
    
    Lemma mcmul_assoc2 : forall {r c} (a b : A) (m : @mat r c), 
      mcmul a (mcmul b m) = mcmul b (mcmul a m).
    Proof.
      intros. apply aeq_iff. simpl. rewrite ?map_map. apply map_ext.
      intros. rewrite ?amap_amap. apply amap_ext. intros; ring.
    Qed.
      
    Lemma mcmul_distr_l : forall {r c} (a : A) (m1 m2 : @mat r c), 
      mcmul a (madd m1 m2) = madd (mcmul a m1) (mcmul a m2).
    Proof.
      intros. apply aeq_iff. simpl. rewrite map2_map_hom; auto.
      intros. apply aeq_iff. simpl. rewrite map2_map_hom; auto.
      intros; ring.
    Qed.
    
    Lemma mcmul_distr_r : forall {r c} (a b : A) (m : @mat r c), 
      mcmul (Aadd a b) m = madd (mcmul a m) (mcmul b m).
    Proof.
      intros. apply aeq_iff. simpl. apply eq_sym. apply map2_map_map.
      intros. apply aeq_iff. simpl. apply eq_sym. apply map2_map_map.
      intros. ring.
    Qed.
    
    Lemma mcmul_1 : forall {r c} (m : @mat r c), mcmul A1 m = m.
    Proof.
      intros. apply aeq_iff. simpl. rewrite <- map_id. apply map_ext.
      intros. apply aeq_iff. simpl. rewrite <- map_id. apply map_ext.
      intros. ring.
    Qed.
  
  End Mcmul_Mmulc.
  
  
  (* ======================================================================= *)
  (** ** Get hd or tl or cols of a matrix *)
  Section Mat_hd_tl_cols.
  
    (* --------------------------------------------------------------------- *)
    (** *** Get head row *)
    Section mhdr.
    
      Definition mhdr {r c} (m : @mat r c) : @array E.A c := 
        ahd m (azero E.A0 c).
      
      Lemma mhdr_simp : forall r c (d : list (@array E.A c))
        (H : length d = r),
        @mhdr r c {| adata := d; acond := H |} = hd (azero E.A0 c) d.
      Proof. intros. unfold mhdr. unfold ahd. simpl. auto. Qed.
      
    End mhdr.
    
    
    (* --------------------------------------------------------------------- *)
    (** *** Get tail rows *)
    Section mtlr.
    
      (** pred version *)
      Definition mtlr_pred {r c} (m : @mat r c) : @mat (pred r) c :=
        atl_pred m.

      (** succ version *)
      Definition mtlr {r c} (m : @mat (S r) c) : @mat r c :=
        atl m.
    
    End mtlr.
    
    
    (* --------------------------------------------------------------------- *)
    (** *** Get head column *)
    Section mhdc.
      
      Definition mhdc {r c} (m : @mat r c) : @array E.A r.
        refine (mkarray (map (fun a => ahd a E.A0) (adata m)) _).
        rewrite map_length. apply adata_length.
      Defined.
      
      Lemma mhdc_cols0 : forall {r} (m : @mat r 0), mhdc m = azero E.A0 r.
      Proof.
        intros. apply aeq_iff. simpl. destruct m as [d H]. simpl.
        gd H. gd d. induction r; intros.
        - apply length_zero_iff_nil in H. subst; auto.
        - destruct d; simpl. easy. f_equal; auto. apply ahd_length0.
      Qed.
    
    
      Lemma mhdc_simp_cond1 : forall r c a d (H: length d = r), 
        @length (@array A (S c)) (a :: d) = S r.
      Proof. intros. simpl. f_equal. assumption. Qed.
      
      Lemma mhdc_simp_cond2 : forall (r c : nat) a d H,
        length (@ahd _ (S c) a 0 :: 
          @adata _ r (@mhdc _ (S c) {| adata := d; acond := H |})) = S r.
      Proof. intros. simpl. f_equal. rewrite map_length. auto. Qed.
      
      Lemma mhdc_simp : forall r c (a : @array E.A (S c)) 
        (d : list (@array E.A (S c))) (H : length d = r)
        (H1 : length (a :: d) = S r),
        @mhdc (S r) (S c) (mkarray (a :: d) H1) =
        mkarray ((ahd a E.A0) :: (@adata _ r (mhdc (mkarray d H)))) 
          (mhdc_simp_cond2 _ _ _ _ _).
      Proof. intros. apply aeq_iff. simpl. auto. Qed.
      
    End mhdc.
    
    
    (* --------------------------------------------------------------------- *)
    (** *** Get tl columns *)
    Section mtlc.
      
      (** pred version *)
      Definition mtlc_pred {r c} (m : @mat r c) : @mat r (pred c).
        refine (mkarray (map (fun a => atl_pred a) (adata m)) _).
        rewrite map_length. apply adata_length.
      Defined.
      
      (** succ version *)
      Definition mtlc {r c} (m : @mat r (S c)) : @mat r c.
        refine (mkarray (map (fun a => atl a) (adata m)) _).
        rewrite map_length. apply adata_length.
      Defined.
      
    End mtlc.
    
    
    (* --------------------------------------------------------------------- *)
    (** *** Get all columns *)
    Section mcols.
      
      Fixpoint mcols {r c} {struct c} : (@mat r c) -> list (@array E.A r) :=
        match c with
        | O => fun m => []
        | S c' => fun m => mhdc m :: (@mcols r c' (mtlc m))
        end.
      
      (** Length of mcols is stable *)
      Lemma mcols_length {r c} (m : @mat r c) : length (mcols m) = c.
      Proof.
        induction c; auto. destruct m; simpl. rewrite IHc. auto.
      Qed.
      
      (** Columns of tail of matrix (pred version) *)
      Lemma mcols_mtlc_pred : forall {r c} (m : @mat r c),
        mcols (mtlc_pred m) = tl (mcols m).
      Proof.
        intros r c. gd r. induction c; intros; simpl in *; auto. f_equal.
        apply aeq_iff. simpl. destruct m as [d H]. simpl.
        apply map_ext. intros. apply atl_pred_eq_atl.
      Qed.
      
      (** Head column of mcols equal to head row *)
      
      (** mat version *)
      Lemma mhdc_mcols' : forall {r c} (m : @mat r c),
        mhdc (mkarray (mcols m) (mcols_length m)) = 
        hd (azero E.A0 c) (adata m).
      Proof.
        intros r c. gd r. induction c; intros; simpl.
        - apply aeq_iff. simpl.
          rewrite (mat_cols0_uniq r m). simpl. destruct r; simpl; auto.
        - apply aeq_iff. simpl. destruct m as [dl H]. simpl.
          destruct dl as [|a m]; simpl.
        Admitted.
        
      (** cons version *)
      Lemma mhdc_mcols : forall {r c} (a : @array E.A c) (d : list array)
        (H : length (a :: d) = S r),
        let m := mkarray (a :: d) H in
          mhdc (mkarray (mcols m) (mcols_length m)) = a.
      Proof.
        intros. apply aeq_iff. simpl. destruct a as [l H1]. simpl in *.
        gd d. gd H1. induction l; intros; simpl in *; subst.
        Admitted.
      
      (** Columns of tail columns of mcols of matrix *)
      Lemma mcols_mtlc_mcols : forall {r c} (a : @array E.A c) (d : list array)
        (H : length (a :: d) = S r),
        let m := mkarray (a :: d) H in
          mcols (mtlc (mkarray (mcols m) (mcols_length m))) = d.
      Proof. intros. simpl. auto. Admitted.
      
      Lemma mcols_mcols : forall {r c} (m : @mat r c),
        mcols (mkarray (mcols m) (mcols_length _)) = adata m.
      Proof.
        intros. destruct m as [d H]. simpl.
        destruct r; simpl in *.
        - apply length_zero_iff_nil in H. auto.
        - destruct d. easy. f_equal.
          + (* mhdc (mcols (a::d)) = a *)
            apply mhdc_mcols.
          + (* mcols (mtlc (mcols (a::d))) = d *)
            apply mcols_mtlc_mcols.
      Qed.
         
    End mcols.
    
  End Mat_hd_tl_cols.
  
  Arguments mhdr {r c}.
  Arguments mtlr_pred {r c}.
  Arguments mtlr {r c}.
  Arguments mhdc {r c}.
  Arguments mtlc_pred {r c}.
  Arguments mtlc {r c}.
  Arguments mcols {r c}.
  
  
  (* ======================================================================= *)
  (** ** Get row or column of a matrix *)
  Section Mat_GetRow_GetColumn.
    
    (** Get one row *)
    Definition mgetr {r c} (m : @mat r c) (ri : nat) : @array E.A c := 
      aget (azero E.A0 c) m ri.
    
    (** Get one column *)
    Definition mgetc {r c} (m : @mat r c) (ci : nat) : @array E.A r.
      refine (mkarray (map (fun a => aget E.A0 a ci) (adata m)) _).
      rewrite map_length. apply adata_length.
      Defined.
    
  End Mat_GetRow_GetColumn.
  
  Arguments mgetr {r c}.
  Arguments mgetc {r c}.
  
  
  (* ======================================================================= *)
  (** ** Matrix transposition *)
  Section Mat_Trans.
    
    (** Transpose a matrix *)
    
    (** old definition, by seq *)
    Definition mtrans' {r c} (m : @mat r c) : @mat c r.
      refine (mkarray (map (fun i => mgetc m i) (seq 0 c)) _).
      rewrite map_length. apply seq_length.
      Defined.
    
    Definition mtrans {r c} (m : @mat r c) : @mat c r :=
      mkarray (mcols m) (mcols_length _).

    (** Get column of a transposed matrix return to its row *)
    Lemma mgetc_mtrans : forall {r c} (m : @mat r c) (ri : nat),
      mgetc (mtrans m) ri = mgetr m ri.
    Abort.
     
    (** Get row of a transposed matrix return to its column *)
    Lemma mgetr_mtrans : forall {r c} (m : @mat r c) (ci : nat),
      mgetr (mtrans m) ci = mgetc m ci.
    Abort.
    
(*     (** Columns of transposed matrix equal to its data *)
    Lemma mcols_mtrans : forall {r c} (m : @mat r c),
      mcols (mtrans m) = adata m.
    Proof. intros. unfold mtrans. apply mcols_mcols. Qed. *)

    (** (m^T)^T = m *)
(*     Lemma mtrans_trans : forall {r c} (m : @mat r c), mtrans (mtrans m) = m.
    Proof. intros. apply aeq_iff. simpl. unfold mtrans. apply mcols_mcols. Qed. *)
    
  End Mat_Trans.
  
  
  (* ======================================================================= *)
  (** ** Matrix multiplicaiton *)
  Section Mat_Multi.
  (* 
    Variable r c s : nat.
  
    Definition mmul (m1 : @mat r c) (m2 : @mat c s) : @mat r s.
    Lemma mmul_madd_distr_l : forall {r c A} (m1 : mat r c) (m2 m3 : mat c A), 
      mmul m1 (madd m2 m3) == madd (mmul m1 m2) (mmul m1 m3).
    Lemma mmul_madd_distr_r : forall {r c A} (m1 m2 : mat r c) (m3 : mat c A), 
      mmul (madd m1 m2) m3 == madd (mmul m1 m3) (mmul m2 m3).
    Lemma mmul_assoc : forall {r c A s} (m1 : mat r c) (m2 : mat c A) 
      (m3 : mat A s), 
     mmul (mmul m1 m2) m3 == mmul m1 (mmul m2 m3).
    Lemma mmul_0_l : forall {r c A} (m : mat c A), 
      mmul (mat0 r c) m == mat0 r A.
    Lemma mmul_0_r : forall {r c A} (m : mat r c), 
      mmul m (mat0 c A) == mat0 r A.
    Lemma mmul_1_l : forall {r c} (m : mat r c), mmul (mat1 r) m == m.
    Lemma mmul_1_r : forall {r c} (m : mat r c), mmul m (mat1 c) == m.  *)
  
  End Mat_Multi.
  
  
  (* ======================================================================= *)
  (** ** Matrix Inverse of symbol matrix *)
  Section MatInverseSymbol.
    
    (* Note that, Matlab has this function, and we can easy to check it *)
    
    (* --------------------------------------------------------------------- *)
    (** *** Adjoint Matrix *)
    Section AdjointMatrix.
      Variable r c : nat.
      Variable m : @mat r c.
      
      Definition madj (ri ci : nat) :
    
    End AdjointMatrix.
    
    (* --------------------------------------------------------------------- *)
    (** *** Determinant of matrix *)
    Section Determinant.
        
      (** det of matrix *)
      Definition det {n} (m : @mat n n) : A.

    
    End Determinant.
    
    
    
  End MatInverseSymbol.

End Matrix.


(* ######################################################################### *)
(** * Test for Matrix Theory *)
Module MatrixR := Matrix (FieldTypeR).
Export MatrixR.
    
Section Test.
  Open Scope R.
  
  (* create mat *)
  Let mat1 : mat:= [l2a [1;2]; l2a [3;4]; l2a [4;5]].
  Let mat2 : mat := mat0 2 3.
  
  (* get element *)
  Compute mnth mat1 0 0.
  Compute mnth mat1 0 1.
  Compute mnth mat1 0 2.
  Compute mnth mat1 1 0.
  Compute mnth mat1 1 1.
  Compute mnth mat1 1 2.
  Compute mnth mat1 2 0.
  Compute mnth mat1 2 1.
  Compute mnth mat1 2 2.
  
  (* mat to list list *)
  Let mat3 : mat := l2m 4 3 [[1;2];[3;4;5];[6]].
  Compute mat3.
  
  Goal mat3 = [l2a [1;2;0]; l2a [3;4;5]; l2a [6;0;0]; l2a [0;0;0]].
  Proof. apply aeq_iff. simpl. repeat f_equal; apply aeq_iff; auto. Qed.
  
  (* list list to mat *)
  Compute m2l mat1.
  
  (** Transpose *)
  Compute mtrans mat1.
  Compute m2l (mtrans mat1).

  Section test_cols.
    Compute (mcols mat1).
    Compute (mkarray (mcols mat1) (mcols_length _)).
    Compute mcols (mkarray (mcols mat1) (mcols_length _)).
    Compute m2l (mcols (mkarray (mcols mat1) (mcols_length _))).
    
(*     mcols (mkarray (mcols m) (mcols_length _)) = adata m. *)
    
  End test_cols.
  
End Test.



