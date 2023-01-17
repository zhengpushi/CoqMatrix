(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : array is a model of array or vector with fixed length
  author      : ZhengPu Shi
  date        : 2022.05
  
  remark      :
  1. main idea of the work
  (1). definition
    Record array A n := {adata : list A; acond : |adata| = n}
  (2). downgrade the array problem to list problem by remove the acond 
    proof with UIP (Uniqueness of Indentity Proofs).
  (3). construct multi-dimensional-array by repeat use this structure.
  2. compare to Coq.Vectors.Vector, this is more simple
  3. the output of extraction OCaml code are more simple.
  4. several implementations are isomorphic each other.
*)


Require Import Coq.Logic.Eqdep.
        Import EqdepTheory.   (* UIP *)

Require Export ListExt.   (* List extension *)


(* ======================================================================= *)
(** ** Definitions of array *)
Section Defs.
  
  (** An array is consist of a list and a length constraint of that list. *)
  Record array {A n} := mkarray {
    adata : list A;
    acond : length adata = n
  }.

  Global Arguments mkarray {A n}.
  
  (** An array with length equal to 0 *)
  Definition array_length0 {A} : @array A 0 := mkarray [] eq_refl.
  
End Defs.


(* ======================================================================= *)
(** ** Basic properties of array *)
Section Props.

  Variable A : Type.
  
  (** Length of adata is stable *)
  Lemma adata_length : forall {n} (a : @array A n), length (adata a) = n.
  Proof. intros n [l H]. auto. Qed.
  
  (** array equal iff its data equal *)
  Lemma aeq_iff : forall {n} (a1 a2 : @array A n), 
    adata a1 = adata a2 <-> a1 = a2.
  Proof.
    intros n [l1 H1] [l2 H2]; simpl. split; intros.
    - subst. f_equal. apply UIP.
    - injection H; auto.
  Qed.

  (** array not equal iff its data not equal *)
  Lemma aeq_iff_not : forall {n} (a1 a2 : @array A n), 
    adata a1 <> adata a2 <-> a1 <> a2.
  Proof.
    intros. split; intros; intro H1; apply aeq_iff in H1; auto.
  Qed.
  
  (** array with length 0 has empty data *)
  Lemma adata_length0 : forall (a : @array A 0), adata a = [].
  Proof. destruct a. simpl. rewrite length_zero_iff_nil in *. auto. Qed.
  
  (** array with length 0 has unique form *)
  Lemma array_length0_eq : forall (a : @array A 0), a = array_length0.
  Proof. intros. apply aeq_iff. simpl. apply adata_length0. Qed.

End Props.


(* ======================================================================= *)
(** ** Create a empty array *)
Section arrayZero.
  
  Definition azero {A} (A0 : A) (n : nat) : @array A n :=
    mkarray (repeat A0 n) (repeat_length A0 n).
  
End arrayZero.


(* ======================================================================= *)
(** ** Convert array shape *)
Section arrayCast.
  
  Definition acast {A} n1 n2 (H : n1 = n2) : @array A n1 -> @array A n2.
    intros a.
    refine (mkarray (adata a) _).
    rewrite adata_length. auto.
    Defined.
    
End arrayCast.


(* ======================================================================= *)
(** ** Convert list to array *)
Section List_to_array.
  
  (** list to array with length of [length l] *)
  Definition l2a {A} (l : list A) : @array A (length l) :=
    mkarray l (eq_refl).
  
  (** treat list as array if need. *)
  Coercion l2a : list >-> array.
  
  (** list to array with length n which n is the length of the list *)
  Definition l2a_pf {A} n (l : list A) (H : length l = n) : @array A n :=
    mkarray l H.
  
  (** list to array with length n, if given list is lack of exceed then the 
    data will be cut or filled with zero *)
  Definition l2a_fix {A} n (l : list A) (A0:A) : @array A n :=
    mkarray (list_to_listN A0 l n) list_to_listN_length.
  
  Lemma l2a_fix_adata {A} : forall n (a : @array A n) (A0:A), 
    l2a_fix n (adata a) A0 = a.
  Proof.
    intros. apply aeq_iff. simpl. apply list_to_listN_eq. apply adata_length.
  Qed.
  
(*   (** All these versions are equivalent *)
  Lemma l2a_eq_l2a_pf : forall A n (l : list A) (H : length l = n),
    l2a l -> (l2a_pf n l H). *)
  
  Section test.
    
    Let a1 : array := [1;2].
    Let a21 : array := [l2a [1;2]; l2a [3;4]].
    Let a22 : array := [l2a [5;6]; l2a [7;8]].
    Let a3 : array := l2a [a21;a22].

    Compute a1.
    Compute adata a1.

    Compute a21.
    Compute adata a21.
    Compute adata (hd _ (adata a21)).
    
    Compute a3.
    Compute adata a3.
    Compute adata (hd _ (adata a3)).
    Compute hd _ (adata (hd _ (adata a3))).
    Compute adata (hd _ (adata (hd _ (adata a3)))).
    
    Compute l2a_pf 3 [1;2;3] eq_refl.
    Compute l2a_fix 5 [1;2;3] 0.

  End test.
  
End List_to_array.


(* ======================================================================= *)
(** ** Convert Coq.Vectors.VectorDef.t to array *)
Section CoqVector_to_array.
  
  Import VectorDef.
  
  (** Create a array by Vector.t *)
  Fixpoint coqvec2a {A} {n} (v : Vector.t A n) : @array A n.
    refine (mkarray (VectorDef.to_list v) _).
    induction v; auto.
    assert (to_list (Vector.cons A h n v) = h :: to_list v); auto.
    rewrite H. simpl. rewrite IHv. auto.
  Defined.
  
  Section test.
  
    Import VectorNotations.
    
    Compute coqvec2a [1;2;3].
    
  End test.
  
End CoqVector_to_array.


(* ======================================================================= *)
(** Get hd or tl of an array *)
Section Array_hd_tl.
  
  (** Get head element *)
  Definition ahd {A n} (a : @array A n) (A0 : A) : A := 
    hd A0 (adata a).
  
  (** Get head element of a array which length is 0 *)
  Lemma ahd_length0 : forall A A0 (a : @array A 0), ahd a A0 = A0.
  Proof.
    intros. destruct a as [l H]. unfold ahd. simpl.
    induction l; simpl in *; auto. easy.
  Qed. 
  
  (** Get tail elements *)
  
  (** pred version *)
  Definition atl_pred {A n} (a : @array A n) : @array A (pred n).
    refine (mkarray (tl (adata a)) _).
    rewrite tl_length. rewrite adata_length. auto.
  Defined.
  
  (** succ version *)
  Definition atl {A n} (a : @array A (S n)) : @array A n.
    refine (mkarray (tl (adata a)) _).
    rewrite tl_length. rewrite adata_length. apply PeanoNat.Nat.pred_succ.
  Defined.
  
  (** two version are equivalent *)
  Lemma atl_pred_eq_atl : forall A n (a : @array A (S n)), atl_pred a = atl a.
  Proof. intros. apply aeq_iff. simpl. auto. Qed.
  
  (** Get data of an array equal to cons of ahd and atl of the array. *)
  Lemma adata_eq_ahd_atl : forall A (A0:A) n (a : @array A (S n)),
    adata a = (ahd a A0) :: (adata (atl a)).
  Proof.
    intros. destruct a as [l H]. simpl. unfold ahd. simpl.
    destruct l; auto. easy.
  Qed.
  
End Array_hd_tl.


(* ======================================================================= *)
(** ** Get n-th element *)
Section Get_nth.

  Variable A : Type.
  Variable A0 : A.
  Variable n : nat.
  
  (** Get element with index, if the index out-of-bounds then return A0 *)
  Definition aget (a : @array A n) (i : nat) : A := 
    nth i (adata a) A0.
  
  (** array equal iff every visit with valid index get same result *)
  Lemma aeq_iff_aget : forall (a1 a2 : @array A n),
    a1 = a2 <-> (forall (i : nat) (Hi : i < n), aget a1 i = aget a2 i).
  Proof.
    intros [l1 H1] [l2 H2]. split; intros.
    - f_equal. auto.
    - apply aeq_iff; simpl.
      rewrite (list_eq_iff_nth A0 n); auto.
  Qed.

End Get_nth.

Global Arguments aget {A} _ {n}.


(* test *)
Section test.

  Compute aget 0 [1;2;3] 0.
  Compute aget 0 [1;2;3] 1.

End test.


(* ======================================================================= *)
(** ** Set n-th element and return a new array *)
Section Set_nth.

  Variable A : Type.
  Variable n : nat.
  
  (** Set element by index with a constant value. *)
  Definition aset (a : @array A n) (i : nat) (x : A) : @array A n :=
    let 'mkarray l H := a in
      mkarray (lst_chg l i x) (lst_chg_height l i n x H).
  
  (** Set element by index with a function. *)
  Definition asetf (a : @array A n) (i : nat) (f : nat -> A) : @array A n :=
    let 'mkarray l H := a in
      mkarray (lst_chgf l i f) (lst_chgf_height l n i f H).
   
End Set_nth.

Global Arguments aset {A n}.
Global Arguments asetf {A n}.

(* test *)
Section test.

  Compute aset [1;2;3] 1 9.
  Compute asetf [1;2;3] 1 (fun i => i + 10).

End test.


(* ======================================================================= *)
(** ** Mapping of an array *)
Section Map.
  
  Variable A B : Type.
  Variable n : nat.
  Variable f : A -> B.
  
  Definition amap (a : @array A n) : @array B n.
    refine (mkarray (map f (adata a)) _).
    rewrite map_length. apply adata_length.
  Defined.

End Map.

Global Arguments amap {A B n}.

Section test.
  
  Compute amap (fun i => Nat.even i) [1;2;3].

End test.


(* ======================================================================= *)
(** *** Properties of amap *)
Section amap_Props.
  
  Variable A B C : Type.
  Variable n : nat.
  
  Lemma amap_ext : forall (f g : A -> A) (H : forall a : A, f a = g a)
    (a : @array A n), amap f a = amap g a.
  Proof. intros. apply aeq_iff. simpl. apply map_ext. auto. Qed.
  
  Lemma amap_amap : forall (f : A -> B) (g : B -> C)
    (a : @array A n), amap g (amap f a) = amap (fun x : A => g (f x)) a.
  Proof. intros. apply aeq_iff. simpl. apply map_map. Qed.

End amap_Props.


(* ======================================================================= *)
(** ** Properties when mapping of array, especially for arith ops *)
Section Map_Props.

  Variable A : Type.
  Variable A0 : A.
  Variable n : nat.
  Variable fopp : A -> A.
  Variable fopp_fopp : forall x, fopp (fopp x) = x.
  Variable fopp_0 : fopp A0 = A0.
  
  (** - (- a) = a *)
  Lemma aopp_aopp (a : @array A n) : amap fopp (amap fopp a) = a.
  Proof.
    destruct a as [l]. apply aeq_iff. simpl.
    rewrite map_map. simpl. rewrite <- map_id.
    rewrite map_ext with (g:= fun x : A => x); auto.
  Qed.
  
  (** - 0 = 0 *)
  Lemma amap_zero : amap fopp (azero A0 n) = azero A0 n.
  Proof. apply aeq_iff. simpl. rewrite map_repeat. rewrite fopp_0. auto. Qed.
  
End Map_Props.


(* ======================================================================= *)
(** ** Mapping of two arrays *)
Section Map2.
  
  Variable A B C : Type.
  Variable n : nat.
  Variable f2 : A -> B -> C.
  
  Definition amap2 (a1 : @array A n) (a2 : @array B n) : @array C n.
    refine (mkarray (map2 f2 (adata a1) (adata a2)) _).
    rewrite (map2_length) with (n:=n); auto. all: apply adata_length.
  Defined.
  
End Map2.

Global Arguments amap2 {A B C n}.

Section test.
  
  Compute amap2 (fun i j => i + j) [1;2;3] [4;5;6].

End test.


(* ======================================================================= *)
(** ** Properties when mapping of two arrays, especially for arith ops. *)
Section Map2_Props.

  Variable A : Type.
  Variable A0 : A.
  Variable n : nat.
  Variable fadd : A -> A -> A.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
  Variable fadd_assoc : forall a b c, fadd (fadd a b) c = fadd a (fadd b c).
  Variable fadd_0_l : forall a, fadd A0 a = a.

  Lemma amap2_comm : forall (a1 a2 : @array A n),
    amap2 fadd a1 a2 = amap2 fadd a2 a1.
  Proof.
    intros [l1 H1] [l2 H2]. apply aeq_iff; simpl. 
    apply map2_comm; auto.
  Qed.
  
  Lemma amap2_assoc : forall (a1 a2 a3 : @array A n),
    amap2 fadd (amap2 fadd a1 a2) a3 = amap2 fadd a1 (amap2 fadd a2 a3).
  Proof.
    intros [l1 H1] [l2 H2] [l3 H3]. apply aeq_iff; simpl.
    apply map2_assoc; auto.
  Qed.
  
  (* 0 + a = a *)
  Lemma amap2_zero_l : forall (a : @array A n), amap2 fadd (azero A0 n) a = a.
  Proof.
    intros [l H]. apply aeq_iff; simpl. gd H. gd l. induction n; intros.
    - apply length_zero_iff_nil in H. subst; auto.
    - destruct l. easy. inversion H. simpl. subst. f_equal; auto.
  Qed.
  
  (* a + 0 = a *)
  Lemma amap2_zero_r : forall (a : @array A n), amap2 fadd a (azero A0 n) = a.
  Proof.
    intros. rewrite amap2_comm. apply amap2_zero_l.
  Qed.

End Map2_Props.

(* 
(* ======================================================================= *)
(** ** General properties when map and map2. *)
Section Map2_Map_Props_General.
  
  Lemma map2_map_distr : forall {A n} (f1 f2 : A -> A) (g : A -> A -> A) 
    (h : A -> A) (m : @array A n),
    map (amap h) (adata m) =
map2 g (map (amap f1) (adata m))
  (map (amap f2) (adata m))

End Map2_Map_Props_General. *)


(* ======================================================================= *)
(** ** Properties when map and map2 both exists, especially for arith ops. *)
Section Map2_Map_Props_Arith.
  Variable A : Type.
  Variable A0 : A.
  Variable n : nat.
  Variable fopp : A -> A.
  Variable fadd : A -> A -> A.
  Variable fopp_fadd_hom : forall x1 x2 : A, 
    fopp (fadd x1 x2) = fadd (fopp x1) (fopp x2).
  Variable fadd_fopp_0_r : forall a, fadd a (fopp a) = A0.
  
  (** amap is homomorphic mapping. Eg.: - (l1 + l2) = (-l1) + (-l2) *)
  Lemma amap2_amap_homo : forall (a1 a2 : @array A n), 
    amap fopp (amap2 fadd a1 a2) = amap2 fadd (amap fopp a1) (amap fopp a2).  
  Proof.
    intros. apply aeq_iff. simpl. apply eq_sym. apply map2_map_hom.
    intros; auto.
  Qed.
  
  (** l + (-l) = 0 *)
  Lemma amap2_amap_r : forall (a : @array A n),
    amap2 fadd a (amap fopp a) = azero A0 n.
  Proof.
    intros. apply aeq_iff. simpl.
    assert (forall n l, length l = n -> map2 fadd l (map fopp l) = repeat A0 n).
    { intros m. induction m; intros.
      - apply length_zero_iff_nil in H. subst; auto.
      - destruct l; simpl. easy. inversion H. f_equal; auto.
        rewrite H1. apply IHm. auto. }
    apply H. apply adata_length.
  Qed.
  
End Map2_Map_Props_Arith.


(* ######################################################################### *)
(** * array of dim n1*n2*n3*... *)

Module ArrayHigherDimension.
  
  (* ======================================================================= *)
  (** ** Definitions of higher dimensional array. *)
  Section Defs.
    
    (** Type of array with specify dimensional *)
    Definition arr1 {A n1} := @array A n1.
    Definition arr2 {A n1 n2} := @array (@arr1 A n2) n1.
    Definition arr3 {A n1 n2 n3} := @array (@arr2 A n2 n3) n1.
    Definition arr4 {A n1 n2 n3 n4} := @array (@arr3 A n2 n3 n4) n1.
    
    (** Zero array *)
    Definition azero1 {A} n1 (A0 : A) : arr1 := 
      azero A0 n1.
    Definition azero2 {A} n1 n2 (A0 : A) : arr2 := 
      azero (azero1 n2 A0) n1.
    Definition azero3 {A} n1 n2 n3 (A0 : A) : arr3 := 
      azero (azero2 n2 n3 A0) n1.
    Definition azero4 {A} n1 n2 n3 n4 (A0 : A) : arr4 := 
      azero (azero3 n2 n3 n4 A0) n1.
    
    (** List to array *)
    Definition l2a1 {A} n1 l (A0 : A) := 
      l2a_fix n1 l A0.
    Definition l2a2 {A} n1 n2 l (A0 : A) :=
      l2a1 n1 (map (fun x => l2a1 n2 x A0) l) (azero1 n2 A0).
    Definition l2a3 {A} n1 n2 n3 l (A0 : A) :=
      l2a1 n1 (map (fun x => l2a2 n2 n3 x A0) l) (azero2 n2 n3 A0).
    Definition l2a4 {A} n1 n2 n3 n4 l (A0 : A) :=
      l2a1 n1 (map (fun x => l2a3 n2 n3 n4 x A0) l) (azero3 n2 n3 n4 A0).
    
    (** Array to list *)
    Definition a2l1 {A n1} (a : @arr1 A n1) := 
      adata a.
    Definition a2l2 {A n1 n2} (a : @arr2 A n1 n2) :=
      map (fun a => a2l1 a) (adata a).
    Definition a2l3 {A n1 n2 n3} (a : @arr3 A n1 n2 n3) :=
      map (fun a => a2l2 a) (adata a).
    Definition a2l4 {A n1 n2 n3 n4} (a : @arr4 A n1 n2 n3 n4) :=
      map (fun a => a2l3 a) (adata a).
    
    (** Get element of array *)
    Definition aget1 {A n1} (a : @arr1 A n1) i1 (A0 : A) := 
      aget A0 a i1.
    Definition aget2 {A n1 n2} (a : @arr2 A n1 n2) i1 i2 (A0 : A) := 
      aget1 (aget1 a i1 (azero1 n2 A0)) i2 A0.
    Definition aget3 {A n1 n2 n3} (a : @arr3 A n1 n2 n3) i1 i2 i3 (A0 : A) := 
      aget2 (aget1 a i1 (azero2 n2 n3 A0)) i2 i3 A0.
    Definition aget4 {A n1 n2 n3 n4} (a : @arr4 A n1 n2 n3 n4) i1 i2 i3 i4 
      (A0 : A) := 
      aget3 (aget1 a i1 (azero3 n2 n3 n4 A0)) i2 i3 i4 A0.
    
  End Defs.


  (* ======================================================================= *)
  (** ** TEST. *)
  Section Test.
    
    (** list to array *)
    Let arr1_ex1 : arr1 := l2a1 2 [1;2] 0.
    Let arr2_ex1 : arr2 := l2a2 2 3 [[1;2;3];[4;5;6]] 0.
    Let arr3_ex1 : arr3 := l2a3 2 3 4 [
      [[1;2;3;4];[5;6;7;8];[9;10;11;12]];
      [[13;14;15;16];[17;18;19;20];[21;22;23;24]]] 0.
    Let arr4_ex1 : arr4 := l2a4 1 2 3 4 [[
      [[1;2;3;4];[5;6;7;8];[9;10;11;12]];
      [[13;14;15;16];[17;18;19;20];[21;22;23;24]]]] 0.
    
    Compute arr2_ex1.
    
    (** arr4 have type arr4~arr1, but base type is different *)
    Check arr4_ex1 : arr3.
    Check arr4_ex1 : arr2.
    Check arr4_ex1 : arr1.
    
    (** array to list *)
    Compute a2l1 arr1_ex1.
    Compute a2l2 arr2_ex1.
    Compute a2l3 arr3_ex1.
    Compute a2l4 arr4_ex1.
    
    Compute a2l3 arr3_ex1.
    Compute a2l2 arr3_ex1.
    Compute a2l1 arr3_ex1.
    
    (** get element *)
    Compute aget1 arr1_ex1 0 0.
    
    Compute aget2 arr2_ex1 0 0 99.
    Compute aget2 arr2_ex1 0 1 99.
    Compute aget2 arr2_ex1 0 2 99.
    Compute aget2 arr2_ex1 1 0 99.
    Compute aget2 arr2_ex1 1 1 99.
    Compute aget2 arr2_ex1 1 2 99.
    
    Compute aget4 arr4_ex1 0 0 0 0 99.     (* get an element *)
    Compute aget3 arr4_ex1 0 0 0 _. (* arr4 treated as arr3, ele is arr1 *)
    Compute aget2 arr4_ex1 0 0 _.   (* arr4 treated as arr2, ele is arr2 *)
    Compute aget1 arr4_ex1 0 _.     (* arr4 treated as arr1, ele is arr3 *)
    
  End Test.

End ArrayHigherDimension.


