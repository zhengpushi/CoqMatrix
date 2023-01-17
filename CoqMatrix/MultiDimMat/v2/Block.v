(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : Block is a fixed length array
  author      : ZhengPu Shi
  date        : 2022.05
  
  remark      :
  1. it is a simple but more general implementation inspired from our team.
  2. main idea of the work
  (1). block
    Record Block A n := {data : list A; Bcond : |data| = n}
  (2). downgrade the block problem to list problem by remove the Bcond 
    condition with UIP (Uniqueness of Indentity Proofs).
  (3). construct any-dim-array by repeat use block structure.
*)


Require Import Coq.Logic.Eqdep.
        Import EqdepTheory.   (* UIP *)

From MyStdLibExt 
Require Export ListExt.General.   (* List extension *)



(* ######################################################################### *)
(** * Definition and basic properties of block *)
Section Def.
  
  (* ======================================================================= *)
  (** ** Definitions and properties *)
  Section Defs.
  
    Variable A : Type.
    Variable n : nat.
    
    (** A block is consists of a list and a limit on the length of that list. *)
    Record Block := mkBlock {
      Bdata : list A;
      Bcond : length Bdata = n
    }.
    
    (** Length of Bdata is stable *)
    Lemma Bdata_length : forall (b : Block), length (Bdata b) = n.
    Proof. intros [l H]. auto. Qed.
    
    (** Block equal iff its data equal *)
    Lemma beq_iff : forall (b1 b2 : Block), 
      Bdata b1 = Bdata b2 <-> b1 = b2.
    Proof.
      intros [l1 H1] [l2 H2]; simpl. split; intros.
      - subst. f_equal. apply UIP.
      - injection H; auto.
    Qed.

    (** Block not equal iff its data not equal *)
    Lemma beq_iff_not : forall (b1 b2 : Block), 
      Bdata b1 <> Bdata b2 <-> b1 <> b2.
    Proof.
      intros. split; intros; intro H1; apply beq_iff in H1; auto.
    Qed.
  
  End Defs.

  Global Arguments Block {A n}.
  Global Arguments mkBlock {A n}.
  Global Arguments Bdata {A n}.
  Global Arguments Bcond {A n}.
  
End Def.



(* ######################################################################### *)
(* * Conversion between block and other data type *)
Section Conversion.


  (* ======================================================================= *)
  (** ** Create a empty block *)
  Section CreateEmpty.
    
    Definition bzero {A} (A0 : A) (n : nat) : @Block A n :=
      mkBlock (repeat A0 n) (repeat_length A0 n).
    
  End CreateEmpty.

  Global Arguments bzero {A}.
  
  
  (* ======================================================================= *)
  (** ** Create block with a list *)
  Section CreateWithList.
  
    (** Create a block by a list and the length of the list. *)
    Definition l2b {A} (l : list A) : @Block A (length l) :=
      mkBlock l (eq_refl).
    
    (** Coercion from list to Block is convenient *)
    Coercion l2b : list >-> Block.
    
  End CreateWithList.
  
  Global Arguments l2b {A}.
  
  Section test.
    
    Let b1 : Block := [1;2].
    Let b21 : Block := [l2b [1;2]; l2b [3;4]].
    Let b22 : Block := [l2b [5;6]; l2b [7;8]].
    Let b3 : Block := l2b [b21;b22].

    Compute b1.
    Compute Bdata b1.

    Compute b21.
    Compute Bdata b21.
    Compute Bdata (hd _ (Bdata b21)).
    
    Compute b3.
    Compute Bdata b3.
    Compute Bdata (hd _ (Bdata b3)).
    Compute hd _ (Bdata (hd _ (Bdata b3))).
    Compute Bdata (hd _ (Bdata (hd _ (Bdata b3)))).

  End test.
  
  
  (* ======================================================================= *)
  (** ** Create block with Coq.Vectors.VectorDef.t *)
  Section CreateWithCoqVector.
    
    Import VectorDef.
    
    (** Create a block by Vector.t *)
    Fixpoint coqvec2b {A} {n} (v : Vector.t A n) : @Block A n.
      refine (mkBlock (VectorDef.to_list v) _).
      induction v; auto.
      assert (to_list (Vector.cons A h n v) = h :: to_list v); auto.
      rewrite H. simpl. rewrite IHv. auto.
    Defined.
    
  End CreateWithCoqVector.
  
  Global Arguments coqvec2b {A n}.
  
  Section test.
    Import VectorDef.
    Import VectorNotations.
    
    Compute coqvec2b [1;2;3].
    
  End test.
  
End Conversion.



(* ######################################################################### *)
(* * Get element of block *)
Section GetElement.

  (* ======================================================================= *)
  (** ** Get element with index *)
  Section ByIndex.

    Variable A : Type.
    Variable A0 : A.
    Variable n : nat.
    
    (** Get element with index, if the index out-of-bounds then return A0 *)
    Definition bget (b : @Block A n) (i : nat) : A := 
      nth i (Bdata b) A0.
    
    (** Block equal iff every visit with valid index get same result *)
    Lemma beq_iff_bget : forall (b1 b2 : @Block A n),
      b1 = b2 <-> (forall (i : nat) (Hi : i < n), bget b1 i = bget b2 i).
    Proof.
      intros [l1 H1] [l2 H2]. split; intros.
      - f_equal. auto.
      - apply beq_iff; simpl.
        rewrite (list_eq_iff_nth A0 n); auto.
    Qed.

  End ByIndex.

  Global Arguments bget {A} _ {n}.
  
  
  (* ======================================================================= *)
  (* test *)
  Section test.

    Compute bget 0 [1;2;3] 0.
    Compute bget 0 [1;2;3] 1.

  End test.

End GetElement.



(* ######################################################################### *)
(* * Set element of block *)
Section SetElement.

  (* ======================================================================= *)
  (** ** Set element by index *)
  Section ByIndex.

    Variable A : Type.
    Variable n : nat.
    
    (** Set element by index with a constant value. *)
    Definition bset (b : @Block A n) (i : nat) (x : A) : @Block A n :=
      let 'mkBlock l H := b in
        mkBlock (lst_chg l i x) (lst_chg_height l i n x H).
    
    (** Set element by index with a function. *)
    Definition bsetf (b : @Block A n) (i : nat) (f : nat -> A) : @Block A n :=
      let 'mkBlock l H := b in
        mkBlock (lst_chgf l i f) (lst_chgf_height l n i f H).
     
  End ByIndex.

  Global Arguments bset {A n}.
  Global Arguments bsetf {A n}.
  
  (* ======================================================================= *)
  (* test *)
  Section test.
  
    Compute bset [1;2;3] 1 9.
    Compute bsetf [1;2;3] 1 (fun i => i + 10).

  End test.

End SetElement.



(* ######################################################################### *)
(* * Mapping of block *)
Section Mapping.

  (* ======================================================================= *)
  (** ** Mapping of one block *)
  Section Map1.
    
    Variable A B : Type.
    Variable n : nat.
    Variable f : A -> B.
    
    Definition bmap (b : @Block A n) : @Block B n.
      refine (mkBlock (map f (Bdata b)) _).
      rewrite map_length. apply Bdata_length.
    Defined.

  End Map1.
  
  Global Arguments bmap {A B n}.
  
  
  (* ======================================================================= *)
  (* test *)
  Section test.
    
    Compute bmap (fun i => Nat.even i) [1;2;3].

  End test.
  
  
  (* ======================================================================= *)
  (** ** Mapping of two blocks *)
  Section Map2.
    
    Variable A B C : Type.
    Variable n : nat.
    Variable f : A -> B -> C.
    
    Definition bmap2 (b1 : @Block A n) (b2 : @Block B n) : @Block C n.
      refine (mkBlock (map2 f (Bdata b1) (Bdata b2)) _).
      rewrite (map2_length) with (n:=n); auto. all: apply Bdata_length.
    Defined.
    
  End Map2.
  
  Global Arguments bmap2 {A B C n}.
  

  (* ======================================================================= *)
  (* test *)
  Section test.
    
    Compute bmap2 (fun i j => i + j) [1;2;3] [4;5;6].

  End test.
  
  
  (* ======================================================================= *)
  (** ** Properties when mapping of two blocks with same base type *)
  Section Map2_sametype.

    Variable A : Type.
    Variable n : nat.
    Variable f : A -> A -> A.
    Variable f_comm : forall a b, f a b = f b a.
    Variable f_assoc : forall a b c, f a (f b c) = f (f a b) c.

    Lemma bmap2_comm : forall (b1 b2 : @Block A n),
      bmap2 f b1 b2 = bmap2 f b2 b1.
    Proof.
      intros [l1 H1] [l2 H2]. apply beq_iff; simpl. 
      apply map2_comm; auto.
    Qed.
    
    Lemma bmap2_assoc : forall (b1 b2 b3 : @Block A n),
      bmap2 f (bmap2 f b1 b2) b3 = bmap2 f b1 (bmap2 f b2 b3).
    Proof.
      intros [l1 H1] [l2 H2] [l3 H3]. apply beq_iff; simpl.
      apply map2_assoc; auto.
    Qed.
    
  End Map2_sametype.

End Mapping.



