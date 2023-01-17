(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : Any-dim-matrix based on list and shape constraints.
  author      : ZhengPu Shi
  date        : 2022.05
  
  remark      :
  1. it is a simple but more general implementation inspired from our team.
  2. main idea of the work
  (1). basic block
    Record Block A n := {data : list A; Bcond : |data| = n}
  (2). downgrade the Block problem to list problem by remove the Bcond 
    condition with UIP.
  (3). construct matrix by repeat use Block structure.
*)


Require Import Coq.Logic.Eqdep.
        Import EqdepTheory.   (* UIP *)

From MyStdLibExt 
Require Import ListExt.General.   (* List extension *)


(* ######################################################################### *)
(** * Basic block *)

Module Block.


  (* ======================================================================= *)
  (** ** Definition of block *)
  
  Section Def.
    
    (** A block is a record with a list and a proof, and the proof said that 
      the list have given length. *)
    Record Block {A : Type} {n : nat} := mkBlock {
      Bdata : list A;
      Bcond : length Bdata = n
    }.
    
    (** Length of Bdata *)
    Lemma Bdata_length : forall {A n} (b : @Block A n), length (Bdata b) = n.
    Proof. intros A n [l H]. auto. Qed.
    
  End Def.

  Arguments mkBlock {A n}.
  Arguments Bdata {A n}.
  Arguments Bcond {A n}.
  
  
  (* ======================================================================= *)
  (** ** Equality of block *)
  
  Section Equality.
    
    Variable A : Type.
    Variable n : nat.
    
    (** Block equal iff its data equal *)
    Lemma beq_iff : forall (b1 b2 : @Block A n), 
      Bdata b1 = Bdata b2 <-> b1 = b2.
    Proof.
      intros [l1 H1] [l2 H2]; simpl. split; intros.
      - subst. rewrite (UIP_refl nat (length l2) H2); auto.
      - injection H; auto.
    Qed.
  
    (** Block not equal iff its data not equal *)
    Lemma beq_iff_not : forall (b1 b2 : @Block A n), 
      Bdata b1 <> Bdata b2 <-> b1 <> b2.
    Proof.
      intros. split; intros.
      - intro. apply beq_iff in H0; auto.
      - intro. apply beq_iff in H0; auto.
    Qed.
    
  End Equality.
  

  (* ======================================================================= *)
  (** ** Create block from other data type *)
  Section CreateBlock.
    
    Variable A : Type.
    Variable A0 : A.
  
    (** Create a empty block *)
    Definition bzero (n : nat) : @Block A n :=
      mkBlock (repeat A0 n) (repeat_length A0 n).
  
    (** Create block with a list *)
    Definition l2b {A} (l : list A) : @Block A (length l) :=
      mkBlock l (eq_refl).
    
    Let b1 := l2b [1;2].
    Let b21 := l2b [l2b [1;2]; l2b [3;4]].
    Let b22 := l2b [l2b [5;6]; l2b [7;8]].
    Let b3 := l2b [b21;b22].
    
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
    
    (** Coercion from list to block is experimental. *)
    Section Experimental_Coercion.
      
      Coercion l2b : list >-> Block.
      
      Compute Bdata [1;2;3].
      Compute Bdata [[1;2];[3;4]].
      
      (* There are some cases may get confused about the ability of type check. 
        A example is given here. *)
      Let ex1 : Block := [[1;2];[3;4;5]].
      
      (* One may expected that ex1 has type {@Block (@Block nat 2) 2}, but it 
        isn't. Press {Shift+Alt+I} to show implicit arguments. *)
      Check ex1 : @Block (list nat) 2.
    
    End Experimental_Coercion.

  End CreateBlock.
  
  Arguments bzero {A}.
  
  
  (* ======================================================================= *)
  (** ** Get element with index *)
  Section GetElement.

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

  End GetElement.

  Arguments bget {A} _ {n}.
  
  Compute bget 0 (l2b [1;2;3]) 0.


  (* ======================================================================= *)
  (** ** Set element with index to generate a new block *)
  Section SetElement.

    Variable A : Type.
    Variable n : nat.
    
    (** Set element with a constant value. *)
    Definition bset (b : @Block A n) (i : nat) (x : A) : @Block A n :=
      let 'mkBlock l H := b in
        mkBlock (lst_chg l i x) (lst_chg_height l i n x H).
    
    (** Set element with a function. *)
    Definition bsetf (b : @Block A n) (i : nat) (f : nat -> A) : @Block A n :=
      let 'mkBlock l H := b in
        mkBlock (lst_chgf l i f) (lst_chgf_height l n i f H).
     
  End SetElement.
  
  Arguments bset {A n}.
  Arguments bsetf {A n}.
  
  Compute bset [1;2;3] 1 4.
  Compute bsetf [1;2;3] 1 (fun i => i + 10).


  (* ======================================================================= *)
  (** ** Mapping of a block *)
  
  Section Map.
    
    Variable A B : Type.
    Variable n : nat.
    Variable f : A -> B.
    
    Definition bmap (b : @Block A n) : @Block B n.
      refine (mkBlock (map f (Bdata b)) _).
      rewrite map_length. apply Bdata_length.
    Defined.

  End Map.

  Arguments bmap {A B n}.
  
  Compute bmap (fun i => Nat.even i) [1;2;3].
  

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

  Arguments bmap2 {A B C n}.
  
  Compute bmap2 (fun i j => i + j) [1;2;3] [4;5;6].
  

  (* ======================================================================= *)
  (** ** map2 with same base type *)
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

End Block.



(* ######################################################################### *)
(** * Matrix is composion of block *)

Module Matrix.

  Export Block.
  
  (* ======================================================================= *)
  (** ** Matrix of dim n1 *)
  
  Section Mat1.
    
    Variable A : Type.
    Variable A0 : A.
  
    Definition Mat1 {n1} := @Block A n1.
    
    Definition mat1zero n1 : Mat1 := bzero A0 n1.
    
  End Mat1.
  
  Arguments Mat1 {A n1}.
  Arguments mat1zero {A}.

  Section Test.
  
    Check [1;2] : Mat1.
    Compute mat1zero 0 3.
    
  End Test.
  
  
  (* ======================================================================= *)
  (** ** Matrix of dim n1*n2 *)
  
  Section Mat2.
    
    Variable A : Type.
    Variable A0 A1 : A.

    Definition Mat2 {n1 n2} := @Block (@Mat1 A n2) n1.
    
    Definition mat2zero n1 n2 : Mat2 := bzero (mat1zero A0 n2) n1.
    
    (* --------------------------------------------------------------------- *)
    (** *** Get element *)
    Section GetElement.

      Definition bget2 {n1 n2} (b : @Mat2 n1 n2) (i1 i2 : nat) 
        : A := bget A0 (bget (mat1zero A0 n2) b i1) i2.
      
    End GetElement.
    
    (* --------------------------------------------------------------------- *)
    (** *** Unit matrix *)
    Section UnitMatrix.
      
      Variable n : nat.
      
      Let genlst := fun i => list_unit A0 A1 n i.
      
      Let genBlk (i : nat) : @Mat1 A n :=
        mkBlock (genlst i) (list_unit_length A A0 A1 n i).
      
      
      Fixpoint mat2unit_aux n : Block :=
        match n with
        | 0 => genBlk n
        | S n => ? genBlk n
        end. @Mat2 n n.
      
      Check map
      
      Definition mat2unit : @Mat2 n n.
        refine (mkBlock (genlst i) _).
        unfold genlst. apply list_unit_length.
      Defined.
      
      Print genBlk.
      
      
      Check (mkBlock (genlst
      
      Check       
      Check list_unit.
      Fixpoint mat2unit n : @Mat2 n n.
    
    End UnitMatrix.
    
    

  End Mat2.
  
  Arguments Mat2 {A n1 n2}.
  Arguments mat2zero {A}.
  Arguments bget2 {A} _ {n1 n2}.
  
  Section Test.
    
    Let mat1 : Mat2 := [l2b [1;2]; l2b [3;4]; l2b [4;5]].
    Let mat2 : Mat2 := mat2zero 0 2 3.
    
    Compute bget2 0 mat1 0 0.
    Compute bget2 0 mat1 0 1.
    Compute bget2 0 mat1 0 2.
    Compute bget2 0 mat1 1 0.
    Compute bget2 0 mat1 1 1.
    Compute bget2 0 mat1 1 2.
    Compute bget2 0 mat1 2 0.
    Compute bget2 0 mat1 2 1.
    Compute bget2 0 mat1 2 2.
    
  End Test.
  
  
  (* ======================================================================= *)
  (** ** Matrix of dim n1*n2*n3 *)
  
  Section Mat3.
    
    Variable A : Type.
    Variable A0 : A.

    Definition Mat3 {n1 n2 n3} := @Block (@Mat2 A n2 n3) n1.
    
    Definition mat3zero n1 n2 n3 : Mat3 := bzero (mat2zero A0 n2 n3) n1.
    
    (* --------------------------------------------------------------------- *)
    (** *** Get element *)
    Section GetElement.
    
      Variable n1 n2 n3 : nat.
      Variable b : @Mat3 n1 n2 n3.
      Variable i1 i2 i3 : nat.
      Check bget2 _ b i1 i2.
      Check (bget _ (bget2 _ b i1 i2) i3).
      Check (bget A0 (bget2 _ b i1 i2) i3).
      Check (bget A0 (bget2 _ b i1 i2) i3).
      Check bget2 (mat1zero A0 n3) b i1 i2.
      Check (bget A0 (bget2 (mat1zero A0 n3) b i1 i2) i3).

      Definition bget3 {n1 n2 n3} (b : @Mat3 n1 n2 n3) (i1 i2 i3 : nat)
        : A := bget A0 (bget2 (mat1zero A0 n3) b i1 i2) i3.
      
    End GetElement.
  
  End Mat3.
  
  Arguments Mat3 {A n1 n2 n3}.
  Arguments mat3zero {A}.
  Arguments bget3 {A} _ {n1 n2 n3}.

  Section Test.
    
    (* 2*2*2 *)
    Let mat1 : Mat3 := [
      l2b [l2b [1;2]; l2b [3;4]]; 
      l2b [l2b [5;6]; l2b [7;8]]
      ].
    
    (* 3*2*1 *)
    Let mat2 : Mat3 := [ 
      l2b [l2b [1]; l2b [2]]; 
      l2b [l2b [3]; l2b [4]]; 
      l2b [l2b [5]; l2b [6]]].
    
    Compute mat3zero 0 2 3 4.
    
    Compute bget3 0 mat2 0 0 0.
    Compute bget3 0 mat2 0 1 0.
    Compute bget3 0 mat2 1 0 0.
    Compute bget3 0 mat2 1 1 0.
    Compute bget3 0 mat2 2 0 0.
    Compute bget3 0 mat2 2 1 0.
    
    
  End Test.
  

End Matrix.



