(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension for general list list
  author    : ZhengPu Shi
  date      : 2021.12
  
  history   :
  
  1. 2021.12, by ZhengPu Shi.
     first version
  
  2. 2022.05, by ZhengPu Shi.
     split big file into small modules

  3. 2022.13, by ZhengPu Shi.
     setoid version
  
 *)


Require Export SetoidListExt.

Generalizable Variables A B C Aeq Beq Ceq Aadd Aopp Amul Ainv.


(* ======================================================================= *)
(** ** width of a dlist (list (list A)) *)

Section dlist_width.
  
  Context {A : Type}.

  (** A proposition that every list of a list list has same length *)
  Definition width {A:Type} (dl : list (list A)) (n : nat) : Prop :=
    Forall (fun l => length l = n) dl.

  (** width property should be kept by its child structure *)
  Lemma cons_width_iff : forall (l : list A) dl n,
      width (l :: dl) n <-> length l = n /\ width dl n.
  Proof.
    intros. split; intros; inversion H; auto.
    constructor; auto.
  Qed.

  (** width property should be kept by every child element *)
  Lemma width_imply_in_length : forall (l : list A) dl n, 
      width dl n -> In l dl -> length l = n.
  Proof.
    intros. induction dl. inv H0.
    apply cons_width_iff in H; destruct H. apply in_inv in H0. destruct H0.
    + subst. auto.
    + apply IHdl; auto.
  Qed.

  (** app operation won't change width property *)
  Lemma app_width : forall (dl1 : list (list A)) dl2 n, 
      width (dl1 ++ dl2) n <-> width dl1 n /\ width dl2 n.
  Proof.
    unfold width in *.
    induction dl1; intros; split; intros; simpl in *; inv H; auto.
    - apply IHdl1 in H3 as []. split; auto.
    - inv H0. constructor; auto. apply IHdl1. auto.
  Qed.

  (** rev operation won't change width property *)
  Lemma rev_width : forall (dl : list (list A)) n, width (rev dl) n -> width dl n.
  Proof.
    unfold width in *.
    induction dl; simpl; intros; auto.
    apply app_width in H. destruct H. inv H0. constructor; auto.
  Qed.

  (** repeat generated list list will keep width property same as seed element *)
  Lemma repeat_width : forall (l : list A) n k,
      length l = k -> width (repeat l n) k.
  Proof.
    unfold width. induction n; intros; simpl; auto.
  Qed.

  (** width promise i-th row has same length *)
  Lemma width_imply_nth_length : forall i c (dl : list (list A)), 
      i < length dl -> width dl c -> length (nth i dl []) = c.
  Proof.
    unfold width. intros i c dl. revert i c.
    induction dl; intros; simpl in *. lia.
    inv H0. destruct i; auto. apply IHdl; auto. lia.
  Qed.

  (** map width law *)
  Lemma width_map : forall (f: nat -> list A) (rowIdxs:list nat) c,
      (forall i, length (f i) = c) -> width (map f rowIdxs) c.
  Proof.
    unfold width. intros f idxs. induction idxs; simpl; auto.
  Qed.

End dlist_width.


(* ======================================================================= *)
(** ** Set element with a constant value *)
Section SetByConstant.
  
  (* --------------------------------------------------------------------- *)
  (** *** Modify a list list *)
  
  (** Definition *)
  Fixpoint dlst_chg {A} (dl : list (list A)) (ri ci : nat) (x : A) 
    : list (list A) :=
    match dl, ri with
    | [], _ => []
    | l :: dl, 0 => (lst_chg l ci x) :: dl
    | l :: dl, S ri => l :: (dlst_chg dl ri ci x)
    end. 
  
  (* Compute dlst_chg [] 0 1 9.
  Compute dlst_chg [[1;2];[3;4;5]] 0 1 9.
  Compute dlst_chg [[1;2];[3;4;5]] 1 1 9.
  Compute dlst_chg [[1;2];[3;4;5]] 2 1 9.
  Compute dlst_chg [[1;2];[3;4;5]] 1 5 9.
   *)
  
  (** Length property *)
  Lemma dlst_chg_length : forall {A} dl ri r ci x, 
      length dl = r ->
      length (@dlst_chg A dl ri ci x) = r.
  Proof.
    intros A dl; induction dl; auto. destruct ri; intros; auto; simpl in *.
    destruct r; auto. easy.
  Qed.
  
  (** Width property *)
  Lemma dlst_chg_width : forall {A} dl ri c ci x, 
      width dl c ->
      width (@dlst_chg A dl ri ci x) c.
  Proof.
    unfold width. intros A dl; induction dl; auto.
    destruct ri; intros; simpl in *; auto; inv H; constructor; auto.
    apply lst_chg_length; auto.
  Qed.

End SetByConstant.


(* ======================================================================= *)
(** ** Set element with a generation function *)
Section SetByFunction.

  (** Inner version, ri0 is given position, ri is changing every loop *)
  Fixpoint dlst_chgf_aux {A} (dl : list (list A)) (ri0 ri ci : nat) 
    (f : nat -> nat -> A) 
    : list (list A) :=
    match dl, ri with
    | [], _ => []
    | l :: dl, 0 => (lst_chgf l ci (f ri0)) :: dl
    | l :: dl, S ri => l :: (dlst_chgf_aux dl ri0 ri ci f)
    end. 
  
  (** User version that hide ri0 parameter *)
  Definition dlst_chgf {A} (dl : list (list A)) (ri ci : nat) 
    (f : nat -> nat -> A) 
    : list (list A) :=
    dlst_chgf_aux dl ri ri ci f.
  
  (* Let f_gen := fun (i j : nat) => (i + j + 10).
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 0 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 1 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 2 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 3 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 4 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 0 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 1 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 2 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 3 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 4 f_gen.
   *)
  
  (** Length property *)
  Lemma dlst_chgf_aux_length : forall {A} dl ri r ri0 ci f, 
      length dl = r ->
      length (@dlst_chgf_aux A dl ri0 ri ci f) = r.
  Proof.
    intros A dl; induction dl; auto. destruct ri; auto; simpl; intros.
    destruct r; auto. easy.
  Qed.
  
  Lemma dlst_chgf_length : forall {A} dl r ri ci f, 
      length dl = r ->
      length (@dlst_chgf A dl ri ci f) = r.
  Proof.
    intros. apply dlst_chgf_aux_length. auto.
  Qed.
  
  (** Width property *)
  Lemma dlst_chgf_aux_width : forall {A} dl ri c ri0 ci f, 
      width dl c ->
      width (@dlst_chgf_aux A dl ri0 ri ci f) c.
  Proof.
    unfold width. intros A dl; induction dl; auto. 
    induction ri; intros; simpl in *; auto; inv H; constructor; auto.
    apply lst_chgf_length; auto.
  Qed.
  
  Lemma dlst_chgf_width : forall {A} dl ri c ci f, 
      width dl c ->
      width (@dlst_chgf A dl ri ci f) c.
  Proof.
    intros. apply dlst_chgf_aux_width; auto.
  Qed.

End SetByFunction.


(* ======================================================================= *)
(** ** Set row with a constant value *)
Section SetRowByConstant.
  
  (** Definition *)
  Fixpoint dlst_chgrow {A} (dl : list (list A)) (ri : nat) (x : list A) 
    : list (list A) :=
    match dl, ri with
    | [], _ => []
    | l :: dl, 0 => x :: dl
    | l :: dl, S ri => l :: (dlst_chgrow dl ri x)
    end. 
  
  (*   Compute dlst_chgrow [] 0 [8;9].
  Compute dlst_chgrow [[1;2];[3;4;5]] 0 [8;9].
  Compute dlst_chgrow [[1;2];[3;4;5]] 1 [8;9].
  Compute dlst_chgrow [[1;2];[3;4;5]] 2 [8;9].
   *)  
  (** Length property *)
  Lemma dlst_chgrow_length : forall {A} dl ri r x, 
      length dl = r ->
      length (@dlst_chgrow A dl ri x) = r.
  Proof.
    intros A dl; induction dl; auto. destruct ri; auto; intros; simpl in *.
    destruct r; auto. easy.
  Qed.
  
  (** Width property *)
  Lemma dlst_chgrow_width : forall {A} dl ri c x,
      length x = c ->
      width dl c ->
      width (@dlst_chgrow A dl ri x) c.
  Proof.
    unfold width; intros A dl; induction dl; auto. 
    induction ri; intros; simpl in *; inv H0; constructor; auto.
  Qed.

End SetRowByConstant.


(* ======================================================================= *)
(** ** Set row with a generation function *)
Section SetRowByFunction.
  
  (** Inner version, ri0 is given position, ri is changing every loop *)
  Fixpoint dlst_chgrowf_aux {A} (dl : list (list A)) (ri0 ri : nat) 
    (f : nat -> list A) 
    : list (list A) :=
    match dl, ri with
    | [], _ => []
    | l :: dl, 0 => (f ri0) :: dl
    | l :: dl, S ri => l :: (dlst_chgrowf_aux dl ri0 ri f)
    end. 
  
  (** User version that hide ri0 parameter *)
  Definition dlst_chgrowf {A} (dl : list (list A)) (ri : nat) 
    (f : nat -> list A) 
    : list (list A) :=
    dlst_chgrowf_aux dl ri ri f.
  
  (*   Let f_gen := fun (i : nat) => [i+10;i+11;i+12].
  Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 f_gen.
  Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 f_gen.
  Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 2 f_gen.
  Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 3 f_gen.
   *) 
  
  (** Length property *)
  Lemma dlst_chgrowf_aux_length : forall {A} dl ri r ri0 f, 
      length dl = r ->
      length (@dlst_chgrowf_aux A dl ri0 ri f) = r.
  Proof.
    intros A dl; induction dl; auto. induction ri; auto.
    intros. simpl. destruct r; auto. easy.
  Qed.
  
  Lemma dlst_chgrowf_length : forall {A} dl r ri f, 
      length dl = r ->
      length (@dlst_chgrowf A dl ri f) = r.
  Proof.
    intros. apply dlst_chgrowf_aux_length. auto.
  Qed.
  
  (** Width property *)
  Lemma dlst_chgrowf_aux_width : forall {A} dl ri c ri0 f, 
      length (f ri0) = c ->
      width dl c ->
      width (@dlst_chgrowf_aux A dl ri0 ri f) c.
  Proof.
    unfold width; intros A dl; induction dl; auto. 
    induction ri; intros; simpl in *; auto; inv H0; constructor; auto.
  Qed.
  
  Lemma dlst_chgrowf_width : forall {A} dl ri c f, 
      length (f ri) = c ->
      width dl c ->
      width (@dlst_chgrowf A dl ri f) c.
  Proof.
    intros. apply dlst_chgrowf_aux_width; auto.
  Qed.

End SetRowByFunction.


(* ======================================================================= *)
(** ** Properties of dlist *)
Section props_dlist.

  Context `{Equiv_Aeq:Equivalence A Aeq}.
  Context `{A0:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  Open Scope nat.

  (** ** Length of a empty dlist *)
  Lemma dlist_h0_iff : forall (dl : list (list A)), 
      length dl = 0 -> dl == nil.
  Proof.
    destruct dl; simpl; auto. intros H; easy.
  Qed.
  
  (** Two list list equal iff all nth nth visit equal *)
  Lemma dlist_eq_iff_nth_nth :
    forall r c (dl1 dl2 : list (list A))
      (H1 : length dl1 = r) (H2 : length dl2 = r)
      (H3 : width dl1 c) (H4 : width dl2 c),
      dl1 == dl2 <->
        (forall (ri ci : nat), ri < r -> ci < c -> 
                        (nth ci (nth ri dl1 []) A0 == nth ci (nth ri dl2 []) A0))%A.
  Proof.
    intros; split; intros.
    - rewrite H. easy.
    - apply (list_eq_iff_nth [] _ dl1 dl2 H1 H2). intros. subst.
      rewrite (list_eq_iff_nth) with (n:=c); auto;
        apply width_imply_nth_length; auto. lia.
  Qed.

  (** dlist_eq is decidable *)
  Context `{Aeq_dec : Decidable A Aeq}.
  Lemma dlist_eq_dec : forall (dl1 dl2 : list (list A)), {dl1 == dl2} + {~(dl1 == dl2)}.
  Proof.
    apply list_eq_dec.
    apply list_eq_dec. apply Aeq_dec.
  Qed.

End props_dlist.



(* ======================================================================= *)
(** ** a dlist with same element nil *)
Section dnil.
  
  Context `{M:Monoid}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  Open Scope nat.
  
  (** a list list that every list is nil, named as dnil *)
  Fixpoint dnil n : list (list A) :=
    match n with
    | O => nil
    | S n' => nil :: (dnil n')
    end.

  (** dnil's length law *)
  Lemma dnil_length : forall n, length (dnil n) = n.
  Proof.
    induction n; simpl; auto.
  Qed.

  (** dnil's width law *)
  Lemma dnil_width : forall n, width (dnil n) 0.
  Proof.
    unfold width; induction n; simpl; auto.
  Qed.
  
  (** dnil equal to append two child dnil *)
  Lemma dnil_app : forall n1 n2, 
      dnil (n1 + n2) == dnil n1 ++ dnil n2.
  Proof.
    induction n1,n2; simpl; try easy.
    - rewrite app_nil_r. rewrite Nat.add_0_r. easy.
    - rewrite IHn1. simpl. easy.
  Qed.

  (** width dl is zero imply it is a dnil *)
  Lemma dlist_w0_eq_dnil : forall (dl : list (list A)), 
      width dl 0 -> dl == dnil (length dl).
  Proof.
    unfold width; induction dl; simpl; auto.
    intros. inv H. apply cons_aeq_mor; auto. 
    apply length_zero_iff_nil; auto.
  Qed.

  (** rev a dnil is itself *)
  Lemma dnil_rev : forall n, rev (dnil n) == dnil n.
  Proof.
    induction n; simpl; auto. rewrite IHn. clear IHn. induction n; simpl; auto.
  Qed.

End dnil.


(* ======================================================================= *)
(** ** map2 *)
Section map2.

  Context {A B C : Type} {Aeq : relation A} {Beq:relation B} {Ceq:relation C}.
  Context {EqEquivA:Equivalence Aeq}.
  Context {EqEquivB:Equivalence Beq}.
  Context {EqEquivC:Equivalence Ceq}.
  Variable f : A -> B -> C.
  
  Infix "==" := (eqlistA (eqlistA Ceq)).
  Open Scope nat.

  (** map2 dnil dl = dnil *)
  Lemma map2_dnil_l : forall dl n, 
      length dl = n -> map2 (map2 f) (dnil n) dl == dnil n.
  Proof.
    intros. gd dl. induction n; intros; simpl; try easy.
    destruct dl. inversion H. inversion H. rewrite H1. auto.
  Qed.

  (** map2 dl dnil = dnil *)
  Lemma map2_dnil_r : forall dl n, 
      length dl = n -> map2 (map2 f) dl (dnil n) == dnil n.
  Proof.
    intros. gd dl. induction n; intros; simpl; try easy.
    - rewrite map2_nil_r. easy.
    - destruct dl. easy. simpl. rewrite IHn; auto. rewrite map2_nil_r. easy.
  Qed.

End map2.


(* ======================================================================= *)
(** ** Convert between row and col. eg, [1;2;3] <-> [[1];[2];[3]] *)
Section convert_row_and_col.

  Context `{M:Monoid}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  
  (** Convert a list to a dlist, it looks like converting a row to a column. *)
  Fixpoint row2col (l : list A) : list (list A) :=
    match l with
    | [] => []
    | x :: tl => [x] :: (row2col tl)
    end.
  
  (** row2col length law *)
  Lemma row2col_length : forall l, length (row2col l) = length l.
  Proof.
    induction l; simpl; intros; auto.
  Qed.
  
  (** row2col width law *)
  Lemma row2col_width : forall l, width (row2col l) 1.
  Proof.
    unfold width; induction l; simpl; intros; auto.
  Qed.

  Lemma nth_row2col : forall l i,
      i < length l ->
      (nth i (row2col l) [] == [nth i l A0])%list.
  Proof.
    induction l.
    - intros. simpl in *. lia.
    - intros. simpl in *. destruct i; try easy.
      apply IHl. auto with arith.
  Qed.
  
  (** Convert a dlist to a list which contain head element, it looks like 
    converting a column to a row. *)
  Fixpoint col2row (dl : list (list A)) : list A :=
    match dl with
    | [] => []
    | l :: tl => (hd A0 l) :: (col2row tl)
    end.
  
  (** Convert a dlist to list then convert it to a dlist, equal to original dlist. *)
  Lemma row2col_col2row : forall (dl : list (list A)),
      width dl 1 -> row2col (col2row dl) == dl.
  Proof.
    unfold width; induction dl; simpl; auto; intros. inv H.
    apply cons_aeq_mor; auto.
    destruct a; simpl in *; try easy. inv H2.
    apply List.length_zero_iff_nil in H0. subst. easy.
  Qed.
  
  (** Convert a list to dlist then convert it to a list, equal to original 
    list. *)
  Lemma col2row_row2col : forall (l : list A), 
      (col2row (row2col l) == l)%list.
  Proof.
    induction l; simpl; auto; intros. rewrite IHl. easy.
  Qed.
  
End convert_row_and_col.


(* ======================================================================= *)
(** ** head column of a dlist *)
Section hdc.
  Context {A : Type} {A0 : A}.
  
  (** Get head column of a dlist *)
  Fixpoint hdc (dl : list (list A)) : list A :=
    match dl with
    | [] => []
    | l :: tl => (hd A0 l) :: (hdc tl)
    end.
  
  (** hdc length law *)
  Lemma hdc_length : forall dl, length (hdc dl) = length dl.
  Proof.
    induction dl; simpl; auto.
  Qed.
  
End hdc.

Arguments hdc {A}.


(* ======================================================================= *)
(** ** tail columns of a dlist *)
Section tlc.
  
  Context {A : Type}.
  
  (** Get tail columns of a dlist *)
  Fixpoint tlc (dl : list (list A)) : list (list A) :=
    match dl with
    | [] => []
    | l :: tl => (tail l) :: (tlc tl)
    end.
  
  (** tlc length law *)
  Lemma tlc_length : forall dl, length (tlc dl) = length dl.
  Proof.
    induction dl; simpl; auto.
  Qed.
  
  (** tlc width law when width equal to 0 *)
  Lemma tlc_width0 : forall dl, 
      width dl 0 -> width (tlc dl) 0.
  Proof.
    unfold width; induction dl; simpl; auto. intros. inv H; constructor; auto.
    apply List.length_zero_iff_nil in H2. subst. auto.
  Qed.
  
  (** tlc width law when width not equal to 0 *)
  Lemma tlc_widthS : forall dl c, 
      width dl (S c) -> width (tlc dl) c.
  Proof.
    unfold width; induction dl; simpl; auto.
    intros. inv H; constructor; auto.
    destruct a; auto. easy.
  Qed.
  
End tlc.


(* ======================================================================= *)
(** ** construct a dlist with a list and a dlist by column *)
Section consc.

  Context `{Equiv_Aeq:Equivalence A Aeq} {A0:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** Construct a dlist by column with a list and a dlist *)
  Fixpoint consc (l : list A) (dl : list (list A)) : list (list A) :=
    match l, dl with
    | xl :: tl, xdl :: tdl => (xl :: xdl) :: (consc tl tdl)
    | _, _ => []
    end.

  Lemma consc_aeq_mor :
    Proper (eqlistA Aeq ==> eqlistA (eqlistA Aeq) ==> eqlistA (eqlistA Aeq)) consc.
  Proof.
    unfold Proper, respectful.
    induction x; intros.
    - destruct x,y0,y; simpl; try easy.
    - destruct x0,y0,y; simpl; try easy.
      apply cons_eq_iff in H as [->], H0 as [->].
      apply cons_aeq_mor; auto. easy.
  Qed.
  
  Global Existing Instance consc_aeq_mor.

  
  (** consc_eq, seems like f_equal *)
  Lemma consc_eq_iff : forall (l1 l2 : list A) (dl1 dl2 : list (list A)) n
                         (H1:length l1 = n) (H2:length l2 = n)
                         (H3:length dl1 = n) (H4:length dl2 = n),
      consc l1 dl1 == consc l2 dl2 <-> (l1 == l2)%list /\ dl1 == dl2.
  Proof.
    induction l1.
    - intros. simpl in *. subst. apply List.length_zero_iff_nil in H4,H3,H2.
      subst. easy.
    - intros. destruct l2,dl1,dl2; simpl in *; subst; try easy.
      inv H2. inv H3. inv H4. split; intros.
      + inv H. rewrite IHl1 in H8; auto. inv H8. inv H6.
        rewrite H,H3,H8,H10. easy.
      + inv H. inv H3. inv H4. rewrite H7,H6. apply cons_eq_iff; split; try easy.
        rewrite IHl1; auto.
  Qed.
  
  (** consc length law *)
  Lemma consc_length : forall l dl r,
      length l = r -> length dl = r ->
      length (consc l dl) = r.
  Proof.
    induction l,dl; simpl; intros; auto. destruct r. inversion H. f_equal.
    inversion H. inversion H0. subst. apply IHl; auto.
  Qed.
  
  (** consc width law *)
  Lemma consc_width : forall l dl c,
      length l = length dl -> width dl c ->
      width (consc l dl) (S c).
  Proof.
    unfold width; induction l,dl; simpl; intros; auto.
    inv H. inv H0. constructor; auto.
  Qed.
  
  (** consc with hdc and tlc of a dnil generate lzero *)
  Lemma consc_hdc_tlc_width0 : forall dl r, 
      length dl = r -> width dl 0 -> 
      consc (hdc A0 dl) (tlc dl) == row2col (repeat A0 r).
  Proof.
    unfold width; induction dl; simpl; intros; subst; try easy.
    inv H0. apply List.length_zero_iff_nil in H2. subst. simpl.
    rewrite IHdl; auto. easy.
  Qed.
  
  (** consc with hdc and tlc of a dlist generate itself *)
  Lemma consc_hdc_tlc_widthS : forall dl c, 
      width dl (S c) ->
      consc (hdc A0 dl) (tlc dl) == dl.
  Proof.
    unfold width; induction dl; simpl; intros; auto. inv H.
    apply cons_eq_iff; split; auto.
    - destruct a; simpl in *. easy. easy.
    - apply IHdl with (c:=c). auto.
  Qed.

  (** consc decompose.
    x1::l1 ++ l2::dl2 = (x::l2) :: (l1 ++ dl2)  *)
  Lemma consc_decompose : forall x1 l1 l2 dl2,
      consc (x1::l1) (l2::dl2) == (x1::l2) :: (consc l1 dl2).
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** repeat (x :: l) decomposition *)
  Lemma repeat_consr : forall l x n,
      repeat (x :: l) n == consc (repeat x n) (repeat l n).
  Proof.
    induction n; simpl; auto. rewrite IHn. easy.
  Qed.

End consc.


(* ======================================================================= *)
(** ** Append two objects of dlist type to one object of dlist *)
Section dlist_app.
  
  Context {A : Type}.
  
  (** dlist append by row *)
  Definition dlappr := app.
  
  (** dlist apend by column *)
  Fixpoint dlappc (dl1 dl2 : list (list A)) : list (list A) :=
    match dl1, dl2 with
    | l1 :: tl1, l2 :: tl2 => (app l1 l2) :: (dlappc tl1 tl2)
    | _, _ => []
    end.

End dlist_app.

Notation "l @@ r" := (dlappc l r) (at level 40) : dlist_scope.


(* ======================================================================= *)
(** ** Zero dlist *)
Section dlzero.

  Context `{Equiv_Aeq:Equivalence A Aeq} {A0:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** dlist constructed by repeated lzero, named as dlzero *)
  Definition dlzero r c := repeat (lzero A0 c) r.

  (** dlzero rewrite *)
  Lemma dlzero_rw : forall r c, repeat (lzero A0 c) r = dlzero r c.
  Proof.
    easy.
  Qed.
  
  (** dlzero with S r rows could be splited to two parts *)
  Lemma dlzero_Sr : forall {r c}, dlzero (S r) c == (lzero A0 c) :: (dlzero r c).
  Proof.
    intros. simpl. cbn. easy.
  Qed.
  
  (** dlzero with 0 rows equal to dnil *)
  Lemma dlzero_dnil : forall {c}, dlzero c 0 == dnil c.
  Proof.
    induction c; simpl; try easy. rewrite <- IHc. easy.
  Qed.
  
  (** dlzero heigth law *)
  Lemma dlzero_length : forall {r c}, length (dlzero r c) = r.
  Proof.
    intros. apply repeat_length.
  Qed.
  
  (** dlzero width law *)
  Lemma dlzero_width : forall {r c}, width (dlzero r c) c.
  Proof.
    unfold width, dlzero; induction r; intros; simpl; auto. constructor; auto.
    apply lzero_length.
  Qed.
  
  (** dlzero with 0 rows equal to dnil *)
  Lemma dlzero_w0_eq_dnil : forall r, (dlzero r 0) == dnil r.
  Proof. 
    induction r; try easy. unfold dlzero in *. simpl in *. rewrite IHr. easy.
  Qed.
  
  (** append two dlzeros by row equal to whole *)
  Lemma dlzero_app_row : forall r1 r2 c,
      dlzero r1 c ++ dlzero r2 c == dlzero (r1 + r2) c.
  Proof.
    unfold dlzero. intros. rewrite repeat_app. easy.
  Qed.
  
  (** append two dlzeros by column equal to whole *)
  Lemma dlzero_app_col : forall r c1 c2,
      ((dlzero r c1) @@ (dlzero r c2))%dlist == dlzero r (c1 + c2).
  Proof.
    induction r; intros; simpl; try easy. unfold dlzero,lzero in *.
    rewrite IHr. simpl. rewrite repeat_app. easy.
  Qed.

End dlzero.

Arguments dlzero {A}.


(* ======================================================================= *)
(** ** transpose a dlist *)
Section dltrans.

  Context `{Equiv_Aeq:Equivalence A Aeq} {A0:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** Transposition of a dlist *)
  (* Idea: fetch row as column one bye one, generate a dlist with c rows if 
      given c is <= column of input dlist.

      Note that, we give c to support dlist_0_c situation.
      eg: 
      [] 3 => [[];[];[]]
      [[];[];[]] 0 => []
   *)
  Fixpoint dltrans (dl : list (list A)) (c : nat) : list (list A) :=
    match dl with
    | [] => @dnil A c
    | l :: tl => consc l (dltrans tl c)
    end.

  Lemma dltrans_aeq_mor :
    Proper (eqlistA (eqlistA Aeq) ==> eq ==> eqlistA (eqlistA Aeq)) dltrans.
  Proof.
    unfold Proper, respectful.
    induction x; intros.
    - destruct y; subst; easy.
    - destruct y. easy. inv H. simpl. rewrite H4. rewrite (IHx y); easy.
  Qed.

  Global Existing Instance dltrans_aeq_mor.

  (** dltrans length law *)
  Lemma dltrans_length : forall dl c, 
      width dl c ->
      length (dltrans dl c) = c.
  Proof.
    induction dl; intros; simpl; auto.
    - rewrite dnil_length. auto.
    - inversion H. rewrite consc_length with (r:=c); auto.
  Qed.
  
  (** dltrans width law *)
  Lemma dltrans_width : forall dl r c, 
      length dl = r -> width dl c -> width (dltrans dl c) r.
  Proof.
    unfold width; induction dl; intros; simpl in *; auto.
    - induction c; simpl in *; auto.
    - rewrite <- H. inv H0. apply consc_width.
      + rewrite dltrans_length; auto.
      + apply IHdl; auto. 
  Qed.
  
  (** dltrans dnil = [] *)
  Lemma dltrans_nil : forall n, dltrans (dnil n) 0 == [].
  Proof.
    intros. destruct n; simpl. reflexivity. easy.
  Qed.
  
  (** dltrans consr = consc dltrans *)
  Lemma dltrans_consr : forall dl l c,
      dltrans (l :: dl) c == consc l (dltrans dl c).
  Proof.
    intros. simpl. easy.
  Qed.

  Existing Instance Equivalence_eqlistA.
  Instance Equiv_eqlistA_eqlistA : Equivalence (@eqlistA (list A) (@eqlistA A Aeq)).
  Proof.
    apply Equivalence_eqlistA.
  Qed.

  (** dltrans consc = consr dltrans *)
  Lemma dltrans_consc : forall dl l r c,
      length l = r -> length dl = r -> width dl c ->
      dltrans (consc l dl) (S c) == l :: (dltrans dl c).
  Proof.
    unfold width; induction dl; simpl; intros; subst.
    - destruct l; simpl; try easy.
    - destruct l. easy.
      inv H0. inv H1.
      specialize (IHdl l (length l) (length a) eq_refl H2 H4).
      simpl.
      destruct (dltrans (consc l dl) (S (length a))). easy. inv IHdl.
      rewrite H3,H6. easy.
  Qed.
  
  (** dltrans twice return back *)
  Lemma dltrans_trans : forall dl r c,
      length dl = r -> width dl c ->
      dltrans (dltrans dl c) r == dl.
  Proof.
    induction dl; intros; simpl in *.
    - subst. destruct c; simpl; auto.
    - destruct r. easy. inv H. inv H0.
      unfold width in *.
      rewrite dltrans_consc with (r:=length a);
        auto using dltrans_length, dltrans_width.
      apply cons_aeq_mor; auto. easy.
  Qed.
  
  (** dltrans dlzero<r,c> = dlzero<c,r> *)
  Lemma dltrans_zero : forall r c,
      dltrans (dlzero A0 r c ) c == dlzero A0 c r.
  Proof.
    induction r; intros; simpl; auto. rewrite dlzero_dnil; easy.
    unfold dlzero in *; simpl in *. rewrite IHr.
    rewrite repeat_consr. easy.
  Qed.
  
End dltrans.


(* ======================================================================= *)
(** ** dlist unit, like a identity matrix *)
Section dlunit.

  Context `{Equiv_Aeq:Equivalence A Aeq} {A0 A1:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** Build a identity matrix with list list. *)
  (* there are 4 parts of a dlunit [n x n]: 
      left top element [1 x 1], 
      right top list [1 x (n-1)], 
      left bottom list [(n-1) x 1],
      right bottom square is another small dlunit [(n-1) x (n-1)] *)
  Fixpoint dlunit (n : nat) : list (list A) :=
    match n with
    | O => []
    | S n0 => (A1 :: (repeat A0 n0)) :: (consc (repeat A0 n0) (dlunit n0))
    end.
  
  (** dlunit length law *)
  Lemma dlunit_length : forall {n}, length (dlunit n) = n.
  Proof.
    induction n; simpl; auto. f_equal.
    rewrite consc_length with (r:=n); auto. apply repeat_length.
  Qed.
  
  (** dlunit width law *)
  Lemma dlunit_width : forall {n}, width (dlunit n) n.
  Proof.
    unfold width; induction n; simpl; auto. constructor.
    - simpl. f_equal. apply repeat_length.
    - apply consc_width; auto. rewrite repeat_length, dlunit_length; auto.
  Qed.
  
  (** transpose dlunit keep unchanged *)
  Lemma dltrans_dlunit : forall {n}, 
      let u := dlunit n in
      dltrans u n == u.
  Proof.
    simpl. induction n; simpl; try easy.
    assert ((dltrans (consc (repeat A0 n) (dlunit n)) (S n)) ==
              (repeat A0 n) :: (dltrans (dlunit n) n)).
    { apply dltrans_consc with (r:=n).
      apply repeat_length. apply dlunit_length. apply dlunit_width. }
    destruct (dltrans (consc (repeat A0 n) (dlunit n)) (S n)). easy.
    inv H. rewrite H3,H5,IHn. easy.
  Qed.

End dlunit.

Arguments dlunit {A}.


(* ======================================================================= *)
(** ** map of dlist with f : A -> B *)
Section dmap_A_B.
  
  Context `{Equiv_Aeq:Equivalence A Aeq}.
  Context `{Equiv_Beq:Equivalence B Beq}.
  Variable f : A -> B.
  Infix "==" := Beq : A_scope.
  Infix "==" := (eqlistA Beq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Beq)).
  
  (** map operation to dlist *)
  Definition dmap dl := map (map f) dl.

  (** dmap is a proper morphism *)
  Context {fProper : (Proper (Aeq ==> Beq) f)}.
  Lemma dmap_aeq_mor : Proper (eqlistA (eqlistA Aeq) ==> eqlistA (eqlistA Beq)) dmap.
  Proof.
    unfold Proper, respectful.
    induction x; destruct y; intros; simpl; try easy. inv H.
    rewrite H3, (IHx y); easy.
  Qed.

  Global Existing Instance dmap_aeq_mor.

  (** dmap length law *)
  Lemma dmap_length : forall dl, length (dmap dl) = length dl.
  Proof.
    induction dl; simpl; auto.
  Qed.
  
  (** dmap width law *)
  Lemma dmap_width : forall dl n, 
      width dl n <-> width (dmap dl) n.
  Proof.
    unfold width; induction dl; intros; split; intros; simpl in *; try easy.
    - inv H. constructor. apply map_length. apply IHdl. auto.
    - inv H. constructor. rewrite map_length. auto.
      apply IHdl. auto.
  Qed.
  
  (** dmap effect equal to map to first head and dmap to tail rows *) 
  Lemma dmap_cons : forall l dl, dmap (l :: dl) == (map f l) :: (dmap dl).
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** dmap distributive law by append *)
  Lemma dmap_app : forall dl1 dl2,
      dmap (dl1 ++ dl2) == (dmap dl1) ++ (dmap dl2).
  Proof.
    induction dl1; destruct dl2; simpl in *; rewrite ?app_nil_r; try easy.
    rewrite IHdl1. easy.
  Qed.
  
  (** dmap dnil = dnil *)
  Lemma dmap_dnil : forall n, dmap (dnil n) == dnil n.
  Proof.
    induction n; simpl; try easy. rewrite IHn. easy.
  Qed.
  
End dmap_A_B.


(* ======================================================================= *)
(** ** map of dlist with f : A -> B *)
Section dmap_A_B.
  Context {A:Type} `{Equiv_Beq:Equivalence B Beq}.
  Infix "==" := Beq : A_scope.
  Infix "==" := (eqlistA (eqlistA Beq)) : dlist_scope.

  (** dmap extensional law  *)
  Lemma dmap_ext : forall dl (f g : A -> B) (H : forall a, f a == g a),
      (dmap f dl == dmap g dl)%dlist.
  Proof.
    intros. unfold dmap.
    apply map_ext. intros. induction a; simpl; auto.
  Qed.
  
End dmap_A_B.


(* ======================================================================= *)
(** ** map of dlist with f : A -> A *)
Section dmap_A_A.
  Context `{Equiv_Aeq:Equivalence A Aeq} {A0:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).

  (** dmap (fun x => A0) dl = dlzero A0 r c *)

  Lemma dmap_eq_zero : forall {r c} dl,
      length dl = r -> width dl c ->
      dmap (fun (x:A) => A0) dl == dlzero A0 r c.
  Proof.
    intros. unfold dmap,dlzero.
    
    (* Note that, use "map_eq_zero" cannot prove this lemma.
       Although this method looks very simple. *)
    (* apply map_eq_zero; auto. intros. apply map_eq_zero; try easy. *)
    
    revert r c H H0.
    induction dl; intros; simpl in *.
    - subst. easy.
    - destruct r; try easy. inv H. inv H0. simpl. apply cons_aeq_mor.
      + apply map_eq_zero; auto. easy.
      + apply IHdl; auto.
  Qed.

End dmap_A_A.


(* ======================================================================= *)
(** ** map2 of dlist *)
Section dmap2.

  Context {A B : Type} `{Equiv_Ceq:Equivalence C Ceq}.
  Variable f : A -> B -> C.
  Infix "==" := (eqlistA (eqlistA Ceq)).
  
  (** map operation to two dlists *)
  Definition dmap2 dl1 dl2 := map2 (map2 f) dl1 dl2.
  
  (** dmap2 length law *)
  Lemma dmap2_length : forall dl1 dl2,
      length dl1 = length dl2 -> length (dmap2 dl1 dl2) = length dl1.
  Proof.
    induction dl1,dl2; simpl; auto.
  Qed.
  
  (** dmap2 width law *)
  Lemma dmap2_width : forall dl1 dl2 n,
      width dl1 n -> width dl2 n -> width (dmap2 dl1 dl2) n.
  Proof. 
    unfold width; induction dl1; intros; simpl in *; auto.
    destruct dl2; auto. inv H. inv H0. constructor.
    apply map2_length; auto. apply IHdl1; auto.
  Qed.
  
  (** dmap2 and consr *)
  Lemma dmap2_consr : forall dl1 dl2 l1 l2,
      dmap2 (l1 :: dl1) (l2 :: dl2) ==
        (map2 f l1 l2) :: (dmap2 dl1 dl2).
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** dmap2 and consc *)
  Lemma dmap2_consc : forall l1 dl1 l2 dl2 c,
      length l1 = length dl1 ->
      length l2 = length dl2 ->
      width dl1 c ->
      width dl2 c ->
      dmap2 (consc l1 dl1) (consc l2 dl2) ==
        consc (map2 f l1 l2) (dmap2 dl1 dl2).
  Proof.
    unfold width; induction l1,dl1,l2,dl2; simpl; intros; try easy.
    (* destruct r,t; try easy. *)
    inv H. inv H0. inv H1. inv H2. inv H3. inv H4.
    apply cons_aeq_mor; try easy. apply IHl1 with (c:=length l); auto.
  Qed.
  
  (** dmap2 and add *)
  Lemma dmap2_app : forall dla1 dla2 dlb1 dlb2,
      length dla1 = length dlb1 ->
      length dla2 = length dlb2 ->
      dmap2 (dla1 ++ dla2) (dlb1 ++ dlb2) ==
        (dmap2 dla1 dlb1) ++ (dmap2 dla2 dlb2).
  Proof.
    intros. unfold dmap2. apply map2_app; auto.
  Qed.
  
  (** dmap2 dnil dl = dnil *)
  Lemma dmap2_dnil_l : forall dl n,
      length dl = n ->
      dmap2 (dnil n) dl == dnil n.
  Proof.
    intros. unfold dmap2. rewrite map2_dnil_l; easy.
  Qed.

  (** dmap2 dl dnil = dnil *)
  Lemma dmap2_dnil_r : forall dl n,
      length dl = n ->
      dmap2 dl (dnil n) == dnil n.
  Proof.
    intros. unfold dmap2. rewrite map2_dnil_r; easy.
  Qed.

  Lemma dmap2_tail : forall dl1 dl2,
      length dl1 = length dl2 ->
      tl (dmap2 dl1 dl2) == dmap2 (tl dl1) (tl dl2).
  Proof.
    intros. unfold dmap2. apply tail_map2_dlist.
  Qed.

  (** Relationship between dltrans and dmap2 *)
  Lemma dltrans_dmap2 : forall dl1 dl2 c,
      length dl1 = length dl2 ->
      width dl1 c -> width dl2 c ->
      dltrans (dmap2 dl1 dl2) c ==
        dmap2 (dltrans dl1 c) (dltrans dl2 c).
  Proof.
    unfold width; induction dl1; intros; simpl in *; subst.
    rewrite dmap2_dnil_l; auto using dltrans_length. easy.
    destruct dl2; simpl.
    - inv H.
    - inv H. inv H0. inv H1. rewrite IHdl1; auto.
      rewrite dmap2_consc; auto using dltrans_width, dltrans_length; try easy.
      rewrite dltrans_length; auto.
      rewrite dltrans_length; auto.
  Qed.
  
End dmap2.


(* ======================================================================= *)
(** ** dmap2 with same base type *)
Section dmap2_sametype.

  Context `{Aadd:A->A->A}.
  Context `{Equiv_Aeq:Equivalence A Aeq}.
  Infix "+" := Aadd : A_scope.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).

  (** dmap2 is a proper morphism *)
  Context {AaddProper : Proper (Aeq ==> Aeq ==> Aeq) Aadd}.
  Lemma dmap2_aeq_mor :
    let deq := eqlistA (eqlistA Aeq) in
    Proper (deq ==> deq ==> deq) (dmap2 Aadd).
  Proof.
    simpl. intros. unfold dmap2.
    apply (map2_aeq_mor (Aeq:=eqlistA Aeq) (Beq:=eqlistA Aeq)); auto.
    apply (map2_aeq_mor (Aeq:=Aeq) (Beq:=Aeq)); auto.
  Qed.

  Global Existing Instance dmap2_aeq_mor.
  
  Context {Comm : Commutative Aadd Aeq}.
  (** dl1 . dl2 = dl2 . dl1 *)
  Lemma dmap2_comm : forall (dl1 dl2 : list (list A)),
      dmap2 Aadd dl1 dl2 == dmap2 Aadd dl2 dl1.
  Proof.
    induction dl1,dl2; simpl; auto. apply cons_eq_iff; split; auto.
    apply map2_comm.
  Qed.

  (** (dl1 . dl2) . dl3 = dl1 . (dl2 . dl3) *)
  Context {Assoc : Associative Aadd Aeq}.
  Lemma dmap2_assoc : forall (dl1 dl2 dl3 : list (list A)),
      dmap2 Aadd (dmap2 Aadd dl1 dl2) dl3 ==
        dmap2 Aadd dl1 (dmap2 Aadd dl2 dl3).
  Proof.
    induction dl1,dl2,dl3; simpl; auto. apply cons_eq_iff; split; auto.
    apply map2_assoc.
  Qed.
  
  (** dmap2 with dmap of two components *)
  Lemma dmap2_dmap_dmap : forall (f1 f2 g : A -> A) (h : A -> A -> A) 
                            (H : forall x, Aeq (g x) (h (f1 x) (f2 x))) l,
      dmap2 h (dmap f1 l) (dmap f2 l) == dmap g l.
  Proof.
    induction l; simpl; auto. rewrite IHl. apply cons_eq_iff; split; try easy.
    apply map2_map_map. easy.
  Qed.

  (** dmap2 over dmap is homorphism *)
  Lemma dmap2_dmap_hom : forall (Aopp : A -> A)
                           (H : forall a b : A, (Aopp (a + b) == (Aopp a) + (Aopp b))%A)
                           d1 d2,
      dmap2 Aadd (dmap Aopp d1) (dmap Aopp d2) == dmap Aopp (dmap2 Aadd d1 d2).
  Proof.
    intros. revert d2.
    induction d1,d2; simpl; try easy. rewrite IHd1. rewrite map2_map_hom. easy.
    easy.
  Qed.
  
End dmap2_sametype.


(* ======================================================================= *)
(** ** Square Zero dlist *)
Section sdlzero.

  Context `{Equiv_Aeq:Equivalence A Aeq} (A0:A).
  Infix "==" := (eqlistA (eqlistA Aeq)).

  (** Square dlist with element zero *)
  Definition sdlzero n := repeat (repeat A0 n) n.
  
  (** dim(sdl0) = rows(dl0) = cols(dl0) -> sdl0 = dl0 *)
  Lemma sdlzero_eq_dlzero_r : forall r c,
      r = c -> sdlzero r == dlzero A0 r c.
  Proof.
    intros. subst. unfold sdlzero, dlzero. easy.
  Qed.
  
  (** dim(sdl0) = rows(dl0) = cols(dl0) -> sdl0 = dl0 *)
  Lemma sdlzero_eq_dlzero_c : forall r c,
      r = c -> sdlzero c == dlzero A0 r c.
  Proof.
    intros. subst. unfold sdlzero, dlzero. easy.
  Qed.
  
  (** length(sdl0) = dim(sdl0) *)
  Lemma sdlzero_length : forall n, length (sdlzero n) = n.
  Proof.
    intros. apply repeat_length.
  Qed.
  
  (** width(sdl0) = dim(sdl0) *)
  Lemma sdlzero_width : forall n, width (sdlzero n) n.
  Proof.
    intros. unfold sdlzero. induction n. simpl. constructor.
    apply repeat_width. apply repeat_length.
  Qed.
  
End sdlzero.


(* ======================================================================= *)
(** ** dmap2 is considered as dladd *)
Section dladd.

  Context `{AG:AGroup}.
  Infix "+" := Aadd.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** dl + 0 = dl *)
  Lemma dladd_zero_l : forall dl r c, 
      length dl = r -> width dl c ->
      dmap2 Aadd (dlzero A0 r c) dl == dl.
  Proof.
    unfold width, dlzero in *.
    induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - destruct r. easy. inv H. inv H0.
      simpl. apply cons_aeq_mor; auto.
      rewrite map2_zero_l. easy.
  Qed.
  
  (** 0 + dl = dl *)
  Lemma dladd_zero_r : forall dl r c, 
      length dl = r -> width dl c ->
      dmap2 Aadd dl (dlzero A0 r c) == dl.
  Proof.
    intros. rewrite dmap2_comm; auto. apply dladd_zero_l; auto.
  Qed.

End dladd.


(* ======================================================================= *)
(** ** dmap2 is considered as dlsub *)
Section dlsub.

  Context `{AG:AGroup}.
  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  Infix "-" := (fun a b => a + (-b)).
  Infix "==" := (eqlistA (eqlistA Aeq)).

  (* Variable A : Type. *)
  (* Variable A0 : A. *)
  (* Variable opp : A -> A. *)
  (* Variable add : A -> A -> A. *)
  (* Infix "+" := add. *)
  
  (* Variable sub_comm : forall a b, a - b = - (b - a). *)
  (* Variable sub_perm : forall a b c, (a - b) - c = (a - c) - b. *)
  (* Variable sub_assoc : forall a b c, (a - b) - c = a - (b + c). *)
  (* Variable sub_0_l : forall a, A0 - a = - a. *)
  (* Variable sub_0_r : forall a, a - A0 = a. *)
  (* Variable sub_self : forall a, a - a = A0. *)
  
  (** dl1 - dl2 = - (dl2 - dl1) *)
  Lemma dlsub_comm : forall dl1 dl2 c,
      let Asub := fun a b => a + (-b) in
      length dl1 = length dl2 ->
      width dl1 c -> width dl2 c ->
      dmap2 Asub dl1 dl2 == dmap Aopp (dmap2 Asub dl2 dl1).
  Proof.
    induction dl1,dl2; simpl; intros; auto. apply cons_aeq_mor.
    - rewrite map2_sub_comm. easy.
    - inv H. inv H0. inv H1.
      apply IHdl1 with (c:=length a); auto.
  Qed.
  
  (** (dl1 - dl2) - dl3 = dl1 - (dl2 + dl3) *)
  Lemma dlsub_assoc : forall dl1 dl2 dl3 c, 
      let Asub := fun a b => a + (-b) in
      length dl1 = length dl2 -> length dl2 = length dl3 ->
      width dl1 c -> width dl2 c ->
      dmap2 Asub (dmap2 Asub dl1 dl2) dl3 ==
        dmap2 Asub dl1 (dmap2 Aadd dl2 dl3).
  Proof.
    induction dl1,dl2,dl3; simpl; intros; auto. apply cons_aeq_mor.
    - apply map2_sub_assoc.
    - inv H. inv H0. unfold width in *. inv H1. inv H2.
      apply IHdl1 with (c:=length a); auto.
  Qed.
  
  (** 0 - dl = - dl *)
  Lemma dlsub_zero_l : forall dl r c, 
      let Asub := fun a b => a + (-b) in
      length dl = r -> width dl c ->
      dmap2 Asub (dlzero A0 r c) dl ==
        dmap Aopp dl.
  Proof.
    induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - induction r. easy. inv H. inv H0. simpl.
      unfold dlzero in *. apply cons_eq_iff; split; auto.
      apply lsub_zero_l; auto.
  Qed.
  
  (** dl - 0 = dl *)
  Lemma dlsub_zero_r : forall dl r c, 
      let Asub := fun a b => a + (-b) in
      length dl = r -> width dl c ->
      dmap2 Asub dl (dlzero A0 r c) == dl.
  Proof.
    induction dl; simpl; intros; auto. destruct r; simpl. easy.
    inv H. inv H0. apply cons_eq_iff; split; auto.
    - apply lsub_zero_r; auto.
    - apply IHdl; auto. 
  Qed.
  
  (** dl - dl = 0 *)
  Lemma dlsub_self : forall dl r c, 
      let Asub := fun a b => a + (-b) in
      length dl = r -> width dl c ->
      dmap2 Asub dl dl == (dlzero A0 r c).
  Proof.
    induction dl; simpl; intros; subst; try easy. inv H0.
    rewrite (IHdl (length dl) (length a)); auto.
    unfold dlzero in *. simpl. apply cons_aeq_mor; try easy.
    apply map2_sub_self; auto.
  Qed.

End dlsub.


(* ======================================================================= *)
(** ** list dot dlist, and dlist dot dlist *)
Section ldotdl_dldotdl.
  
  (* Variable A : Type. *)
  (* Variable A0 A1 : A. *)
  (* Variable add mul : A -> A -> A. *)
  (* Variable add_comm : forall a b, a + b = b + a. *)
  (* Variable mul_comm : forall a b, a * b = b * a. *)
  (* Variable add_assoc : forall a b c, (a + b) + c = a + (b + c). *)
  (* Variable mul_assoc : forall a b c, (a * b) * c = a * (b * c). *)
  (* Variable mul_add_distr_l : forall a b1 b2, a * (b1 + b2) = a * b1 + a * b2. *)
  (* Variable mul_add_distr_r : forall a1 a2 b, (a1 + a2) * b = (a1 * b) + (a2 * b). *)
  (* Variable add_0_l : forall a, A0 + a = a. *)
  (* Variable mul_0_l : forall a, A0 * a = A0. *)
  (* Variable mul_1_l : forall a, A1 * a = a. *)

  Context `{R:Ring}.
  Add Ring ring_inst : make_ring_theory.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- b" := (Aopp b) : A_scope.
  Notation Asub := (fun a b => a + (-b)).
  Infix "-" := Asub : A_scope.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (* a convenient notation in this section *)
  Notation ldot := (ldot (Aadd:=Aadd) (A0:=A0) (Amul:=Amul)).
  
  (** list dot product to dlist *)
  Fixpoint ldotdl (l : list A) (dl : list (list A)) : list A :=
    match dl with
    | h :: t => (ldot l h) :: (ldotdl l t)
    | [] => []
    end.
  
  (** ldotdl left with nil *)
  Lemma ldotdl_nil_l : forall dl r,
      length dl = r -> (ldotdl [] dl == lzero A0 r)%list.
  Proof.
    induction dl; simpl; intros; subst; try easy.
    rewrite ldot_nil_l. rewrite IHdl with (r:=length dl); simpl; auto. easy.
  Qed.
  
  (** ldotdl right with nil *)
  Lemma ldotdl_nil_r : forall r l, (ldotdl l (dnil r) == lzero A0 r)%list.
  Proof.
    induction r; simpl; intros; auto. rewrite IHr. rewrite ldot_nil_r. easy.
  Qed.

  Lemma ldotdl_aeq_mor :
    Proper (eqlistA Aeq ==> eqlistA (eqlistA Aeq) ==> eqlistA Aeq) ldotdl.
  Proof.
    unfold Proper, respectful.
    intros l1 l2 H dl1. revert l1 l2 H. induction dl1; simpl; intros.
    - destruct y; try easy.
    - destruct y; try easy. simpl. inv H0. apply cons_eq_iff; split; auto.
      rewrite H,H4. easy.
  Qed.

  Global Existing Instance ldotdl_aeq_mor.

  (** ldotdl length law *)
  Lemma ldotdl_length : forall dl l r,
      length dl = r ->
      length (ldotdl l dl) = r.
  Proof.
    induction dl; intros; simpl in *; auto.
    destruct r. easy. rewrite IHdl with (r:=r); auto.
  Qed.
  
  (** ldotdl left distributve over map2 *)
  Lemma ldotdl_map2_distr_l : forall dl l1 l2 {c},
      length l1 = length l2 ->
      length dl = c -> width dl (length l1) ->
      (ldotdl (map2 Aadd l1 l2) dl == 
         map2 Aadd (ldotdl l1 dl) (ldotdl l2 dl))%list.
  Proof.
    induction dl; intros; simpl; auto. inv H1. apply cons_aeq_mor.
    - apply ldot_map2_distr_l with (r:=length l1); auto.
    - apply IHdl with (c:=length dl); auto.
  Qed.

  (** ldotdl right distributve over dmap2 *)
  Lemma ldotdl_dmap2_distr_r : forall l dl1 dl2 {c},
      length l = c ->
      width dl1 c -> width dl2 c ->
      (ldotdl l (dmap2 Aadd dl1 dl2) == 
         map2 Aadd (ldotdl l dl1) (ldotdl l dl2))%list.
  Proof.
    induction dl1,dl2; simpl; intros; auto. inv H0. inv H1.
    apply cons_aeq_mor.
    - apply ldot_map2_distr_r with (r:=length a); auto. lia.
    - apply IHdl1 with (c:=length l); auto.
  Qed.
  
  (** ldotdl left with zero *)
  Lemma ldotdl_zero_l : forall dl r c,
      length dl = r -> width dl c ->
      (ldotdl (lzero A0 c) dl == lzero A0 r)%list.
  Proof.
    induction dl; simpl; intros; auto.
    - subst; easy.
    - inv H0. rewrite IHdl with (r:=length dl); auto.
      rewrite ldot_zero_l; easy.
  Qed.
  
  (** ldotdl right with zero *)
  Lemma ldotdl_zero_r : forall l r c,
      length l = c ->
      (ldotdl l (dlzero A0 r c) == lzero A0 r)%list.
  Proof.
    induction r; simpl; intros; auto. unfold dlzero in *. rewrite IHr; auto.
    rewrite ldot_zero_r. easy.
  Qed.
  
  (** ldotdl of consr and consc *)
  Lemma ldotdl_consr_consc : forall l2 dl2 l1 x1 r c,
      length l2 = c -> length dl2 = c -> width dl2 r ->
      (ldotdl (x1 :: l1) (consc l2 dl2) ==
         ladd (Aadd:=Aadd) (lcmul (Amul:=Amul) x1 l2) (ldotdl l1 dl2))%list.
  Proof.
    induction l2, dl2; simpl; intros; auto. inv H1.
    rewrite IHl2 with (r:=length l); auto.
    rewrite ldot_cons. easy.
  Qed.

  (** ldot and ldotdl could swap first two operands.
    l1 . (l2 . dl) = l2 . (l1 . dl^T) *)
  Lemma ldot_ldotdl_swap12 : forall dl l1 l2 r c,
      length l1 = r -> length l2 = c -> length dl = r -> width dl c ->
      (ldot l1 (ldotdl l2 dl) ==
         ldot l2 (ldotdl l1 (dltrans dl c)))%A.
  Proof.
    induction dl,l1; simpl; intros; auto.
    - rewrite ldotdl_nil_l with (r:=c); try apply dnil_length.
      rewrite ldot_zero_r; cbv. easy.
    - subst. inversion H1.
    - subst. inversion H1.
    - inv H2. rewrite ldot_cons.
      rewrite ldotdl_consr_consc with (r:=length l1) (c:=length a); auto.
      + rewrite ldot_ladd_distr_l with (r:=length l2);
          auto using lcmul_length, ldotdl_length, dltrans_length.
        rewrite <- IHdl with (r:=length l1); auto.
        rewrite ldot_lcmul_distr_r. easy.
      + rewrite dltrans_length; auto.
      + apply dltrans_width; auto.
  Qed.

  (** ldotdl with consr at right operend *)
  Lemma ldotdl_consr_r : forall l1 l2 dl2 r c,
      length l1 = r -> length l2 = r -> length dl2 = c -> width dl2 r ->
      (ldotdl l1 (l2 :: dl2) == (ldot l1 l2) :: (ldotdl l1 dl2))%list.
  Proof.
    induction l1,l2,dl2; simpl; intros; easy.
  Qed.
  
  (** ldotdl right distributive over ladd.
    (l1 + l2) . dl = l1 . dl + l2.dl *)
  Lemma ldotdl_ladd_distr_r : forall l1 l2 dl r c,
      length l1 = r -> length l2 = r -> length dl = c -> width dl r ->
      (ldotdl (ladd (Aadd:=Aadd) l1 l2) dl == 
         ladd (Aadd:=Aadd) (ldotdl l1 dl) (ldotdl l2 dl))%list.
  Proof.
    induction dl; simpl; intros; auto. inv H2.
    rewrite <- IHdl with (r:=length l1) (c:=length dl); auto.
    rewrite ldot_ladd_distr_r with (r:=length l1); easy.
  Qed.
  
  (** ldotdl with lcmul is assocociative.
    cmul a (dot l dl) = dot (cmul a l) dl *)
  Lemma ldotdl_lcmul_assoc : forall dl a l r c,
      length l = r -> length dl = c -> width dl r ->
      (lcmul (Amul:=Amul) a (ldotdl l dl) == ldotdl (lcmul (Amul:=Amul) a l) dl)%list.
  Proof.
    induction dl; simpl; intros; auto. inv H1.
    rewrite IHdl with (r:=length l) (c:=length dl); auto.
    rewrite ldot_lcmul_distr_l. easy.
  Qed.
  
  (** a * (x :: l) = (a * x) :: (a * l) *)
  Lemma lcmul_cons : forall a x l,
      (lcmul (Amul:=Amul) a (x :: l) == (Amul a x) :: (lcmul (Amul:=Amul) a l))%list.
  Proof.
    intros. easy.
  Qed.
  
  (** a * 0 = 0 *)
  Lemma lcmul_zero_r : forall a n, (lcmul (Amul:=Amul) a (lzero A0 n) == lzero A0 n)%list.
  Proof.
    intros. unfold lcmul. rewrite map_repeat. unfold lzero.
    apply repeat_aeq_mor; auto. ring.
  Qed.
  
  (** l dotdl E = l *)
  Lemma ldotdl_dlunit : forall l {n},
      length l = n -> (ldotdl l (dlunit A0 A1 n) == l)%list.
  Proof.
    induction l; simpl; intros; auto.
    - subst. simpl. easy.
    - destruct n. easy. inv H. simpl. apply cons_eq_iff; split.
      + rewrite ldot_cons. rewrite ldot_zero_r. ring.
      + rewrite (ldotdl_consr_consc);
          try apply repeat_length; try apply dlunit_length; try apply dlunit_width.
        rewrite IHl; try easy.
        rewrite lcmul_zero_r. rewrite ladd_zero_l; easy.
  Qed.
  
  (** dlist dot product *)
  Fixpoint dldotdl (dl1 dl2 : list (list A)) : list (list A) :=
    match dl1 with
    | h1 :: t1 => (ldotdl h1 dl2) :: (dldotdl t1 dl2)
    | [] => []
    end.

  Lemma dldotdl_aeq_mor :
    let deq := eqlistA (eqlistA Aeq) in
    Proper (deq ==> deq ==> deq) dldotdl.
  Proof.
    unfold Proper, respectful.
    induction x; intros.
    - destruct y; easy.
    - destruct y; try easy. simpl. inv H. apply cons_eq_iff; split; auto.
      rewrite H4,H0. easy.
  Qed.

  Global Existing Instance dldotdl_aeq_mor.
  
  (** dldotdl length law *)
  Lemma dldotdl_length : forall dl1 dl2 r1,
      length dl1 = r1 ->
      length (dldotdl dl1 dl2) = r1.
  Proof.
    induction dl1; intros; auto. simpl in *. destruct r1. easy.
    rewrite IHdl1 with (r1:=r1); auto.
  Qed.

  (** dldotdl width law *)
  Lemma dldotdl_width : forall dl1 dl2 r2 c,
      length dl2 = r2 -> width dl1 c -> width dl2 c ->
      width (dldotdl dl1 dl2) r2.
  Proof.
    unfold width; induction dl1; intros; simpl in *; auto. inv H0. constructor.
    - apply ldotdl_length; auto.
    - apply IHdl1 with (c:=length a); auto.
  Qed.

  (** dldotdl consr left *)
  Lemma dldotdl_consr_l : forall l1 dl1 dl2,
      dldotdl (l1 :: dl1) dl2 == (ldotdl l1 dl2) :: (dldotdl dl1 dl2). 
  Proof.
    simpl. easy.
  Qed.
  
  (** dldotdl consr right *)
  Lemma dldotdl_consr_r : forall dl1 l2 dl2 c,
      length l2 = c ->
      width dl1 c ->
      width dl2 c ->
      dldotdl dl1 (l2 :: dl2) == consc (ldotdl l2 dl1) (dldotdl dl1 dl2).
  Proof.
    induction dl1; simpl; intros; auto. inv H0.
    rewrite ldot_comm.
    rewrite IHdl1 with (c:=length l2); auto. easy.
  Qed.
  
  (** dldotdl left distributve over dmap2 *)
  Lemma dldotdl_dmap2_distr_l : forall dl1 dl2 dl3 {c},
      width dl1 c -> width dl2 c -> width dl3 c -> 
      dldotdl (dmap2 Aadd dl1 dl2) dl3 == 
        dmap2 Aadd (dldotdl dl1 dl3) (dldotdl dl2 dl3).
  Proof.
    induction dl1; destruct dl2; intros; simpl in *; try easy.
    inv H. inv H0. apply cons_aeq_mor.
    - apply ldotdl_map2_distr_l with (c:=length dl3); auto.
    - apply IHdl1 with (c:=length a); auto. 
  Qed.
  
  (** dldotdl right distributve over dmap2 *)
  Lemma dldotdl_dmap2_distr_r : forall dl1 dl2 dl3 {c},
      width dl1 c -> width dl2 c -> width dl3 c -> 
      dldotdl dl1 (dmap2 Aadd dl2 dl3) ==
        dmap2 Aadd (dldotdl dl1 dl2) (dldotdl dl1 dl3).
  Proof.
    induction dl1; simpl; intros; auto. inv H. apply cons_aeq_mor.
    - apply ldotdl_dmap2_distr_r with (c:=length a); auto.
    - apply IHdl1 with (c:=length a); auto.
  Qed.

  (** dldotdl [] dl = dnil *)
  Lemma dldotdl_nil_l : forall dl, dldotdl dl [] == dnil (length dl).
  Proof.
    induction dl; simpl; intros; subst; simpl; subst; try easy.
    apply cons_aeq_mor; auto.
  Qed.
  
  (** dldotdl dl [] = dnil *)
  Lemma dldotdl_nil_r : forall dl, dldotdl dl [] == dnil (length dl).
  Proof.
    induction dl; simpl; intros; subst; simpl; subst; try easy.
    apply cons_aeq_mor; auto.
  Qed.

  (** dldotdl zero dl = zero *)
  Lemma dldotdl_zero_l : forall r dl c,
      width dl c ->
      dldotdl (dlzero A0 r c) dl == dlzero A0 r (length dl).
  Proof.
    induction r; simpl; intros; simpl; unfold dlzero in *; simpl; try easy.
    rewrite (IHr _ c); auto.
    rewrite (ldotdl_zero_l _); auto. easy.
  Qed.
  
  (** dldotdl dl zero = zero *)
  Lemma dldotdl_zero_r : forall dl c t,
      width dl c ->
      dldotdl dl (dlzero A0 t c) == dlzero A0 (length dl) t.
  Proof.
    induction dl; simpl; intros; auto. easy. inv H.
    unfold dlzero; simpl. apply cons_aeq_mor.
    - rewrite dlzero_rw. rewrite ldotdl_zero_r; auto. easy.
    - apply IHdl. auto.
  Qed.
  
  (** dltrans for dldotdl with right decomposition *)
  Lemma dltrans_dldotdl_right : forall d1 d2 l2 r,
      dltrans (dldotdl d1 (l2 :: d2)) (S r) ==
        (ldotdl l2 d1) :: (dltrans (dldotdl d1 d2) r).
  Proof.
    unfold width; induction d1; intros; simpl in *. easy.
    specialize (IHd1 d2 l2 r).
    destruct (dltrans (dldotdl d1 (l2 :: d2)) (S r)); try easy. inv IHd1.
    apply cons_aeq_mor.
    - apply cons_aeq_mor; auto. apply ldot_comm.
    - apply consc_aeq_mor; auto. easy. 
  Qed.
  
  (** dldotdl commutation *)
  Lemma dldotdl_comm : forall d1 d2 r c,
      length d1 = r -> width d1 c -> width d2 c ->
      dldotdl d1 d2 == dltrans (dldotdl d2 d1) r.
  Proof.
    induction d1; simpl; intros; subst.
    - rewrite dldotdl_nil_r. rewrite dltrans_nil. easy.
    - inv H0. rewrite dltrans_dldotdl_right.
      apply cons_aeq_mor; try easy. apply IHd1 with (c:=length a); auto.
  Qed.
  
  (** l * (d1 . d2)^T = (l . d1^T) . d2 *)
  Lemma ldotdl_dldotdl_dltrans_assoc : forall d1 d2 l {r c},
      width d1 c ->
      length d2 = r -> width d2 c ->
      (ldotdl l (dltrans (dldotdl d1 d2) r) ==
         ldotdl (ldotdl l (dltrans d1 c)) d2)%list.
  Proof.
    unfold width. induction d1; intros.
    - subst. simpl. rewrite ?ldotdl_nil_r.
      rewrite ldotdl_zero_l with (r:=length d2); auto. easy.
    - inv H. simpl. destruct l.
      + rewrite ldotdl_nil_l with (r:=length d2).
        2:{ apply consc_length.
            apply ldotdl_length; auto.
            apply dltrans_length. apply dldotdl_width with (c:=length a); auto. }
        rewrite ldotdl_nil_l with (r:=length a).
        2:{ apply consc_length; auto.
            apply dltrans_length; auto. }
        rewrite ldotdl_zero_l with (r:=length d2); auto. easy.
      + rewrite ldotdl_consr_consc with (r:=length d1);
          auto using dltrans_length, dltrans_width.
        2:{ rewrite dltrans_length. rewrite ldotdl_length with (r:=length d2); auto.
            apply dldotdl_width with (c:=length a); auto. }
        2:{ apply dltrans_width. apply dldotdl_length; auto.
            apply dldotdl_width with (c:=length a); auto. }
        rewrite ldotdl_consr_consc with (r:=length d1) (c:=length a);
          auto using dltrans_length, dltrans_width.
        rewrite ldotdl_lcmul_assoc with (r:=length a); auto.
        rewrite ldotdl_ladd_distr_r with (r:=length a) (c:=length d2);
          auto using lcmul_length, ldotdl_length, dltrans_length.
        rewrite IHd1 with (c:=length a); auto.
        easy.
  Qed.

  (** dldotdl association *)
  Lemma dldotdl_assoc : forall d1 d2 d3 r c,
      width d2 c ->
      length d3 = r -> width d3 c ->
      dldotdl (dldotdl d1 (dltrans d2 c)) d3 ==
        dldotdl d1 (dltrans (dldotdl d2 d3) r).
  Proof.
    induction d1; simpl; intros; auto.
    apply cons_aeq_mor.
    - rewrite ldotdl_dldotdl_dltrans_assoc with (c:=c); auto. easy.
    - apply IHd1; auto.
  Qed.
  
  (** dldotdl left with dlunit *)
  Lemma dldotdl_dlunit_l : forall (dl : list (list A)) {c},
      width dl c -> 
      dldotdl (dlunit A0 A1 c) dl == dltrans dl c.
  Proof.
    induction dl; simpl; intros; try easy.
    - rewrite dldotdl_nil_r. rewrite dlunit_length. easy.
    - inversion H.
      rewrite dldotdl_consr_r with (c:=c); auto using dlunit_width.
      rewrite IHdl; auto.
      rewrite ldotdl_dlunit; easy.
  Qed.
  
  (** dldotdl right with dlunit *)
  Lemma dldotdl_dlunit_r : forall (dl : list (list A)) {c},
      width dl c -> 
      dldotdl dl (dlunit A0 A1 c) == dl.
  Proof.
    induction dl; simpl; intros; auto. inversion H.
    rewrite IHdl; auto. rewrite ldotdl_dlunit; easy.
  Qed.
  
End ldotdl_dldotdl.


(* ======================================================================= *)
(** ** Properties of dlcmul *)
Section dlcmul_properties.

  (* Variable A : Type. *)
  (* Variable A0 A1 : A. *)
  (* Variable mul : A -> A -> A. *)
  (* Infix "*" := mul. *)
  (* Variable mul_comm : forall a b, a * b = b * a. *)
  (* Variable mul_0_l : forall a, A0 * a = A0. *)
  (* Variable Aeq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}. *)
  (* Variable mul_1_l : forall a : A, A1 * a = a. *)
  (* Variable fmul_cancel_r : forall r1 r2 r : A,  *)
  (*   r <> A0 -> r1 * r = r2 * r -> r1 = r2.  *)

  Context `{F:Field}.
  Context `{Dec_Aeq:Decidable A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** Mapping cmul to dlist keep unchanged imply k = 1 or dlist is zero *)
  Lemma dlcmul_fixpoint_imply_k1_or_dlzero : 
    forall {r c} k (dl : list (list A)) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Amul k x)) dl == dl ->
      ((k == A1)%A \/ dl == dlzero A0 r c).
  Proof.
    unfold width; induction r; intros.
    - rewrite List.length_zero_iff_nil in H1. subst. right. cbv. easy.
    - destruct dl. easy. simpl in *.
      rewrite dlzero_Sr by apply monoidEquiv. 
      inversion H. inversion H1. inversion H2.
      apply (lcmul_fixpoint_imply_k1_or_lzero l eq_refl) in H5.
      specialize (IHr c k dl H9 H12 H7).
      destruct IHr,H5; try (left; easy). right.
      subst. rewrite <- H13. rewrite <- H5. easy.
  Qed.
  
  (** Mapping mulc to dlist keep unchanged imply k = 1 or dlist is zero *)
  Lemma dlmulc_fixpoint_imply_k1_or_dlzero : 
    forall {r c} k (dl : list (list A)) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Amul x k)) dl == dl ->
      ((k == A1)%A \/ dl == dlzero A0 r c).
  Proof.
    intros. apply dlcmul_fixpoint_imply_k1_or_dlzero; auto.
    rewrite <- H at 2.
    apply map_ext. intros.
    apply map_ext. intros. apply commutative. 
  Qed.

  (** Mapping cmul to dlist got zero imply k = 0 or dlist is zero *)
  Lemma dlcmul_zero_imply_k0_or_dlzero : 
    forall {r c} k (dl : list (list A)) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Amul k x)) dl == (dlzero A0 r c) ->
      ((k == A0)%A \/ dl == dlzero A0 r c).
  Proof.
    induction r; intros.
    - rewrite List.length_zero_iff_nil in H1. subst. cbv. right. easy.
    - destruct dl. easy. simpl in *.
      rewrite dlzero_Sr by apply monoidEquiv.
      inv H. inv H1. inv H2.
      apply IHr in H7; auto.
      apply lcmul_eq0_imply_k0_or_lzero in H5; auto.
      destruct H5, H7; auto.
  Qed.
  
End dlcmul_properties.
