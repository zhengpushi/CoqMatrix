(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension for list (Setoid version)
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. reference "A Gentle Introduction to Type Classes and Relations in Coq"
  2. Owing to Setoid，lots of properties of list need to re-proof.
  
  history   :
  1. 2021.12, by ZhengPu Shi.
     first version

  2. 2022.05, by ZhengPu Shi.
     split big file into small modules


  3. 2022.10, by ZhengPu Shi
     Setoid version
*)

Require Export List. Export ListNotations.
Require Export SetoidList.
Require Export HierarchySetoid.
Require Export NatExt.

Open Scope nat_scope.
Open Scope A.
Open Scope list.

Generalizable Variables A B C Aeq Beq Ceq.
Generalizable Variables Aadd Aopp Amul Ainv.


(* ======================================================================= *)
(** ** Properties of cons *)

Section cons.

  Context `{Aeq : relation A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** cons is a proper morphism *)
  Lemma cons_aeq_mor : Proper (Aeq ==> eqlistA Aeq ==> eqlistA Aeq) (@cons A).
  Proof.
    intros x y H1 l1 l2 H2. destruct l1,l2; auto.
  Qed.

  Global Existing Instance cons_aeq_mor.

  (** Equality of cons, iff both parts are equal *)
  Lemma cons_eq_iff : forall (a1 a2 : A) (l1 l2 : list A),
      a1 :: l1 == a2 :: l2 <-> (a1 == a2)%A /\ l1 == l2.
  Proof.
    intros. split; intros H; inversion H; subst; auto.
  Qed.

  (** Inequality of cons, iff at least one parts are not equal *)
  Lemma cons_neq_iff : forall (a1 a2 : A) (l1 l2 : list A),
      ~(a1 :: l1 == a2 :: l2) <-> (~(a1 == a2)%A \/ ~(l1 == l2)).
  Proof.
    intros. split; intro H.
    - rewrite cons_eq_iff in H.
      apply not_and_or in H; auto.
    - intro. inversion H0. subst. destruct H; auto.
  Qed.

End cons.


(* ======================================================================= *)
(** ** General properties on list A *)

Section Props_listA.

  (** eqlistA eq and eq are same relation *)
  Lemma eqlistA_eq_same_relation : forall {A} (l1 l2 : list A),
      eqlistA eq l1 l2 <-> l1 = l2.
  Proof.
    intros A l1. induction l1; destruct l2; simpl; split; intros; auto; try easy.
    - inv H. f_equal. apply IHl1. auto.
    - inv H. easy.
  Qed.

  (** eqlistA eqlistA eq and eq are same relation *)
  Lemma eqlistA_eq_same_relation2 : forall {A} (l1 l2 : list (list A)),
      eqlistA (eqlistA eq) l1 l2 <-> l1 = l2.
  Proof.
    intros A l1. induction l1; destruct l2; simpl; split; intros; auto; try easy.
    - inv H. f_equal.
      + apply eqlistA_eq_same_relation; auto.
      + apply IHl1. auto.
    - inv H. easy.
  Qed.

  Context `{Aeq:relation A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  
  (** Redefine 'length_zero_iff_nil', original is opaque, make it transparent t *)
  Lemma length_zero_iff_nil : forall (l : list A), length l = 0 <-> l == [].
  Proof.
    intros. destruct l; intros; split; intros; auto; try easy.
  Defined.

  (** list equality is decidable on setoid *)
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Lemma list_eq_dec : (forall x y : A, {(x == y)%A} + {~(x == y)%A}) ->
                      forall l1 l2 : list A, {l1 == l2} + {~(l1 == l2)}.
  Proof.
    intros H l1. induction l1; destruct l2; intros;
      try (left; easy); try (right; easy).
    destruct (H a a0),(IHl1 l2); auto.
    - right. intro. inv H0. easy.
    - right. intro. inv H0. easy.
    - right. intro. inv H0. easy.
  Qed.
  
End Props_listA.


(* ======================================================================= *)
(** ** Properties of hd and tl *)
Section hd_tl.
  
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** hd is a proper morphism *)
  Lemma hd_aeq_mor : Proper (Aeq ==> eqlistA Aeq ==> Aeq) (@hd A).
  Proof.
    unfold Proper, respectful.
    intros. destruct x0, y0; simpl; try easy. inv H0. auto.
  Qed.
  Global Existing Instance hd_aeq_mor.
  
  (** tl is a proper morphism *)
  Lemma tl_aeq_mor : Proper (eqlistA Aeq ==> eqlistA Aeq) (@tl A).
  Proof.
    unfold Proper, respectful.
    intros. destruct x, y; simpl; try easy. inv H. auto.
  Qed.
  Global Existing Instance tl_aeq_mor.
  
  (** length of tl. (pred version) *)
  Lemma tl_length : forall (l : list A), length (tl l) = pred (length l).
  Proof.
    induction l; auto.
  Qed.

End hd_tl.

(* ======================================================================= *)
(** ** Properties of nth *)

Section nth.
  
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).

  
  (** nth is a proper morphism *)
  Lemma nth_aeq_mor : Proper (eq ==> eqlistA Aeq ==> Aeq ==> Aeq) (@nth A).
  Proof.
    unfold Proper, respectful.
    intros i j H; inv H. rename j into i.
    intros l1 l2. revert l2 i.
    induction l1; destruct l2,i; intros; simpl in *; try easy.
    - inv H. easy.
    - inv H. auto.
  Qed.

  Global Existing Instance nth_aeq_mor.
    

  (** nth [] a = a *)
  Lemma nth_nil : forall (a : A) (i : nat), (nth i [] a == a)%A.
  Proof.
    intros. destruct i; simpl; easy.
  Qed.

  (** Two list equal iff all nth visit equal *)
  Lemma list_eq_iff_nth (A0 : A) : forall n (l1 l2 : list A)
                                     (H1 : length l1 = n) (H2 : length l2 = n),
      l1 == l2 <-> (forall (i : nat), i < n -> (nth i l1 A0 == nth i l2 A0)%A).
  Proof.
    intros n l1. revert n. induction l1; intros; simpl in *; subst.
    - split; intros; try easy. apply List.length_zero_iff_nil in H2. rewrite H2. easy.
    - split; intros; try easy.
      + destruct l2; try easy.
        inversion H. subst.
        destruct i; simpl; auto.
        simpl in H2. inversion H2.
        specialize (IHl1 (length l1) l2 eq_refl H3).
        rewrite IHl1 in H7. apply H7. lia.
      + destruct l2; simpl in *; try easy.
        assert (a == a0)%A.
        { specialize (H 0).
          assert (0 < S (length l1)) by lia.
          apply H in H0; auto. }
        assert (l1 == l2).
        { rewrite (IHl1 (length l1)); auto. intros.
          specialize (H (S i)); simpl in H. apply H. lia. }
        rewrite H0,H1. easy.
  Qed.

  (** Get from repeat x and default value x always return x *)
  Lemma nth_repeat_same : forall (a : A) (n i : nat),
      (nth i (repeat a n) a == a)%A.
  Proof.
    intros a n. induction n; destruct i; simpl; easy.
  Qed.

End nth.

  
(* ======================================================================= *)
(** ** Set element of a list *)

Section chg.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** *** Set element with a constant value *)
  Fixpoint lst_chg (l : list A) (i : nat) (x : A) : list A :=
    match l, i with
    | [], _ => []
    | a :: l, 0 => x :: l
    | a :: l, S i => a :: (lst_chg l i x)
    end.

  (** Length property *)
  Lemma lst_chg_length : forall (l : list A) ni n x, 
      length l = n ->
      length (lst_chg l ni x) = n.
  Proof.
    intros l; induction l; auto. induction ni; auto; simpl; intros.
    destruct n; auto. easy.
  Qed.

  (** *** Set element with a generation function *)

  (** Inner version. i0 is given position, i is changing every loop *)
  Fixpoint lst_chgf_aux (l : list A) (i0 i : nat) (f : nat -> A) 
    : list A :=
    match l, i with
    | [], _ => []
    | a :: l, 0 => f i0 :: l
    | a :: l, S i => a :: (lst_chgf_aux l i0 i f)
    end.

  (** User version that hide i0 parameter *)
  Definition lst_chgf (l : list A) (i : nat) (f : nat -> A) : list A :=
    lst_chgf_aux l i i f.

  (* Let f_gen := fun (i : nat) => (i + 5).
     Compute lst_chgf [1;2;3] 0 f_gen.
     Compute lst_chgf [1;2;3] 1 f_gen.
   *)
  
  (** Length property *)
  Lemma lst_chgf_aux_length : forall (l : list A) ni n ni0 f, 
      length l = n ->
      length (lst_chgf_aux l ni0 ni f) = n.
  Proof.
    intros l; induction l; auto. destruct ni; auto; simpl; intros.
    destruct n; auto. easy.
  Qed.

  Lemma lst_chgf_length : forall (l : list A) n ni f, 
      length l = n ->
      length (lst_chgf l ni f) = n.
  Proof.
    intros. apply lst_chgf_aux_length; auto.
  Qed.

End chg.


(* ======================================================================= *)
(** ** Properties of length *)
Section length.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** decompose a list which length is 1 *)

  (** Note that, we need this lemma to split a list with only one element,
      although the definition end with "Defined", we cannot got a explicit 
      result by Compute. In practice, won't use this lemma if you needn't *)
  Lemma list_length_1 : forall (l : list A),
      length l = 1 -> {x | l == [x]}.
  Proof. 
    destruct l; intros. inversion H. inversion H.
    apply List.length_zero_iff_nil in H1. subst. exists a. easy.
  Defined.

  Section Test.
    Let l := [1].
    Definition h : length l = 1. auto. Defined.
    (*   Compute proj2_sig (list_length_1 l h). *)
  End Test.

  (** a list has only one element equal to [hd _ l] *)
  Lemma list_length1_eq_hd : forall (x : A) (l:list A), 
      length l = 1 -> [hd x l] == l.
  Proof.
    intros x l. destruct l.
    - intros. simpl in *. lia.
    - intros. simpl in *. f_equal.
      apply eq_add_S in H. apply List.length_zero_iff_nil in H. subst. easy.
  Qed.

  (** decompose a list which length is S n *)
  Lemma list_length_Sn : forall (l : list A) n,
      length l = S n -> {x & { t | l == x :: t}}.
  Proof.
    destruct l; intros. inversion H. exists a. exists l. easy.
  Qed.

  (** decompose a list which length is S (S n) *)
  Lemma list_length_SSn : forall (l : list A) n,
      length l = S (S n) -> {x & { y & { t | l = x :: y :: t}}}.
  Proof.
    destruct l; intros. inversion H.
    exists a. destruct l. inversion H.
    exists a0. exists l. auto.
  Qed.

  (** Split list which length is 1 *)
  Lemma list_length1_neq : forall (l : list A) (a b : A), 
      (length (a :: l) = 1 /\ ~((a :: l) == [b])) -> (~(a == b)%A /\ l == []).
  Proof.
    intros l. induction l; intros; destruct H.
    - simpl in *. split; auto.
    - simpl in *. easy. 
  Qed.

End length.

(* ======================================================================= *)
(** ** Customized list induction *)

Section ind.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** Connect induction principle between nat and list *)
  Lemma ind_nat_list : forall (P : list A -> Prop) ,
      (forall n l, length l = n -> P l) -> (forall l, P l).
  Proof.
    intros. apply (H (length l)). auto.
  Qed.

  (** Two step induction principle for list *)
  Theorem list_ind2 : forall (P : list A -> Prop),
      (* 新增的前提，表示 P 与 Aeq 是相容的 *)
      (forall l1 l2 : list A, l1 == l2 -> P l1 -> P l2) ->
      (P []) -> 
      (forall a, P [a]) -> 
      (forall l a b, P l -> P (a :: b :: l)) ->
      (forall l, P l).
  Proof.
    intros P Hx H0 H1 H2. apply ind_nat_list. induction n using nat_ind2. 
    - intros. apply List.length_zero_iff_nil in H; subst. apply (Hx []); easy.
    - intros. apply list_length_1 in H. destruct H.
      apply (Hx [x]); easy.
    - destruct l; auto. destruct l; auto.
      intros. apply H2. apply IHn. simpl in H. lia.
  Qed.

End ind.


(* ======================================================================= *)
(** ** list repeat properties *)

Section repeat.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := (eqlistA Aeq).

  Lemma repeat_aeq_mor : Proper (Aeq ==> eq ==> (eqlistA Aeq)) (@repeat A).
  Proof.
    unfold Proper, respectful.
    intros a b Hab i j. revert j.
    induction i; intros.
    - subst; simpl. easy.
    - destruct j. easy. simpl. apply cons_aeq_mor; auto.
  Qed.
  
  Global Existing Instance repeat_aeq_mor.

  (** repeat S n times equal to another form *)
  Lemma list_repeat_Sn (A0 : A) : forall n, repeat A0 (S n) == A0 :: repeat A0 n.
  Proof.
    intros. simpl. easy.
  Qed.

End repeat.


(* ======================================================================= *)
(** ** Zero list *)

Section lzero.

  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq).
  
  (** A friendly name for zero list *)
  Definition lzero (A0 : A) n := repeat A0 n.

  (** lzero's length law *)
  Lemma lzero_length (A0 : A) : forall n, length (lzero A0 n) = n.
  Proof.
    intros. apply repeat_length.
  Qed.

  (** append two zero list to a zero list satisfy length relation *)
  Lemma lzero_app (A0 : A) : forall n1 n2,
      lzero A0 n1 ++ lzero A0 n2 == lzero A0 (n1 + n2).
  Proof.
    unfold lzero. intros. rewrite repeat_app. easy.
  Qed.

End lzero.

(* ======================================================================= *)
(** ** Properties of map *)

(** map for three types *)

Section map_A_B_C.
  Context `{Aeq : relation A} `{Beq : relation B} `{Equiv_Ceq : Equivalence C Ceq}.
  Infix "==" := (eqlistA Ceq).

  (** map_map setoid version *)
  Lemma map_map : forall (f : A -> B) (g : B -> C) (l : list A),
      map g (map f l) == map (fun x : A => g (f x)) l.
  Proof.
    intros f g l. induction l; simpl; try easy.
    apply cons_aeq_mor; auto.
    easy.
  Qed.

End map_A_B_C.


(** map for two types *)
Section map_A_B.

  Context `{Equiv_Aeq:Equivalence A Aeq}.
  Context `{Equiv_Beq:Equivalence B Beq}.
  Infix "==" := (Beq) : A_scope.
  Infix "==" := (eqlistA Beq).

  (** map is a proper morphism *)
  Lemma map_aeq_mor : Proper ((Aeq ==> Beq) ==> eqlistA Aeq ==> eqlistA Beq) (@map A B).
  Proof.
    unfold Proper, respectful.
    intros f1 f2 Hf l1.
    induction l1.
    - intros [|l2]; intros; simpl in *; auto. inv H.
    - intros [|l2]; intros; simpl in *. inv H. inv H.
      constructor; auto.
  Qed.

  Global Existing Instance map_aeq_mor.

  (** map_ext setoid version *)
  Lemma map_ext : forall (f g : A -> B),
      (forall a : A, (f a == g a)%A) -> forall l : list A, map f l == map g l.
  Proof.
    intros f g H l. induction l; intros; try easy.
    simpl. rewrite H,IHl. easy.
  Qed.

  (** map_ext_in_iff setoid version *)
  Lemma map_ext_in_iff : forall (f g : A -> B) (l : list A),
      map f l == map g l <-> (forall a : A, In a l -> (f a == g a)%A).
  Proof.
    intros f g l. induction l; intros; simpl; split; intros; try easy.
    - inversion H; subst. rewrite IHl in H6. destruct H0.
      + subst. easy.
      + apply H6. auto.
    - apply cons_aeq_mor; auto.
      apply IHl. auto.
  Qed.

  (** map and repeat is communtative *)
  Lemma map_repeat (f : A -> B) : forall (a : A) n, 
      (map f (repeat a n)) == (repeat (f a) n).
  Proof. 
    induction n; simpl; auto. constructor; auto. easy.
  Qed.
  
End map_A_B.


(** map for one type *)
Section map_A.

  Context `{Equiv_Aeq:Equivalence A Aeq}.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** Extented map_id lemma, which needn't the function is a exactly format of
     "forall x, x" *)
  Lemma map_id : forall (l : list A) (f : A -> A) (H: forall a, (f a == a)%A),
      (map f l == l)%list.
  Proof.
    induction l; intros; simpl. easy. apply cons_eq_iff; split; auto.
  Qed.

  (** lzero equal to map to_zero *)
  Lemma map_eq_zero : forall l (A0 : A) (f : A -> A) n,
      (forall x : A, (f x == A0)%A) -> length l = n -> map f l == lzero A0 n.
  Proof.
    induction l; intros; simpl in *. subst. simpl. easy.
    destruct n. easy. inv H0. simpl.
    apply cons_aeq_mor; auto.
  Qed.
    
  (** Mapping is fixpoint, iff f is id *)
  Lemma map_fixpoint_imply_id (f : A -> A) : forall (l : list A), 
      map f l == l -> (forall x, In x l -> (f x == x)%A).
  Proof.
    induction l; intros; simpl in *. easy. inversion H.
    destruct H0. subst; auto. apply IHl; auto.
  Qed.

  (** Simplify of nth+map+seq *)
  Lemma nth_map_seq : forall i f n m (a0:A),
      i < m -> (nth i (map f (seq n m)) a0 == f (i + n))%A.
  Proof.
    intros. gd m. gd f. gd i. induction n.
    - intros i f m. gd f. gd i. induction m.
      + intros. lia.
      + intros. simpl. destruct i; try easy.
        rewrite <- seq_shift.
        rewrite List.map_map.
        rewrite IHm; try easy. lia.
    - intros. rewrite <- seq_shift. rewrite List.map_map.
      rewrite IHn; auto. replace (S (i + n)) with (i + S n); auto. easy.
  Qed.

  (** Simplify of map+nth+seq *)
  (* Note: the lower index of seq is 0, it could extend to any nat number later *)
  Lemma map_nth_seq  : forall n (l : list A) A0,
      length l = n -> map (fun i => nth i l A0) (seq 0 n) == l.
  Proof.
    induction n.
    - intros. simpl. apply List.length_zero_iff_nil in H; subst. easy.
    - intros. simpl. destruct l.
      + simpl in *; lia.
      + apply cons_aeq_mor; try easy. inversion H.
        rewrite <- seq_shift.
        rewrite map_map; auto.
        simpl. rewrite H1. rewrite IHn; easy.
  Qed.

  (** Equality of map+seq, iff corresponding elements are equal *)
  Lemma map_seq_eq : forall n (f g : nat -> A),
      map f (seq 0 n) == map g (seq 0 n) <-> (forall i, i < n -> (f i == g i)%A).
  Proof.
    intros; split; intros.
    - rewrite map_ext_in_iff in H. apply H. apply in_seq. lia.
    - apply map_ext_in_iff. intros. apply H. apply in_seq in H0. lia.
  Qed.

End map_A.


(* ======================================================================= *)
(** ** map two lists to a list *)
Section map2.

  Context {A B C :Type} {Aeq:relation A} {Beq:relation B} {Ceq:relation C}.
  Context {Aadd : A -> B -> C}.
  Context `{Equiv_Ceq : Equivalence C Ceq}.
  Infix "==" := (eqlistA Ceq).

  (** map operation to two list *)
  Fixpoint map2 (l1 : list A) (l2 : list B) : list C :=
    match l1, l2 with
    | x1 :: t1, x2 :: t2 => (Aadd x1 x2) :: (map2 t1 t2)
    | _, _ => []
    end.

  Context (AaddProper : Proper (Aeq ==> Beq ==> Ceq) Aadd).
  Lemma map2_aeq_mor : Proper (eqlistA Aeq ==> eqlistA Beq ==> eqlistA Ceq) map2.
  Proof.
    intros a1. induction a1.
    - intros a2 Ha b1 b2 Hb. destruct b1,a2,b2; try easy.
    - intros a2 Ha b1 b2 Hb. destruct b1,a2,b2; try easy.
      simpl. inversion Ha. inversion Hb. subst.
      apply cons_eq_iff. split.
      + apply AaddProper; auto.
      + apply IHa1; auto.
  Qed.
  Global Existing Instance map2_aeq_mor.
  
  (** length of map2 *)
  Lemma map2_length : forall (l1 : list A) (l2 : list B) n,
    length l1 = n -> length l2 = n -> length (map2 l1 l2) = n.
  Proof. 
    induction l1,l2; simpl; auto. intros. destruct n; simpl; auto. easy.
  Qed.
  
  (** map2 to two lists could be separated by two segments with same length *)
  Lemma map2_app : forall (la1 la2 : list A) (lb1 lb2 : list B),
    length la1 = length lb1 -> length la2 = length lb2 ->
    map2 (la1 ++ la2) (lb1 ++ lb2) == (map2 la1 lb1) ++ (map2 la2 lb2).
  Proof.
    induction la1, lb1; intros; simpl; auto; simpl in H; try easy.
    apply cons_aeq_mor; try easy.
    apply IHla1; auto.
  Qed.
  
  (** map2 [] l = [] *)
  Lemma map2_nil_l : forall l, map2 [] l == [].
  Proof.
    destruct l; easy.
  Qed.

  (** map2 l [] = [] *)
  Lemma map2_nil_r : forall l, map2 l [] == [].
  Proof.
    destruct l; easy.
  Qed.
  
End map2.

Arguments map2 {A B C}.


(* ======================================================================= *)
(** ** map2 on dlist *)

Section map2_dlist.

  Context {A B C :Type} `{Ceq:relation C}.
  Context `{EqEquivC:Equivalence C Ceq}.
  Infix "==" := (eqlistA (eqlistA Ceq)).
  Variable f : A -> B -> C.
  
  (** tail of map2 to dlist, equal to map2 to tail part of original dlists *)
  Lemma tail_map2_dlist : forall dl1 dl2,
    tl (map2 (map2 f) dl1 dl2) ==
    map2 (map2 f) (tl dl1) (tl dl2).
  Proof.
    destruct dl1, dl2; simpl; try easy. rewrite map2_nil_r. easy.
  Qed.

End map2_dlist.


(* ======================================================================= *)
(** ** map2 properties with same base type *)
Section map2_sametype.

  Context `{Equiv_Aeq:Equivalence A Aeq}.
  Context `{Aadd:A->A->A} `{Aopp:A->A}.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (-b)).
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** nth (map2 f l1 l2) i = f (nth l1 i) (nth l2 i) *)
  Lemma map2_nth : forall (l1 l2 : list A) i (a : A),
    i < length l1 -> i < length l2 ->
    (nth i (map2 Aadd l1 l2) a == Aadd (nth i l1 a) (nth i l2 a))%A.
  Proof.
    induction l1; intros; simpl in *; try lia.
    destruct l2; simpl in *; try lia.
    destruct i; try easy.
    apply IHl1; try lia.
  Qed.

  (** l1 . l2 = l2 . l1 *)
  Context `{Comm:Commutative A Aadd Aeq}.
  Lemma map2_comm : forall (l1 l2 : list A), map2 Aadd l1 l2 == map2 Aadd l2 l1.
  Proof.
    induction l1; destruct l2; simpl; try easy.
    apply cons_aeq_mor; auto. apply commutative.
  Qed.
    
  (** (l1 . l2) . l3 = l1 . (l2 . l3) *)
  Context {Assoc:Associative Aadd Aeq}.
  Lemma map2_assoc : forall (l1 l2 l3 : list A),
      map2 Aadd (map2 Aadd l1 l2) l3 == map2 Aadd l1 (map2 Aadd l2 l3).
  Proof.
    induction l1; destruct l2,l3; simpl; try easy.
    apply cons_aeq_mor; auto.
    rewrite associative. easy.
  Qed.

  (** map2 over map is homorphism *)
  (* In fact, I don't know how to naming this property yet. *)
  Lemma map2_map_hom : forall l1 l2
    (H : forall a b : A, (Aopp (Aadd a b) == Aadd (Aopp a) (Aopp b))%A),
    map2 Aadd (map Aopp l1) (map Aopp l2) == map Aopp (map2 Aadd l1 l2).
  Proof.
    intros. revert l2.
    induction l1; destruct l2; simpl; try easy.
    apply cons_aeq_mor; auto. easy.
  Qed.

  
  (** *** The properties below, need a monoid structure *)

  Context `{M:Monoid A Aadd A0 Aeq}.

  (** map2 lzero l = l *)
  Lemma map2_zero_l : forall l, map2 Aadd (lzero A0 (length l)) l == l.
  Proof.
    induction l; intros; simpl. easy. rewrite IHl. monoid_simpl.
  Qed.

  (** map2 l lzero = l *)
  Lemma map2_zero_r : forall l, map2 Aadd l (lzero A0 (length l)) == l.
  Proof.
    induction l; intros; simpl. easy. rewrite IHl. monoid_simpl.
  Qed.

  
  (** *** The properties below, need a group structure *)

  Context `{G:Group A Aadd A0 Aopp Aeq}.

  (* l1 - l2 = - (l2 - l1) *)
  (* Context {Invo_Aopp : Involution Aopp Aeq}. *)
  (* Context {ResBianry : RespectBinary Aadd Aeq Aeq Aeq}. *)
  Lemma map2_sub_comm : forall (l1 l2 : list A),
      map2 Asub l1 l2 == map Aopp (map2 Asub l2 l1).
  Proof.
    induction l1; destruct l2; intros; simpl in *; auto.
    apply cons_aeq_mor; auto.
    rewrite group_inv_distr. rewrite group_inv_inv. easy.
  Qed.

  (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
  Lemma map2_sub_perm : forall (l1 l2 l3 : list A),
      map2 Asub (map2 Asub l1 l2) l3 == map2 Asub (map2 Asub l1 l3) l2.
  Proof.
    induction l1,l2,l3; simpl; auto. apply cons_aeq_mor; auto.
    rewrite ?associative.
    apply monoidAaddProper; try easy. apply commutative.
  Qed.
  
  (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
  Lemma map2_sub_assoc : forall (l1 l2 l3 : list A),
      map2 Asub (map2 Asub l1 l2) l3 == map2 Asub l1 (map2 Aadd l2 l3).
  Proof.
    induction l1,l2,l3; simpl; auto. apply cons_aeq_mor; auto.
    rewrite associative. apply monoidAaddProper; try easy.
    rewrite group_inv_distr. apply commutative.
  Qed.

  (** 0 - l = - l *)
  Lemma map2_sub_zero_l : forall l n, 
      length l = n -> map2 Asub (lzero A0 n) l == map Aopp l.
  Proof.
    induction l; simpl; intros. apply map2_nil_r.
    induction n ; simpl. inversion H. apply cons_aeq_mor; auto.
    group_simpl.
  Qed.
  
  (** l - 0 = l *)
  Lemma map2_sub_zero_r : forall l n, 
      length l = n -> map2 Asub l (lzero A0 n) == l.
  Proof.
    induction l; simpl; intros; auto. destruct n; simpl. inversion H.
    apply cons_aeq_mor; auto.
    rewrite group_inv_id. group_simpl.
  Qed.
  
  (** l - l = 0 *)
  Lemma map2_sub_self : forall l n, 
      length l = n -> map2 Asub l l == (lzero A0 n).
  Proof.
    induction l; simpl; intros; subst; try easy.
    apply cons_aeq_mor; auto. group_simpl.
  Qed.

End map2_sametype.

(** map2 with map of two components *)
Section map2_map_map.

  Context {A B : Type}.
  Context {Beq : relation B}.
  Infix "==" := (Beq) : A_scope.
  Infix "==" := (eqlistA Beq) : list_scope.

  Lemma map2_map_map : forall (f1 f2 g : A -> B) (h : B -> B -> B)
                         (H : forall x, (h (f1 x) (f2 x) == g x)%A)
                         (l : list A),
    map2 h (map f1 l) (map f2 l) == map g l.
  Proof.
    induction l; simpl; auto.
  Qed.

End map2_map_map.

Section fold.
  Context `{M:Monoid}.

  (** fold_right is a Proper morphism *)
  Lemma fold_right_aeq_mor : Proper (Aeq ==> eqlistA Aeq ==> Aeq) (fold_right Aadd).
  Proof.
    intros x y H l1. induction l1; intros l2 H2; destruct l2; try easy.
    inv H2. simpl. apply monoidAaddProper; try easy.
    apply IHl1. easy.
  Qed.
  Global Existing Instance fold_right_aeq_mor.

End fold.

(* ======================================================================= *)
(** ** Addition, Opposition and Subtraction of list *)
Section ladd_opp_sub.

  (* Tips: these old codes are replaced with Typeclass. *)
  (* Variable A : Type. *)
  (* Variable A0 : A. *)
  (* Variable add : A -> A -> A. *)
  (* Variable add_comm : forall a b, add a b = add b a. *)
  (* Variable add_0_l : forall a, add A0 a = a. *)
  (* Variable opp : A -> A. *)
  (* Variable sub : A -> A -> A. *)
  (* Variable sub_comm : forall a b, sub a b = opp (sub b a). *)
  (* Variable sub_assoc1 : forall a b c, sub (sub a b) c = sub a (sub c b). *)
  (* Variable sub_assoc2 : forall a b c, sub (sub a b) c = sub a (add b c). *)
  (* Variable sub_0_l : forall a, sub A0 a = opp a. *)
  (* Variable sub_0_r : forall a, sub a A0 = a. *)
  (* Variable sub_self : forall a, sub a a = A0. *)
  
  Context `{AG:AGroup A Aadd A0 Aopp Aeq}.
  Notation Asub := (fun a b => Aadd a (Aopp b)).
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** l1 + l2 *)
  Definition ladd (l1 l2 : list A) : list A := map2 Aadd l1 l2.
  Infix "+" := ladd : list_scope.

  Lemma ladd_aeq_mor : Proper (eqlistA Aeq ==> eqlistA Aeq ==> eqlistA Aeq) ladd.
  Proof.
    apply map2_aeq_mor. apply groupAaddProper.
  Qed.
  
  Global Existing Instance ladd_aeq_mor.
  
  (** l1 + l2 = l2 + l1 *)
  Lemma ladd_comm : forall l1 l2, l1 + l2 == l2 + l1.
  Proof.
    apply map2_comm; auto.
  Qed.
  
  (** [] + l = [] *)
  Lemma ladd_nil_l : forall l, ladd l [] == [].
  Proof.
    induction l; try easy.
  Qed.
  
  (** l + [] = [] *)
  Lemma ladd_nil_r : forall l, ladd [] l == [].
  Proof.
    try easy.
  Qed.
  
  (** 0 + l = l *)
  Lemma ladd_zero_l : forall l n, 
    length l = n -> ladd (lzero A0 n) l == l.
  Proof.
    induction l; simpl; intros. apply map2_nil_r.
    induction n ; simpl. inversion H.
    apply cons_aeq_mor; auto.
    group_simpl.
  Qed.
  
  (** l + 0 = l *)
  Lemma ladd_zero_r : forall l n, length l = n -> ladd l (lzero A0 n) == l.
  Proof.
    intros. unfold ladd. rewrite map2_comm; auto.
    apply ladd_zero_l; auto.
  Qed.
  
  (** - l *)
  Definition lopp (l : list A) : list A := map Aopp l.

  Lemma lopp_aeq_mor : Proper (eqlistA Aeq ==> eqlistA Aeq) lopp.
  Proof.
    apply map_aeq_mor. apply groupAoppProper.
  Qed.

  Global Existing Instance lopp_aeq_mor.
  
  (** l1 - l2 *)
  Definition lsub (l1 l2 : list A) : list A := map2 Asub l1 l2.

  Lemma lsub_aeq_mor : Proper (eqlistA Aeq ==> eqlistA Aeq ==> eqlistA Aeq) lsub.
  Proof.
    apply map2_aeq_mor.
    unfold Proper, respectful.
    intros. apply monoidAaddProper; try easy. apply groupAoppProper. auto.
  Qed.

  Global Existing Instance lsub_aeq_mor.

  (** l1 - l2 = - (l2 - l1) *)
  Lemma lsub_comm : forall (l1 l2 : list A), lsub l1 l2 == lopp (lsub l2 l1).
  Proof.
    intros.
    apply map2_sub_comm.
  Qed.
  
  (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
  Lemma lsub_perm : forall (l1 l2 l3 : list A),
      lsub (lsub l1 l2) l3 == lsub (lsub l1 l3) l2.
  Proof.
    apply map2_sub_perm.
  Qed.
  
  (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
  Lemma lsub_assoc : forall (l1 l2 l3 : list A),
      lsub (lsub l1 l2) l3 == lsub l1 (ladd l2 l3).
  Proof.
    apply map2_sub_assoc.
  Qed.
  
  (** 0 - l = - l *)
  Lemma lsub_zero_l : forall l n, length l = n -> lsub (lzero A0 n) l == lopp l.
  Proof.
    apply map2_sub_zero_l.
  Qed.
  
  (** l - 0 = l *)
  Lemma lsub_zero_r : forall l n, length l = n -> lsub l (lzero A0 n) == l.
  Proof.
    apply map2_sub_zero_r.
  Qed.
  
  (** l - l = 0 *)
  Lemma lsub_self : forall l n, length l = n -> lsub l l == (lzero A0 n).
  Proof.
    apply map2_sub_self.
  Qed.
  
End ladd_opp_sub.


(* ======================================================================= *)
(** ** constant multiplication of list *)
Section lcmul_lmulc.
  
  (* Variable A : Type. *)
  (* Variable A0 A1 : A. *)
  (* Variable mul : A -> A -> A. *)
  (* Infix "*" := mul. *)
  (* Variable mul_comm : forall a b, a * b = b * a. *)
  (* Variable mul_0_l : forall a, A0 * a = A0. *)
  (* Variable Aeqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}. *)
  (* Variable mul_1_l : forall a : A, A1 * a = a. *)
  (* Variable mul_cancel_r : forall r1 r2 r : A,  *)
  (*     r <> A0 -> r1 * r = r2 * r -> r1 = r2.  *)

  Context `{R:Ring}.

  Infix "*" := Amul : A_scope.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).

  Context `{Dec:Decidable A Aeq}.
  
  (** a * l *)
  Definition lcmul (a : A) (l : list A) : list A := map (fun x => a * x) l.
  
  (** l * a *)
  Definition lmulc (l : list A) (a : A) : list A := map (fun x => x * a) l.
  
  (** cmul keep its length *)
  Lemma lcmul_length : forall a l n, length l = n -> 
    length (lcmul a l) = n.
  Proof.
    intros. unfold lcmul. rewrite map_length; auto.
  Qed.
  
  (** a * l = l * a *)
  Lemma lmulc_lcmul : forall a l,
    lmulc l a == lcmul a l.
  Proof.
    induction l; simpl; try easy. apply cons_aeq_mor; auto.
    apply commutative.
  Qed.
  
  (** a * [] = [] *)
  Lemma lcmul_nil : forall a, lcmul a [] == [].
  Proof.
    intros. easy.
  Qed.
  
  (** [] * a = [] *)
  Lemma lmulc_nil : forall a, lmulc [] a == [].
  Proof.
    intros. easy.
  Qed.
  
  Context `{F:Field A Aadd A0 Aopp Amul A1 Ainv Aeq}.

  (** mul k x = x -> k = 1 \/ x = 0 *)
  Lemma fcmul_fixpoint_imply_k1_or_zero :
    forall (k x : A), (k * x == x)%A -> (k == A1)%A \/ (x == A0)%A.
  Proof.
    intros. destruct (decidable x A0); auto. left.
    apply symmetry in H.
    rewrite <- (@identityLeft _ Amul A1 Aeq) in H at 1.
    - apply field_mul_cancel_r in H; auto. easy.
    - apply monoidIdL.
  Qed.
  
  (** mul x k = x -> k = 1 \/ x = 0 *)
  Lemma fmulc_fixpoint_imply_k1_or_zero :
    forall (k x : A), (x * k == x)%A -> (k == A1)%A \/ (x == A0)%A.
  Proof.
    intros. rewrite commutative in H.
    apply fcmul_fixpoint_imply_k1_or_zero; auto.
  Qed.

  (** k * l = l -> k = 1 \/ l = 0 *)
  Lemma lcmul_fixpoint_imply_k1_or_lzero : 
    forall (l : list A) {n} (Hl : length l = n) (k : A),
      lcmul k l == l -> ((k == A1)%A \/ l == lzero A0 n).
  Proof.
    induction l; intros. subst; auto.
    destruct n. easy. simpl in *. inversion H. inversion Hl. subst.
    apply fcmul_fixpoint_imply_k1_or_zero in H3.
    destruct (decidable k A1).
    - left; auto.
    - right.
      apply cons_aeq_mor.
      + destruct H3; auto. easy.
      + destruct (IHl (length l) eq_refl k H5); auto. easy.
  Qed.
  
  (** lmulc is fixpoint, iff k1 or lzero *)
  Lemma lmulc_fixpoint_imply_k1_or_lzero : 
    forall (l : list A) {n} (Hl : length l = n) (k : A),
      lmulc l k == l -> ((k == A1)%A \/ l == lzero A0 n).
  Proof.
    intros.
    apply lcmul_fixpoint_imply_k1_or_lzero; auto.
    rewrite <- lmulc_lcmul. easy.
  Qed.

  (** k * l = 0 -> k = 0 \/ l = 0 *)
  Lemma lcmul_eq0_imply_k0_or_lzero : 
    forall (l : list A) {n} (Hl : length l = n) (k : A),
      lcmul k l == lzero A0 n -> ((k == A0)%A \/ l == lzero A0 n).
  Proof.
    induction l; intros. subst; auto.
    destruct n. easy. simpl in *. inv H.
    apply IHl in H5; try lia.
    apply field_mul_eq0_imply_a0_or_b0 in H3; auto.
    destruct H3; auto.
    destruct H5; auto.
  Qed.
  
End lcmul_lmulc.

(* ======================================================================= *)
(** ** product of two lists *)
Section ldot.
  
  (* Variable A : Type. *)
  (* Variable A0 : A. *)
  (* Variable add mul : A -> A -> A. *)
  (* Infix "+" := add. *)
  (* Infix "*" := mul. *)
  (* Variable add_comm : forall a b, a + b = b + a. *)
  (* Variable add_assoc : forall a b c, (a + b) + c = a + (b + c). *)
  (* Variable mul_assoc : forall a b c, (a * b) * c = a * (b * c). *)
  (* Variable mul_comm : forall a b, a * b = b * a. *)
  (* Variable mul_add_distr_l : forall a b1 b2, a * (b1 + b2) = a * b1 + a * b2. *)
  (* Variable mul_add_distr_r : forall a1 a2 b, (a1 + a2) * b = a1 * b + a2 * b. *)
  (* Variable add_0_l : forall a, A0 + a = a. *)
  (* Variable mul_0_l : forall a, A0 * a = A0. *)

  Context `{R:Ring}.
  Add Ring ring_inst : make_ring_theory.

  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).
  
  (** dot product, marked as l1 . l2 *)
  Definition ldot (l1 l2 : list A) : A :=
    fold_right Aadd A0 (map2 Amul l1 l2).

  (** map is respect to aeq *)
  Lemma ldot_aeq_mor : Proper (eqlistA Aeq ==> eqlistA Aeq ==> Aeq) ldot.
  Proof.
    unfold Proper, respectful.
    intros. unfold ldot. rewrite H,H0. easy.
  Qed.

  Global Existing Instance ldot_aeq_mor.


  (** l1 . l2 = l2 . l1 *)
  Lemma ldot_comm : forall (l1 l2 : list A),
    (ldot l1 l2 == ldot l2 l1)%A.
  Proof.
    intros. unfold ldot. rewrite map2_comm. easy.
  Qed.
  
  (** [] . l = 0 *)
  Lemma ldot_nil_l : forall (l : list A), (ldot nil l == A0)%A.
  Proof.
    intros. destruct l; simpl; try easy.
  Qed.
  
  (** l . [] = 0 *)
  Lemma ldot_nil_r : forall (l : list A), (ldot l nil == A0)%A.
  Proof.
    intros. destruct l; simpl; try easy.
  Qed.

  (** ldot cons *)
  Lemma ldot_cons : forall l1 l2 x1 x2,
    (ldot (x1 :: l1) (x2 :: l2) == (x1 * x2) + (ldot l1 l2))%A.
  Proof.
    induction l1,l2; simpl; intros; try easy.
  Qed.
  
  (** lzero . l = 0 *)
  Lemma ldot_zero_l : forall l n, (ldot (lzero A0 n) l == A0)%A.
  Proof.
    induction l,n; simpl; intros; try easy. rewrite ldot_cons.
    rewrite IHl. ring.
  Qed.
  
  (** l . lzero = 0 *)
  Lemma ldot_zero_r : forall l n, (ldot l (lzero A0 n) == A0)%A.
  Proof.
    intros. rewrite ldot_comm. apply ldot_zero_l.
  Qed.
  
  (** ldot left distributive over ladd.
    l1 . (l2 + l3) = l1.l2 + l1.l3 *)
  Lemma ldot_ladd_distr_l : forall l1 l2 l3 r,
    length l1 = r -> length l2 = r -> length l3 = r ->
    (ldot l1 (@ladd _ Aadd l2 l3) == (ldot l1 l2) + (ldot l1 l3))%A.
  Proof.
    induction l1,l2,l3; simpl; intros; subst; try (cbv;ring); try discriminate.
    rewrite ?ldot_cons. inversion H1. inversion H0.
    rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.
  
  (** ldot right distributive over ladd.
    (l1 + l2) . l3 = l1.l3 + l2.l3 *)
  Lemma ldot_ladd_distr_r : forall l1 l2 l3 r,
    length l1 = r -> length l2 = r -> length l3 = r ->
    (ldot (@ladd _ Aadd l1 l2) l3 == (ldot l1 l3) + (ldot l2 l3))%A.
  Proof.
    induction l1,l2,l3; simpl; intros; subst; try (cbv;ring); try discriminate.
    rewrite ?ldot_cons. inversion H1. inversion H0.
    rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.
  
  (** ldot left distributive over lcmul and mul.
      (x * l1) . l2 = x * (l1 . l2) *)
  Lemma ldot_lcmul_distr_l : forall l1 l2 x,
    (ldot (@lcmul _ Amul x l1) l2 == x * (ldot l1 l2))%A.
  Proof.
    induction l1,l2; simpl; intros; try (cbv; ring).
    rewrite ?ldot_cons. rewrite IHl1. ring.
  Qed.

  (** ldot right distributive over lcmul and mul.
      l1 . (x * l2) = x * (l1 . l2) *)
  Lemma ldot_lcmul_distr_r : forall l1 l2 x,
    (ldot l1 (@lcmul _ Amul x l2) == x * (ldot l1 l2))%A.
  Proof.
    induction l1,l2; simpl; intros; try (cbv; ring).
    rewrite ?ldot_cons. rewrite IHl1. ring.
  Qed.

  (** ldot left distributve over map2.
    dot (map l1 l2) l3 = dot l1 l3 + dot l2 l3 *)
  Lemma ldot_map2_distr_l : forall l1 l2 l3 r,
    length l1 = r -> length l2 = r -> length l3 = r ->
    (ldot (map2 Aadd l1 l2) l3 == (ldot l1 l3) + (ldot l2 l3))%A.
  Proof.
    induction l1,l2,l3; simpl in *; intros; subst; try (cbv; ring); try easy.
    rewrite ?ldot_cons.
    ring_simplify. rewrite IHl1 with (length l1); auto. ring.
  Qed.
  
  (** ldot right distributve over map2.
    dot l1 (map l2 l3) = dot l1 l2 + dot l1 l3 *)
  Lemma ldot_map2_distr_r : forall l1 l2 l3 r,
    length l1 = r -> length l2 = r -> length l3 = r ->
    (ldot l1 (map2 Aadd l2 l3) == (ldot l1 l2) + (ldot l1 l3))%A.
  Proof.
    induction l1,l2,l3; simpl in *; intros; subst; try (cbv; ring); try discriminate.
    rewrite ?ldot_cons. rewrite IHl1 with (length l1); auto; ring.
  Qed.

End ldot.


(* ======================================================================= *)
(** ** Generate special list for MatrixUnit *)
Section GenerateSpecialList.

  Context `{R:Ring}.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).
  
  (** create a list for matrix unit, which length is n and almost all elements 
    are A0 excepts i-th is A1. *)
  Fixpoint list_unit (n i : nat) : list A :=
    match n, i with
    | 0, _ => []
    | S n, 0 => A1 :: (repeat A0 n)
    | S n, S i => A0 :: (list_unit n i)
    end.

  (* Compute list_unit 0 2. (* [] *) *)
  (* Compute list_unit 3 0. (* [1;0;0] *) *)
  (* Compute list_unit 3 1. (* [0;1;0] *) *)
  (* Compute list_unit 3 2. (* [0;0;1] *) *)
  (* Compute list_unit 3 3. (* [0;0;0] *) *)

  Lemma list_unit_length : forall n i, length (list_unit n i) = n.
  Proof.
    induction n; auto. destruct i; simpl; auto. rewrite repeat_length. auto.
  Qed.
  
  (** list_unit(n,i) [i] = A1, when i < n *)
  Lemma list_unit_A1 : forall n i, i < n -> 
    (nth i (list_unit n i) A0 == A1)%A.
  Proof.
    induction n; try easy. destruct i; simpl; try easy.
    intros; apply IHn.
    (* since Coq_8.16.0, Arith.Lt was deprecated *)
    (* apply Lt.lt_S_n; auto. *)
    apply Nat.succ_lt_mono. auto.
  Qed.
  
  (** list_unit(n,i) [j] = A0, when i < n /\ j <> i *)
  Fact list_unit_spec1 : forall n i j, i < n -> j <> i ->
    (nth j (list_unit n i) A0 == A0)%A.
  Proof.
    induction n; try easy. intros. destruct i,j; simpl; try easy.
    - apply nth_repeat_same.
    - apply IHn; lia.
  Qed.
  
  (** list_unit(n,i) [j] = A0, j <> i *)
  Lemma list_unit_A0 : forall n i j, j <> i -> 
    (nth j (list_unit n i) A0 == A0)%A.
  Proof.
    induction n; try easy; simpl; intros.
    - destruct j; easy.
    - destruct i,j; simpl; try easy.
      apply nth_repeat_same. apply IHn. auto.
  Qed.
    
End GenerateSpecialList.

(* Arguments list_unit. *)


(* ======================================================================= *)
(** ** Convert list to fixed-length list *)
Section List2FixedlengthList.

  Context `{M:Monoid}.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).
  
  Fixpoint list_to_listN (l : list A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n' => (hd A0 l) :: (list_to_listN (tl l) n')
    end.
  
  Lemma list_to_listN_length : forall (l : list A) (n : nat),
    length (list_to_listN l n) = n.
  Proof.
    intros l n. gd l. induction n; intros; simpl; auto.
  Qed.
  
  Lemma list_to_listN_eq : forall (l : list A) (n : nat) 
    (H1 : length l = n), (list_to_listN l n == l).
  Proof.
    intros l n. gd l. induction n; intros; simpl.
    - apply (length_zero_iff_nil (Aeq:=Aeq)) in H1; easy.
    - rewrite IHn; destruct l; try easy. simpl. inversion H1. auto.
  Qed.

End List2FixedlengthList.

(* Arguments list_to_listN. *)
Arguments list_to_listN_length {A A0 l n}.

