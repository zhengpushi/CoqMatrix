(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension for list
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. reference "A Gentle Introduction to Type Classes and Relations in Coq"
  
  history   :
  1. 2021.12, by ZhengPu Shi.
     first version

  2. 2022.05, by ZhengPu Shi.
     split big file into small modules

  3. 2022.10, by ZhengPu Shi
     Setoid version

  4. 2023.11, by ZhengPu Shi
     Leibniz Equality version
 *)

Require Export List. Export ListNotations.
Require Export Hierarchy.
Require Export NatExt.

Open Scope nat_scope.
Open Scope A.
Open Scope list.

Generalizable Variables A B C.
Generalizable Variables Azero Aone Aadd Aopp Amul Ainv.


(* ======================================================================= *)
(** ** Properties of cons *)
Section cons.

  Context {A:Type}.
  
  (** Equality of cons, iff both parts are equal *)
  Lemma cons_eq_iff : forall (a1 a2 : A) (l1 l2 : list A),
      a1 :: l1 = a2 :: l2 <-> a1 = a2 /\ l1 = l2.
  Proof.
    intros. split; intros H; inversion H; subst; auto.
  Qed.

  (** Inequality of cons, iff at least one parts are not equal *)
  Lemma cons_neq_iff : forall (a1 a2 : A) (l1 l2 : list A),
      a1 :: l1 <> a2 :: l2 <-> (a1 <> a2) \/ (l1 <> l2).
  Proof.
    intros. split; intro H.
    - rewrite cons_eq_iff in H.
      apply not_and_or in H; auto.
    - intro. inversion H0. subst. destruct H; auto.
  Qed.

End cons.


(* ==================================== *)
(** ** Properties of hd and tl *)
Section hd_tl.
  
  Context {A:Type}.
  
  (** length of tl. (pred version) *)
  Lemma tl_length : forall (l : list A), length (tl l) = pred (length l).
  Proof.
    induction l; auto.
  Qed.

End hd_tl.

(* ==================================== *)
(** ** Properties of nth *)
Section nth.
  
  Context {A:Type}.

  (** nth [] a = a *)
  Lemma nth_nil : forall (a : A) (i : nat), nth i [] a = a.
  Proof.
    intros. destruct i; simpl; easy.
  Qed.

  (** Two list equal iff all nth visit equal *)
  Lemma list_eq_iff_nth (Azero : A) :
    forall n (l1 l2 : list A) (H1 : length l1 = n) (H2 : length l2 = n),
      l1 = l2 <-> (forall (i : nat), i < n -> nth i l1 Azero = nth i l2 Azero).
  Proof.
    intros n l1. revert n. induction l1; intros; simpl in *; subst.
    - split; intros; try easy. apply List.length_zero_iff_nil in H2. easy.
    - split; intros; try easy.
      + destruct l2; try easy.
        inversion H. subst. destruct i; simpl; auto.
      + destruct l2; simpl in *; try easy. f_equal.
        * specialize (H 0). simpl in H. apply H. lia.
        * rewrite (IHl1 (length l1)); auto. intros.
          specialize (H (S i)); simpl in H. apply H. lia.
  Qed.

  (** Get from repeat x and default value x always return x *)
  Lemma nth_repeat_same : forall (a : A) (n i : nat), nth i (repeat a n) a = a.
  Proof.
    intros a n. induction n; destruct i; simpl; easy.
  Qed.

End nth.


(* ==================================== *)
(** ** Set element of a list *)
Section chg.

  Context {A:Type}.

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

(* Let f_gen := fun (i : nat) => (i + 5). *)
(* Compute lst_chgf [1;2;3] 0 f_gen. *)
(* Compute lst_chgf [1;2;3] 1 f_gen. *)


(* ==================================== *)
(** ** Properties of length *)
Section length.

  Context {A:Type}.

  (** Redefine 'length_zero_iff_nil', original is opaque, make it transparent t *)
  Lemma length_zero_iff_nil : forall (l : list A), length l = 0 <-> l = [].
  Proof.
    intros. destruct l; intros; split; intros; auto; try easy.
  Defined.

  (** decompose a list which length is 1 *)
  Lemma list_length_1 : forall (l : list A),
      length l = 1 -> {x | l = [x]}.
  Proof. 
    destruct l; intros. inversion H. inversion H.
    apply length_zero_iff_nil in H1. subst. exists a. easy.
  Defined.

  (** a list has only one element equal to [hd _ l] *)
  Lemma list_length1_eq_hd : forall (x : A) (l:list A), 
      length l = 1 -> [hd x l] = l.
  Proof.
    intros x l. destruct l.
    - intros. simpl in *. lia.
    - intros. simpl in *. f_equal.
      apply eq_add_S in H. apply List.length_zero_iff_nil in H. subst. easy.
  Qed.

  (** decompose a list which length is S n *)
  Lemma list_length_Sn : forall (l : list A) n,
      length l = S n -> {x & { t | l = x :: t}}.
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
      (length (a :: l) = 1 /\ (a :: l <> [b]) -> (a <> b) /\ l = []).
  Proof.
    intros; destruct l. destruct H.
    - split; auto. intro; subst; easy.
    - destruct H. simpl in H. easy.
  Qed.

End length.

Section Test.
  Variable (A:Type) (a : A).
  Let l := [a].
  Definition h : length l = 1. auto. Defined.
  (* Compute proj1_sig (list_length_1 l h). *)
End Test.


(* ==================================== *)
(** ** Customized list induction *)
Section ind.

  Context {A:Type}.

  (** Connect induction principle between nat and list *)
  Lemma ind_nat_list : forall (P : list A -> Prop) ,
      (forall n l, length l = n -> P l) -> (forall l, P l).
  Proof.
    intros. apply (H (length l)). auto.
  Qed.

  (** Two step induction principle for list *)
  Theorem list_ind2 : forall (P : list A -> Prop),
      (P []) -> 
      (forall a, P [a]) -> 
      (forall l a b, P l -> P (a :: b :: l)) ->
      (forall l, P l).
  Proof.
    intros P H0 H1 H2. apply ind_nat_list. induction n using nat_ind2. 
    - intros. apply length_zero_iff_nil in H; subst; auto.
    - intros. apply list_length_1 in H. destruct H. subst; auto.
    - destruct l; auto. destruct l; auto.
      intros. apply H2. apply IHn. simpl in H. lia.
  Qed.

End ind.


(* ==================================== *)
(** ** list repeat properties *)
Section repeat.
  Context {A:Type}.

  (** repeat S n times equal to another form *)
  Lemma list_repeat_Sn (Azero : A) : forall n, repeat Azero (S n) = Azero :: repeat Azero n.
  Proof. intros. simpl. easy. Qed.

End repeat.


(* ==================================== *)
(** ** Zero list *)
Section lzero.
  Context {A:Type}.
  
  (** A friendly name for zero list *)
  Definition lzero (Azero : A) n := repeat Azero n.

  (** lzero's length law *)
  Lemma lzero_length (Azero : A) : forall n, length (lzero Azero n) = n.
  Proof. intros. apply repeat_length. Qed.

  (** append two zero list to a zero list satisfy length relation *)
  Lemma lzero_app (Azero : A) : forall n1 n2,
      lzero Azero n1 ++ lzero Azero n2 = lzero Azero (n1 + n2).
  Proof. unfold lzero. intros. rewrite repeat_app. easy. Qed.

End lzero.

(* ==================================== *)
(** ** Properties of map *)

(** map for two types *)
Section map_A_B.
  Context {A B:Type}.
  
  (** map is equal, imply the list is equal *)
  Lemma map_eq_imply_eq : forall (f : A -> B) (l1 l2 : list A),
      map f l1 = map f l2 -> Bijective f -> l1 = l2.
  Proof.
    intros f l1. induction l1; intros; destruct l2; simpl in *; try easy.
    inversion H. f_equal; auto.
    apply bijective_preserve_eq in H2; auto.
  Qed.

  (** map and repeat is communtative *)
  Lemma map_repeat (f : A -> B) : forall (a : A) n, 
      (map f (repeat a n)) = (repeat (f a) n).
  Proof.
    induction n; simpl; auto. f_equal; auto.
  Qed.
  
End map_A_B.

(** map for one type *)
Section map_A.
  Context {A:Type}.

  (** Extented map_id lemma, which needn't the function is a exactly format of
     "forall x, x" *)
  Lemma map_id : forall (l : list A) (f : A -> A) (H: forall a, f a = a), map f l = l.
  Proof.
    induction l; intros; simpl. easy. f_equal; auto.
  Qed.

  (** f x = zero -> map f = lzero *)
  Lemma map_eq_zero : forall l (Azero : A) (f : A -> A) n,
      (forall x : A, (f x = Azero)) -> length l = n -> map f l = lzero Azero n.
  Proof.
    induction l; intros; simpl in *. subst. simpl. easy.
    destruct n. easy. inv H0. simpl. f_equal; auto.
  Qed.
  
  (** Mapping is fixpoint, iff f is id *)
  Lemma map_fixpoint_imply_id (f : A -> A) : forall (l : list A), 
      map f l = l -> (forall x, In x l -> (f x = x)).
  Proof.
    induction l; intros; simpl in *. easy. inversion H.
    destruct H0. subst; auto. apply IHl; auto.
  Qed.

  (** Simplify of nth+map+seq *)
  Lemma nth_map_seq : forall i f n m (a0:A),
      i < m -> (nth i (map f (seq n m)) a0 = f (i + n)).
  Proof.
    intros. gd m. gd f. gd i. induction n.
    - intros i f m. gd f. gd i. induction m.
      + intros. lia.
      + intros. simpl. destruct i; try easy.
        rewrite <- seq_shift.
        rewrite List.map_map.
        rewrite IHm; try easy. lia.
    - intros. rewrite <- seq_shift. rewrite List.map_map. rewrite IHn; auto.
  Qed.

  (** Simplify of map+nth+seq *)
  (* Note: the lower index of seq is 0, it could extend to any nat number later *)
  Lemma map_nth_seq  : forall n (l : list A) Azero,
      length l = n -> map (fun i => nth i l Azero) (seq 0 n) = l.
  Proof.
    induction n.
    - intros. simpl. apply length_zero_iff_nil in H; subst. easy.
    - intros. simpl. destruct l.
      + simpl in *; lia.
      + f_equal. inversion H.
        rewrite <- seq_shift.
        rewrite map_map; auto. simpl.
        rewrite H1. rewrite IHn; easy.
  Qed.

  (** Equality of map+seq, iff corresponding elements are equal *)
  Lemma map_seq_eq : forall n (f g : nat -> A),
      map f (seq 0 n) = map g (seq 0 n) <-> (forall i, i < n -> (f i = g i)).
  Proof.
    intros; split; intros.
    - rewrite map_ext_in_iff in H. apply H. apply in_seq. lia.
    - apply map_ext_in_iff. intros. apply H. apply in_seq in H0. lia.
  Qed.

End map_A.


(* ==================================== *)
(** ** map two lists to a list *)
Section map2.
  Context {A B C:Type} (f : A -> B -> C).

  (** map operation to two list *)
  Fixpoint map2 (l1 : list A) (l2 : list B) : list C :=
    match l1, l2 with
    | x1 :: t1, x2 :: t2 => (f x1 x2) :: (map2 t1 t2)
    | _, _ => []
    end.
  
  (** length of map2 *)
  Lemma map2_length : forall (l1 : list A) (l2 : list B) n,
      length l1 = n -> length l2 = n -> length (map2 l1 l2) = n.
  Proof. 
    induction l1,l2; simpl; auto. intros. destruct n; simpl; auto. easy.
  Qed.
  
  (** map2 to two lists could be separated by two segments with same length *)
  Lemma map2_app : forall (la1 la2 : list A) (lb1 lb2 : list B),
      length la1 = length lb1 -> length la2 = length lb2 ->
      map2 (la1 ++ la2) (lb1 ++ lb2) = (map2 la1 lb1) ++ (map2 la2 lb2).
  Proof.
    induction la1, lb1; intros; simpl; auto; simpl in H; try easy.
    f_equal. auto.
  Qed.
  
  (** map2 [] l = [] *)
  Lemma map2_nil_l : forall l, map2 [] l = [].
  Proof. destruct l; easy. Qed.

  (** map2 l [] = [] *)
  Lemma map2_nil_r : forall l, map2 l [] = [].
  Proof. destruct l; easy. Qed.
  
End map2.

Arguments map2 {A B C}.


(* ==================================== *)
(** ** map2 on dlist *)
Section map2_dlist.
  Context {A B C:Type}.
  Variable f : A -> B -> C.
  
  (** tail of map2 to dlist, equal to map2 to tail part of original dlists *)
  Lemma tail_map2_dlist : forall dl1 dl2,
      tl (map2 (map2 f) dl1 dl2) =
        map2 (map2 f) (tl dl1) (tl dl2).
  Proof.
    destruct dl1, dl2; simpl; try easy. rewrite map2_nil_r. easy.
  Qed.

End map2_dlist.


(* ==================================== *)
(** ** map2 properties with same base type *)
Section map2_sametype.
  Context {A:Type} (Aadd:A->A->A) (Aopp:A->A).
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (-b)).

  (** nth (map2 f l1 l2) i = f (nth l1 i) (nth l2 i) *)
  Lemma map2_nth : forall (l1 l2 : list A) i (a : A),
      i < length l1 -> i < length l2 ->
      (nth i (map2 Aadd l1 l2) a = Aadd (nth i l1 a) (nth i l2 a)).
  Proof.
    induction l1; intros; simpl in *; try lia.
    destruct l2; simpl in *; try lia.
    destruct i; try easy.
    apply IHl1; try lia.
  Qed.

  (** l1 . l2 = l2 . l1 *)
  Context `{Comm:Commutative A Aadd}.
  Lemma map2_comm : forall (l1 l2 : list A), map2 Aadd l1 l2 = map2 Aadd l2 l1.
  Proof.
    induction l1; destruct l2; simpl; try easy. f_equal; auto. apply commutative.
  Qed.
  
  (** (l1 . l2) . l3 = l1 . (l2 . l3) *)
  Context {Assoc:Associative Aadd}.
  Lemma map2_assoc : forall (l1 l2 l3 : list A),
      map2 Aadd (map2 Aadd l1 l2) l3 = map2 Aadd l1 (map2 Aadd l2 l3).
  Proof.
    induction l1; destruct l2,l3; simpl; try easy. f_equal; auto.
    rewrite associative; auto.
  Qed.

  (** map2 over map is homorphism *)
  (* In fact, I don't know how to naming this property yet. *)
  Lemma map2_map_hom :
    forall l1 l2 (H : forall a b : A, (Aopp (Aadd a b) = Aadd (Aopp a) (Aopp b))),
      map2 Aadd (map Aopp l1) (map Aopp l2) = map Aopp (map2 Aadd l1 l2).
  Proof.
    intros. revert l2.
    induction l1; destruct l2; simpl; try easy.
    f_equal; auto.
  Qed.

  
  (** *** The properties below, need a monoid structure *)

  Context `{M:Monoid A Aadd Azero}.

  (** map2 lzero l = l *)
  Lemma map2_zero_l : forall l, map2 Aadd (lzero Azero (length l)) l = l.
  Proof.
    induction l; intros; simpl. easy. rewrite IHl. monoid_simpl.
  Qed.

  (** map2 l lzero = l *)
  Lemma map2_zero_r : forall l, map2 Aadd l (lzero Azero (length l)) = l.
  Proof.
    induction l; intros; simpl. easy. rewrite IHl. monoid_simpl.
  Qed.

  
  (** *** The properties below, need a group structure *)

  Context `{G:Group A Aadd Azero Aopp}.

  (* l1 - l2 = - (l2 - l1) *)
  (* Context {Invo_Aopp : Involution Aopp Aeq}. *)
  (* Context {ResBianry : RespectBinary Aadd Aeq Aeq Aeq}. *)
  Lemma map2_sub_comm : forall (l1 l2 : list A),
      map2 Asub l1 l2 = map Aopp (map2 Asub l2 l1).
  Proof.
    induction l1; destruct l2; intros; simpl in *; auto.
    f_equal; auto.
    rewrite group_inv_distr. rewrite group_inv_inv. easy.
  Qed.

  (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
  Lemma map2_sub_perm : forall (l1 l2 l3 : list A),
      map2 Asub (map2 Asub l1 l2) l3 = map2 Asub (map2 Asub l1 l3) l2.
  Proof.
    induction l1,l2,l3; simpl; auto. f_equal; auto. group_simpl.
    f_equal. apply commutative.
  Qed.
  
  (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
  Lemma map2_sub_assoc : forall (l1 l2 l3 : list A),
      map2 Asub (map2 Asub l1 l2) l3 = map2 Asub l1 (map2 Aadd l2 l3).
  Proof.
    induction l1,l2,l3; simpl; auto. f_equal; auto.
    rewrite associative. f_equal.
    rewrite group_inv_distr. apply commutative.
  Qed.

  (** 0 - l = - l *)
  Lemma map2_sub_zero_l : forall l n, 
      length l = n -> map2 Asub (lzero Azero n) l = map Aopp l.
  Proof.
    induction l; simpl; intros. apply map2_nil_r.
    induction n ; simpl. inversion H. f_equal; auto.
    group_simpl.
  Qed.
  
  (** l - 0 = l *)
  Lemma map2_sub_zero_r : forall l n, 
      length l = n -> map2 Asub l (lzero Azero n) = l.
  Proof.
    induction l; simpl; intros; auto. destruct n; simpl. inversion H.
    f_equal; auto.
    rewrite group_inv_id at 1. group_simpl.
  Qed.
  
  (** l - l = 0 *)
  Lemma map2_sub_self : forall l n, 
      length l = n -> map2 Asub l l = (lzero Azero n).
  Proof.
    induction l; simpl; intros; subst; try easy. simpl lzero.
    f_equal; auto. group_simpl.
  Qed.

End map2_sametype.

(** map2 with map of two components *)
Section map2_map_map.

  Context {A B : Type}.

  Lemma map2_map_map :
    forall (f1 f2 g : A -> B) (h : B -> B -> B)
      (H : forall x, (h (f1 x) (f2 x) = g x))
      (l : list A),
      map2 h (map f1 l) (map f2 l) = map g l.
  Proof.
    induction l; simpl; auto. f_equal; auto.
  Qed.

End map2_map_map.


(* ==================================== *)
(** ** concatenation of list *)
Section concat.

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

End concat.


(* ==================================== *)
(** ** Convert between list and function *)
Section f2l_l2f.
  Context {A:Type} {Azero:A}.

  Definition f2l {n : nat} (f : nat -> A) : list A :=
    map f (seq 0 n).

  Definition l2f {n : nat} (l : list A) : nat -> A :=
    fun i => nth i l Azero.

  Lemma f2l_length : forall n f, length (@f2l n f) = n.
  Proof.
    intros. unfold f2l. rewrite map_length. apply seq_length.
  Qed.

End f2l_l2f.

Section test.
  (** [1;2;3] *)
  Let f := fun i => i + 1.
  Let l := @f2l nat 3 f.
  (* Compute l. *)

  Let g := @l2f nat 0 3 l.
  (* Compute (g 0, g 1, g 2). *)
End test.  


(* ==================================== *)
(** ** Addition, Opposition and Subtraction of list *)
Section ladd_opp_sub.

  Context `{AG:AGroup A Aadd Azero Aopp}.
  Notation Asub := (fun a b => Aadd a (Aopp b)).

  (** l1 + l2 *)
  Definition ladd (l1 l2 : list A) : list A := map2 Aadd l1 l2.
  Infix "+" := ladd : list_scope.

  (** invariant for length of ladd *)
  Lemma ladd_length : forall l1 l2 n,
      length l1 = n -> length l2 = n -> length (l1 + l2) = n.
  Proof.
    intros. apply map2_length; auto.
  Qed.
  
  (** l1 + l2 = l2 + l1 *)
  Lemma ladd_comm : forall l1 l2, l1 + l2 = l2 + l1.
  Proof.
    apply map2_comm; auto. apply AG.
  Qed.
  
  (** [] + l = [] *)
  Lemma ladd_nil_l : forall l, ladd l [] = [].
  Proof.
    induction l; try easy.
  Qed.
  
  (** l + [] = [] *)
  Lemma ladd_nil_r : forall l, ladd [] l = [].
  Proof.
    try easy.
  Qed.
  
  (** 0 + l = l *)
  Lemma ladd_zero_l : forall l n, 
      length l = n -> ladd (lzero Azero n) l = l.
  Proof.
    induction l; simpl; intros. apply map2_nil_r.
    induction n ; simpl. inversion H.
    f_equal; auto.
    group_simpl.
  Qed.
  
  (** l + 0 = l *)
  Lemma ladd_zero_r : forall l n, length l = n -> ladd l (lzero Azero n) = l.
  Proof.
    intros. unfold ladd. rewrite map2_comm; auto.
    apply ladd_zero_l; auto. apply AG.
  Qed.
  
  (** - l *)
  Definition lopp (l : list A) : list A := map Aopp l.
  
  (** l1 - l2 *)
  Definition lsub (l1 l2 : list A) : list A := map2 Asub l1 l2.

  (** l1 - l2 = - (l2 - l1) *)
  Lemma lsub_comm : forall (l1 l2 : list A), lsub l1 l2 = lopp (lsub l2 l1).
  Proof.
    intros.
    apply map2_sub_comm with (Azero:=Azero). apply AG.
  Qed.
  
  (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
  Lemma lsub_perm : forall (l1 l2 l3 : list A),
      lsub (lsub l1 l2) l3 = lsub (lsub l1 l3) l2.
  Proof.
    apply map2_sub_perm; apply AG.
  Qed.
  
  (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
  Lemma lsub_assoc : forall (l1 l2 l3 : list A),
      lsub (lsub l1 l2) l3 = lsub l1 (ladd l2 l3).
  Proof.
    apply map2_sub_assoc with (Azero:=Azero); apply AG.
  Qed.
  
  (** 0 - l = - l *)
  Lemma lsub_zero_l : forall l n, length l = n -> lsub (lzero Azero n) l = lopp l.
  Proof.
    apply map2_sub_zero_l; apply AG.
  Qed.
  
  (** l - 0 = l *)
  Lemma lsub_zero_r : forall l n, length l = n -> lsub l (lzero Azero n) = l.
  Proof.
    apply map2_sub_zero_r; apply AG.
  Qed.
  
  (** l - l = 0 *)
  Lemma lsub_self : forall l n, length l = n -> lsub l l = (lzero Azero n).
  Proof.
    apply map2_sub_self; apply AG.
  Qed.
  
End ladd_opp_sub.


(* ==================================== *)
(** ** constant multiplication of list *)
Section lcmul_lmulc.
  
  Context `{R:Ring}.
  Add Ring ring_inst : make_ring_theory.

  Infix "*" := Amul : A_scope.
  Context `{Dec:Decidable A}.
  
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
      lmulc l a = lcmul a l.
  Proof.
    induction l; simpl; try easy. f_equal; auto.
    apply commutative.
  Qed.
  
  (** a * [] = [] *)
  Lemma lcmul_nil : forall a, lcmul a [] = [].
  Proof.
    intros. easy.
  Qed.
  
  (** [] * a = [] *)
  Lemma lmulc_nil : forall a, lmulc [] a = [].
  Proof.
    intros. easy.
  Qed.
  
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv}.
  Add Field field_inst : make_field_theory.

  (** mul k x = x -> k = 1 \/ x = 0 *)
  Lemma fcmul_fixpoint_imply_k1_or_zero :
    forall (k x : A), (k * x = x) -> (k = Aone) \/ (x = Azero).
  Proof.
    intros. destruct (decidable x Azero); auto. left.
    apply symmetry in H.
    rewrite <- (@identityLeft _ Amul Aone) in H at 1.
    - apply field_mul_cancel_r in H; auto.
    - apply monoidIdL.
  Qed.
  
  (** mul x k = x -> k = 1 \/ x = 0 *)
  Lemma fmulc_fixpoint_imply_k1_or_zero :
    forall (k x : A), (x * k = x) -> (k = Aone) \/ (x = Azero).
  Proof.
    intros. rewrite commutative in H.
    apply fcmul_fixpoint_imply_k1_or_zero; auto.
  Qed.

  (** k * l = l -> k = 1 \/ l = 0 *)
  Lemma lcmul_fixpoint_imply_k1_or_lzero : 
    forall (l : list A) {n} (Hl : length l = n) (k : A),
      lcmul k l = l -> ((k = Aone) \/ l = lzero Azero n).
  Proof.
    induction l; intros. subst; auto.
    destruct n. easy. simpl in *. inversion H. inversion Hl. subst.
    apply fcmul_fixpoint_imply_k1_or_zero in H1.
    destruct (decidable k Aone); auto. destruct H1; auto.
    right. f_equal.
    - rewrite H0. ring.
    - rewrite H2.
      specialize (IHl (length l) eq_refl k H2). destruct IHl; auto. easy.
  Qed.
  
  (** lmulc is fixpoint, iff k1 or lzero *)
  Lemma lmulc_fixpoint_imply_k1_or_lzero : 
    forall (l : list A) {n} (Hl : length l = n) (k : A),
      lmulc l k = l -> ((k = Aone) \/ l = lzero Azero n).
  Proof.
    intros.
    apply lcmul_fixpoint_imply_k1_or_lzero; auto.
    rewrite <- lmulc_lcmul. easy.
  Qed.

  (** k * l = 0 -> k = 0 \/ l = 0 *)
  Lemma lcmul_eq0_imply_k0_or_lzero : 
    forall (l : list A) {n} (Hl : length l = n) (k : A),
      lcmul k l = lzero Azero n -> ((k = Azero) \/ l = lzero Azero n).
  Proof.
    induction l; intros. subst; auto.
    destruct n. easy. simpl in *.
    inversion H. inversion Hl.
    specialize (IHl (length l) eq_refl k). rewrite H1,<-H3 in H2.
    specialize (IHl H2).
    destruct IHl; auto.
    - subst. left. ring.
    - apply field_mul_eq0_imply_a0_or_b0 in H1; auto. destruct H1.
      + left. subst. ring.
      + right. subst. f_equal; try ring.
        rewrite <- H0 in H2. auto.
  Qed.
  
End lcmul_lmulc.

(* ==================================== *)
(** ** product of two lists *)
Section ldot.
  
  Context `{R:Ring}.
  Add Ring ring_inst : make_ring_theory.

  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  
  (** dot product, marked as l1 . l2 *)
  Definition ldot (l1 l2 : list A) : A :=
    fold_right Aadd Azero (map2 Amul l1 l2).

  (** l1 . l2 = l2 . l1 *)
  Lemma ldot_comm : forall (l1 l2 : list A),
      (ldot l1 l2 = ldot l2 l1).
  Proof.
    intros. unfold ldot. rewrite map2_comm; auto. apply R.
  Qed.
  
  (** [] . l = 0 *)
  Lemma ldot_nil_l : forall (l : list A), (ldot nil l = Azero).
  Proof.
    intros. destruct l; simpl; try easy.
  Qed.
  
  (** l . [] = 0 *)
  Lemma ldot_nil_r : forall (l : list A), (ldot l nil = Azero).
  Proof.
    intros. destruct l; simpl; try easy.
  Qed.

  (** ldot cons *)
  Lemma ldot_cons : forall l1 l2 x1 x2,
      (ldot (x1 :: l1) (x2 :: l2) = (x1 * x2) + (ldot l1 l2)).
  Proof.
    induction l1,l2; simpl; intros; try easy.
  Qed.
  
  (** lzero . l = 0 *)
  Lemma ldot_zero_l : forall l n, (ldot (lzero Azero n) l = Azero).
  Proof.
    induction l,n; simpl; intros; try easy. rewrite ldot_cons.
    rewrite IHl. ring.
  Qed.
  
  (** l . lzero = 0 *)
  Lemma ldot_zero_r : forall l n, (ldot l (lzero Azero n) = Azero).
  Proof.
    intros. rewrite ldot_comm. apply ldot_zero_l.
  Qed.
  
  (** ldot left distributive over ladd.
    l1 . (l2 + l3) = l1.l2 + l1.l3 *)
  Lemma ldot_ladd_distr_l : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      (ldot l1 (@ladd _ Aadd l2 l3) = (ldot l1 l2) + (ldot l1 l3)).
  Proof.
    induction l1,l2,l3; simpl; intros; subst; try (cbv;ring); try discriminate.
    rewrite ?ldot_cons. inversion H1. inversion H0.
    rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.
  
  (** ldot right distributive over ladd.
    (l1 + l2) . l3 = l1.l3 + l2.l3 *)
  Lemma ldot_ladd_distr_r : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      (ldot (@ladd _ Aadd l1 l2) l3 = (ldot l1 l3) + (ldot l2 l3)).
  Proof.
    induction l1,l2,l3; simpl; intros; subst; try (cbv;ring); try discriminate.
    rewrite ?ldot_cons. inversion H1. inversion H0.
    rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.
  
  (** ldot left distributive over lcmul and mul.
      (x * l1) . l2 = x * (l1 . l2) *)
  Lemma ldot_lcmul_distr_l : forall l1 l2 x,
      (ldot (@lcmul _ Amul x l1) l2 = x * (ldot l1 l2)).
  Proof.
    induction l1,l2; simpl; intros; try (cbv; ring).
    rewrite ?ldot_cons. rewrite IHl1. ring.
  Qed.

  (** ldot right distributive over lcmul and mul.
      l1 . (x * l2) = x * (l1 . l2) *)
  Lemma ldot_lcmul_distr_r : forall l1 l2 x,
      (ldot l1 (@lcmul _ Amul x l2) = x * (ldot l1 l2)).
  Proof.
    induction l1,l2; simpl; intros; try (cbv; ring).
    rewrite ?ldot_cons. rewrite IHl1. ring.
  Qed.

  (** ldot left distributve over map2.
    dot (map l1 l2) l3 = dot l1 l3 + dot l2 l3 *)
  Lemma ldot_map2_distr_l : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      (ldot (map2 Aadd l1 l2) l3 = (ldot l1 l3) + (ldot l2 l3)).
  Proof.
    induction l1,l2,l3; simpl in *; intros; subst; try (cbv; ring); try easy.
    rewrite ?ldot_cons.
    rewrite (IHl1 l2 l3 (length l1)); auto. ring.
  Qed.
  
  (** ldot right distributve over map2.
    dot l1 (map l2 l3) = dot l1 l2 + dot l1 l3 *)
  Lemma ldot_map2_distr_r : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      (ldot l1 (map2 Aadd l2 l3) = (ldot l1 l2) + (ldot l1 l3)).
  Proof.
    induction l1,l2,l3; simpl in *; intros; subst;
      try (cbv; ring); try discriminate.
    rewrite ?ldot_cons. rewrite IHl1 with l2 l3 (length l1); auto; ring.
  Qed.

End ldot.


(* ==================================== *)
(** ** Generate special list for MatrixUnit *)
Section GenerateSpecialList.

  Context `{R:Ring}.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  
  (** create a list for matrix unit, which length is n and almost all elements 
    are Azero excepts i-th is Aone. *)
  Fixpoint list_unit (n i : nat) : list A :=
    match n, i with
    | 0, _ => []
    | S n, 0 => Aone :: (repeat Azero n)
    | S n, S i => Azero :: (list_unit n i)
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
  
  (** list_unit(n,i) [i] = Aone, when i < n *)
  Lemma list_unit_Aone : forall n i,
      i < n -> (nth i (list_unit n i) Azero = Aone).
  Proof.
    induction n; try easy. destruct i; simpl; try easy.
    intros; apply IHn.
    (* since Coq_8.16.0, Arith.Lt was deprecated *)
    (* apply Lt.lt_S_n; auto. *)
    apply Nat.succ_lt_mono. auto.
  Qed.
  
  (** list_unit(n,i) [j] = Azero, when i < n /\ j <> i *)
  Fact list_unit_spec1 : forall n i j,
      i < n -> j <> i -> (nth j (list_unit n i) Azero = Azero).
  Proof.
    induction n; try easy. intros. destruct i,j; simpl; try easy.
    - apply nth_repeat_same.
    - apply IHn; lia.
  Qed.
  
  (** list_unit(n,i) [j] = Azero, j <> i *)
  Lemma list_unit_Azero : forall n i j,
      j <> i -> (nth j (list_unit n i) Azero = Azero).
  Proof.
    induction n; try easy; simpl; intros.
    - destruct j; easy.
    - destruct i,j; simpl; try easy.
      apply nth_repeat_same. apply IHn. auto.
  Qed.
  
End GenerateSpecialList.

(* Arguments list_unit. *)


(* ==================================== *)
(** ** Convert list to fixed-length list *)
Section List2FixedlengthList.

  Context `{M:Monoid}.
  
  Fixpoint list_to_listN (l : list A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n' => (hd Azero l) :: (list_to_listN (tl l) n')
    end.
  
  Lemma list_to_listN_length : forall (l : list A) (n : nat),
      length (list_to_listN l n) = n.
  Proof.
    intros l n. gd l. induction n; intros; simpl; auto.
  Qed.
  
  Lemma list_to_listN_eq : forall (l : list A) (n : nat) 
                             (H1 : length l = n), (list_to_listN l n = l).
  Proof.
    intros l n. gd l. induction n; intros; simpl.
    - apply (length_zero_iff_nil) in H1; easy.
    - rewrite IHn; destruct l; try easy. simpl. inversion H1. auto.
  Qed.

End List2FixedlengthList.

(* Arguments list_to_listN. *)
Arguments list_to_listN_length {A Azero l n}.


(* ==================================== *)
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


(* ==================================== *)
(** ** Set element with a constant value *)
Section SetByConstant.
  
  (* --------------------------------------------------------------------- *)
  (** *** Modify a list list *)
  
  (** Definition *)
  Fixpoint dlst_chg {A} (dl : list (list A)) (i j : nat) (x : A) 
    : list (list A) :=
    match dl, i with
    | [], _ => []
    | l :: dl, 0 => (lst_chg l j x) :: dl
    | l :: dl, S i' => l :: (dlst_chg dl i' j x)
    end. 
  
  (* Compute dlst_chg [] 0 1 9. *)
  (* Compute dlst_chg [[1;2];[3;4;5]] 0 1 9. *)
  (* Compute dlst_chg [[1;2];[3;4;5]] 1 1 9. *)
  (* Compute dlst_chg [[1;2];[3;4;5]] 2 1 9. *)
  (* Compute dlst_chg [[1;2];[3;4;5]] 1 5 9. *)
  
  (** Length property *)
  Lemma dlst_chg_length : forall {A} dl i r j x, 
      length dl = r ->
      length (@dlst_chg A dl i j x) = r.
  Proof.
    intros A dl; induction dl; auto. destruct i; intros; auto; simpl in *.
    destruct r; auto. easy.
  Qed.
  
  (** Width property *)
  Lemma dlst_chg_width : forall {A} dl i c j x, 
      width dl c ->
      width (@dlst_chg A dl i j x) c.
  Proof.
    unfold width. intros A dl; induction dl; auto.
    destruct i; intros; simpl in *; auto; inv H; constructor; auto.
    apply lst_chg_length; auto.
  Qed.

End SetByConstant.


(* ==================================== *)
(** ** Set element with a generation function *)
Section SetByFunction.

  (** Inner version, i0 is given position, i is changed in every loop *)
  Fixpoint dlst_chgf_aux {A} (dl : list (list A)) (i0 i j : nat) 
    (f : nat -> nat -> A) 
    : list (list A) :=
    match dl, i with
    | [], _ => []
    | l :: dl, 0 => (lst_chgf l j (f i0)) :: dl
    | l :: dl, S i' => l :: (dlst_chgf_aux dl i0 i' j f)
    end. 
  
  (** User version that hide i0 parameter *)
  Definition dlst_chgf {A} (dl : list (list A)) (i j : nat) 
    (f : nat -> nat -> A) 
    : list (list A) :=
    dlst_chgf_aux dl i i j f.
  
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
  Lemma dlst_chgf_aux_length : forall {A} dl i r i0 j f, 
      length dl = r ->
      length (@dlst_chgf_aux A dl i0 i j f) = r.
  Proof.
    intros A dl; induction dl; auto. destruct i; auto; simpl; intros.
    destruct r; auto. easy.
  Qed.
  
  Lemma dlst_chgf_length : forall {A} dl r i j f, 
      length dl = r ->
      length (@dlst_chgf A dl i j f) = r.
  Proof.
    intros. apply dlst_chgf_aux_length. auto.
  Qed.
  
  (** Width property *)
  Lemma dlst_chgf_aux_width : forall {A} dl i c i0 j f, 
      width dl c ->
      width (@dlst_chgf_aux A dl i0 i j f) c.
  Proof.
    unfold width. intros A dl; induction dl; auto. 
    induction i; intros; simpl in *; auto; inv H; constructor; auto.
    apply lst_chgf_length; auto.
  Qed.
  
  Lemma dlst_chgf_width : forall {A} dl i c j f, 
      width dl c ->
      width (@dlst_chgf A dl i j f) c.
  Proof.
    intros. apply dlst_chgf_aux_width; auto.
  Qed.

End SetByFunction.


(* ==================================== *)
(** ** Set row with a constant value *)
Section SetRowByConstant.
  
  (** Definition *)
  Fixpoint dlst_chgrow {A} (dl : list (list A)) (i : nat) (x : list A) 
    : list (list A) :=
    match dl, i with
    | [], _ => []
    | l :: dl, 0 => x :: dl
    | l :: dl, S i' => l :: (dlst_chgrow dl i' x)
    end. 
  
  (*   Compute dlst_chgrow [] 0 [8;9].
  Compute dlst_chgrow [[1;2];[3;4;5]] 0 [8;9].
  Compute dlst_chgrow [[1;2];[3;4;5]] 1 [8;9].
  Compute dlst_chgrow [[1;2];[3;4;5]] 2 [8;9].
   *)  
  (** Length property *)
  Lemma dlst_chgrow_length : forall {A} dl i r x, 
      length dl = r ->
      length (@dlst_chgrow A dl i x) = r.
  Proof.
    intros A dl; induction dl; auto. destruct i; auto; intros; simpl in *.
    destruct r; auto. easy.
  Qed.
  
  (** Width property *)
  Lemma dlst_chgrow_width : forall {A} dl i c x,
      length x = c ->
      width dl c ->
      width (@dlst_chgrow A dl i x) c.
  Proof.
    unfold width; intros A dl; induction dl; auto. 
    induction i; intros; simpl in *; inv H0; constructor; auto.
  Qed.

End SetRowByConstant.


(* ==================================== *)
(** ** Set row with a generation function *)
Section SetRowByFunction.
  
  (** Inner version, i0 is given position, i is changed in every loop *)
  Fixpoint dlst_chgrowf_aux {A} (dl : list (list A)) (i0 i : nat) 
    (f : nat -> list A) 
    : list (list A) :=
    match dl, i with
    | [], _ => []
    | l :: dl, 0 => (f i0) :: dl
    | l :: dl, S i' => l :: (dlst_chgrowf_aux dl i0 i' f)
    end. 
  
  (** User version that hide i0 parameter *)
  Definition dlst_chgrowf {A} (dl : list (list A)) (i : nat) 
    (f : nat -> list A) 
    : list (list A) :=
    dlst_chgrowf_aux dl i i f.
  
  (*   Let f_gen := fun (i : nat) => [i+10;i+11;i+12].
  Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 f_gen.
  Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 f_gen.
  Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 2 f_gen.
  Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 3 f_gen.
   *) 
  
  (** Length property *)
  Lemma dlst_chgrowf_aux_length : forall {A} dl i r i0 f, 
      length dl = r ->
      length (@dlst_chgrowf_aux A dl i0 i f) = r.
  Proof.
    intros A dl; induction dl; auto. induction i; auto.
    intros. simpl. destruct r; auto. easy.
  Qed.
  
  Lemma dlst_chgrowf_length : forall {A} dl r i f, 
      length dl = r ->
      length (@dlst_chgrowf A dl i f) = r.
  Proof.
    intros. apply dlst_chgrowf_aux_length. auto.
  Qed.
  
  (** Width property *)
  Lemma dlst_chgrowf_aux_width : forall {A} dl i c i0 f, 
      length (f i0) = c ->
      width dl c ->
      width (@dlst_chgrowf_aux A dl i0 i f) c.
  Proof.
    unfold width; intros A dl; induction dl; auto. 
    induction i; intros; simpl in *; auto; inv H0; constructor; auto.
  Qed.
  
  Lemma dlst_chgrowf_width : forall {A} dl i c f, 
      length (f i) = c ->
      width dl c ->
      width (@dlst_chgrowf A dl i f) c.
  Proof.
    intros. apply dlst_chgrowf_aux_width; auto.
  Qed.

End SetRowByFunction.


(* ==================================== *)
(** ** Properties of dlist *)
Section props_dlist.
  Context {A:Type} {Azero:A}.
  Open Scope nat.

  (** ** Length of a empty dlist *)
  Lemma dlist_h0_iff : forall (dl : list (list A)), 
      length dl = 0 -> dl = nil.
  Proof.
    destruct dl; simpl; auto. intros H; easy.
  Qed.
  
  (** Two list list equal iff all nth nth visit equal *)
  Lemma dlist_eq_iff_nth_nth :
    forall r c (dl1 dl2 : list (list A))
      (H1 : length dl1 = r) (H2 : length dl2 = r)
      (H3 : width dl1 c) (H4 : width dl2 c),
      dl1 = dl2 <->
        (forall (i j : nat), i < r -> j < c -> 
                      (nth j (nth i dl1 []) Azero =
                         nth j (nth i dl2 []) Azero)).
  Proof.
    intros; split; intros.
    - rewrite H. easy.
    - apply (list_eq_iff_nth [] _ dl1 dl2 H1 H2). intros. subst.
      rewrite (list_eq_iff_nth) with (n:=c); auto;
        apply width_imply_nth_length; auto. lia.
  Qed.

  (** dlist_eq is decidable *)
  Context `{Aeq_dec : Decidable A}.
  Lemma dlist_eq_dec : forall (dl1 dl2 : list (list A)), {dl1 = dl2} + {~(dl1 = dl2)}.
  Proof.
    apply list_eq_dec.
    apply list_eq_dec. apply Aeq_dec.
  Qed.

End props_dlist.



(* ==================================== *)
(** ** a dlist with same element nil *)
Section dnil.
  
  Context `{M:Monoid}.
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
      dnil (n1 + n2) = dnil n1 ++ dnil n2.
  Proof.
    induction n1,n2; simpl; try easy.
    - rewrite app_nil_r. rewrite Nat.add_0_r. easy.
    - rewrite IHn1. simpl. easy.
  Qed.

  (** width dl is zero imply it is a dnil *)
  Lemma dlist_w0_eq_dnil : forall (dl : list (list A)), 
      width dl 0 -> dl = dnil (length dl).
  Proof.
    unfold width; induction dl; simpl; auto.
    intros. inv H. f_equal; auto. 
    apply length_zero_iff_nil; auto.
  Qed.

  (** rev a dnil is itself *)
  Lemma dnil_rev : forall n, rev (dnil n) = dnil n.
  Proof.
    induction n; simpl; auto. rewrite IHn. clear IHn.
    induction n; simpl; auto. f_equal. auto.
  Qed.

End dnil.


(* ==================================== *)
(** ** map2 *)
Section map2.
  Context {A B C:Type}.
  Variable f : A -> B -> C.
  
  Open Scope nat.

  (** map2 dnil dl = dnil *)
  Lemma map2_dnil_l : forall dl n, 
      length dl = n -> map2 (map2 f) (dnil n) dl = dnil n.
  Proof.
    intros. gd dl. induction n; intros; simpl; try easy.
    destruct dl. inversion H. inversion H. rewrite H1. f_equal. auto.
  Qed.

  (** map2 dl dnil = dnil *)
  Lemma map2_dnil_r : forall dl n, 
      length dl = n -> map2 (map2 f) dl (dnil n) = dnil n.
  Proof.
    intros. gd dl. induction n; intros; simpl; try easy.
    - rewrite map2_nil_r. easy.
    - destruct dl. easy. simpl. rewrite IHn; auto. rewrite map2_nil_r. easy.
  Qed.

End map2.


(* ==================================== *)
(** ** Convert between dlist and function *)
Section f2dl_dl2f.
  Context {A:Type} {Azero:A}.

  Definition f2dl {r c : nat} (f : nat -> nat -> A) : list (list A) :=
    map (fun i => f2l (n:=c) (f i)) (seq 0 r).

  Definition dl2f {r c : nat} (dl : list (list A)) : nat -> nat -> A :=
    fun i j => nth j (nth i dl []) Azero.

  Lemma f2dl_length : forall r c f, length (@f2dl r c f) = r.
  Proof.
    intros. unfold f2dl. rewrite map_length. apply seq_length.
  Qed.

  Lemma f2dl_width : forall r c f, width (@f2dl r c f) c.
  Proof.
    unfold f2dl,width.
    induction r; intros; simpl; try constructor.
    - apply f2l_length.
    - rewrite <- seq_shift. rewrite List.map_map.
      apply IHr.
  Qed.

End f2dl_dl2f.

Section test.
  (** [[1;2;3];[4;5;6];[7;8;9]] *)
  Let f := fun i j => i * 3 + j + 1.
  Let dl := @f2dl nat 3 3 f.
  (* Compute dl. *)

  Let g := @dl2f nat 0 3 3 dl.
  (* Compute (g 0 0, g 0 1, g 0 2, g 1 0, g 1 1, g 1 2, g 2 0, g 2 1, g 2 2). *)
End test.  


(* ==================================== *)
(** ** Convert between row and col. eg, [1;2;3] <-> [[1];[2];[3]] *)
Section convert_row_and_col.

  Context `{M:Monoid}.
  
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
      (nth i (row2col l) [] = [nth i l Azero]).
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
    | l :: tl => (hd Azero l) :: (col2row tl)
    end.
  
  (** Convert a dlist to list then convert it to a dlist, equal to original dlist. *)
  Lemma row2col_col2row : forall (dl : list (list A)),
      width dl 1 -> row2col (col2row dl) = dl.
  Proof.
    unfold width; induction dl; simpl; auto; intros. inv H.
    f_equal; auto.
    destruct a; simpl in *; try easy. inv H2.
    apply length_zero_iff_nil in H0. subst. easy.
  Qed.
  
  (** Convert a list to dlist then convert it to a list, equal to original 
    list. *)
  Lemma col2row_row2col : forall (l : list A), 
      (col2row (row2col l) = l).
  Proof.
    induction l; simpl; auto; intros. rewrite IHl. easy.
  Qed.
  
End convert_row_and_col.


(* ==================================== *)
(** ** head column of a dlist *)
Section hdc.
  Context {A : Type} {Azero : A}.
  
  (** Get head column of a dlist *)
  Fixpoint hdc (dl : list (list A)) : list A :=
    match dl with
    | [] => []
    | l :: tl => (hd Azero l) :: (hdc tl)
    end.
  
  (** hdc length law *)
  Lemma hdc_length : forall dl, length (hdc dl) = length dl.
  Proof.
    induction dl; simpl; auto.
  Qed.
  
End hdc.

Arguments hdc {A}.


(* ==================================== *)
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
    apply length_zero_iff_nil in H2. subst. auto.
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


(* ==================================== *)
(** ** construct a dlist with a list and a dlist by column *)
Section consc.
  Context {A:Type} {Azero:A}.
  
  (** Construct a dlist by column with a list and a dlist *)
  Fixpoint consc (l : list A) (dl : list (list A)) : list (list A) :=
    match l, dl with
    | xl :: tl, xdl :: tdl => (xl :: xdl) :: (consc tl tdl)
    | _, _ => []
    end.
  
  (** consc_eq, seems like f_equal *)
  Lemma consc_eq_iff : forall (l1 l2 : list A) (dl1 dl2 : list (list A)) n
                         (H1:length l1 = n) (H2:length l2 = n)
                         (H3:length dl1 = n) (H4:length dl2 = n),
      consc l1 dl1 = consc l2 dl2 <-> (l1 = l2) /\ dl1 = dl2.
  Proof.
    induction l1.
    - intros. simpl in *. subst. apply length_zero_iff_nil in H4,H3,H2.
      subst. easy.
    - intros. destruct l2,dl1,dl2; simpl in *; subst; try easy.
      inv H2. inv H3. inv H4. split; intros.
      + inv H. rewrite IHl1 in H6; auto. inv H6. auto.
      + inv H. inv H3. inv H4. auto.
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
      consc (hdc Azero dl) (tlc dl) = row2col (repeat Azero r).
  Proof.
    unfold width; induction dl; simpl; intros; subst; try easy.
    inv H0. apply length_zero_iff_nil in H2. subst. simpl. f_equal.
    apply IHdl; auto.
  Qed.
  
  (** consc with hdc and tlc of a dlist generate itself *)
  Lemma consc_hdc_tlc_widthS : forall dl c, 
      width dl (S c) ->
      consc (hdc Azero dl) (tlc dl) = dl.
  Proof.
    unfold width; induction dl; simpl; intros; auto. inv H.
    f_equal; auto.
    - destruct a; simpl in *. easy. easy.
    - apply IHdl with (c:=c). auto.
  Qed.

  (** consc decompose.
    x1::l1 ++ l2::dl2 = (x::l2) :: (l1 ++ dl2)  *)
  Lemma consc_decompose : forall x1 l1 l2 dl2,
      consc (x1::l1) (l2::dl2) = (x1::l2) :: (consc l1 dl2).
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** repeat (x :: l) decomposition *)
  Lemma repeat_consr : forall l x n,
      repeat (x :: l) n = consc (repeat x n) (repeat l n).
  Proof.
    induction n; simpl; auto. rewrite IHn. easy.
  Qed.

End consc.


(* ==================================== *)
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


(* ==================================== *)
(** ** Zero dlist *)
Section dlzero.
  Context {A:Type} {Azero:A}.
  
  (** dlist constructed by repeated lzero, named as dlzero *)
  Definition dlzero r c := repeat (lzero Azero c) r.

  (** dlzero rewrite *)
  Lemma dlzero_rw : forall r c, repeat (lzero Azero c) r = dlzero r c.
  Proof.
    easy.
  Qed.
  
  (** dlzero with S r rows could be splited to two parts *)
  Lemma dlzero_Sr : forall {r c}, dlzero (S r) c = (lzero Azero c) :: (dlzero r c).
  Proof.
    intros. simpl. cbn. easy.
  Qed.
  
  (** dlzero with 0 rows equal to dnil *)
  Lemma dlzero_dnil : forall {c}, dlzero c 0 = dnil c.
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
  Lemma dlzero_w0_eq_dnil : forall r, (dlzero r 0) = dnil r.
  Proof. 
    induction r; try easy. unfold dlzero in *. simpl in *. rewrite IHr. easy.
  Qed.
  
  (** append two dlzeros by row equal to whole *)
  Lemma dlzero_app_row : forall r1 r2 c,
      dlzero r1 c ++ dlzero r2 c = dlzero (r1 + r2) c.
  Proof.
    unfold dlzero. intros. rewrite repeat_app. easy.
  Qed.
  
  (** append two dlzeros by column equal to whole *)
  Lemma dlzero_app_col : forall r c1 c2,
      ((dlzero r c1) @@ (dlzero r c2))%dlist = dlzero r (c1 + c2).
  Proof.
    induction r; intros; simpl; try easy. unfold dlzero,lzero in *.
    rewrite IHr. simpl. rewrite repeat_app. easy.
  Qed.

End dlzero.

Arguments dlzero {A}.


(* ==================================== *)
(** ** transpose a dlist *)
Section dltrans.
  Context {A:Type} {Azero:A}.
  
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
  Lemma dltrans_nil : forall n, dltrans (dnil n) 0 = [].
  Proof.
    intros. destruct n; simpl. reflexivity. easy.
  Qed.
  
  (** dltrans consr = consc dltrans *)
  Lemma dltrans_consr : forall dl l c,
      dltrans (l :: dl) c = consc l (dltrans dl c).
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** dltrans consc = consr dltrans *)
  Lemma dltrans_consc : forall dl l r c,
      length l = r -> length dl = r -> width dl c ->
      dltrans (consc l dl) (S c) = l :: (dltrans dl c).
  Proof.
    unfold width; induction dl; simpl; intros; subst.
    - destruct l; simpl; try easy.
    - destruct l. easy.
      inv H0. inv H1.
      specialize (IHdl l (length l) (length a) eq_refl H2 H4).
      simpl.
      destruct (dltrans (consc l dl) (S (length a))). easy. inv IHdl. auto.
  Qed.
  
  (** dltrans twice return back *)
  Lemma dltrans_trans : forall dl r c,
      length dl = r -> width dl c ->
      dltrans (dltrans dl c) r = dl.
  Proof.
    induction dl; intros; simpl in *.
    - subst. destruct c; simpl; auto.
    - destruct r. easy. inv H. inv H0.
      unfold width in *.
      rewrite dltrans_consc with (r:=length a);
        auto using dltrans_length, dltrans_width.
      f_equal; auto.
  Qed.
  
  (** dltrans dlzero<r,c> = dlzero<c,r> *)
  Lemma dltrans_zero : forall r c,
      dltrans (dlzero Azero r c ) c = dlzero Azero c r.
  Proof.
    induction r; intros; simpl; auto. rewrite dlzero_dnil; easy.
    unfold dlzero in *; simpl in *. rewrite IHr.
    rewrite repeat_consr. easy.
  Qed.
  
End dltrans.


(* ==================================== *)
(** ** dlist unit, like a identity matrix *)
Section dlunit.
  Context {A:Type} {Azero Aone:A}.
  
  (** Build a identity matrix with list list. *)
  (* there are 4 parts of a dlunit [n x n]: 
      left top element [1 x 1], 
      right top list [1 x (n-1)], 
      left bottom list [(n-1) x 1],
      right bottom square is another small dlunit [(n-1) x (n-1)] *)
  Fixpoint dlunit (n : nat) : list (list A) :=
    match n with
    | O => []
    | S n0 => (Aone :: (repeat Azero n0)) :: (consc (repeat Azero n0) (dlunit n0))
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
      dltrans u n = u.
  Proof.
    simpl. induction n; simpl; try easy.
    assert ((dltrans (consc (repeat Azero n) (dlunit n)) (S n)) =
              (repeat Azero n) :: (dltrans (dlunit n) n)).
    { apply dltrans_consc with (r:=n).
      apply repeat_length. apply dlunit_length. apply dlunit_width. }
    destruct (dltrans (consc (repeat Azero n) (dlunit n)) (S n)). easy.
    inv H. f_equal. f_equal. auto.
  Qed.

End dlunit.

Arguments dlunit {A}.


(* ==================================== *)
(** ** map of dlist with f : A -> B *)
Section dmap_A_B.
  Context {A B:Type}.
  Variable f : A -> B.
  
  (** map operation to dlist *)
  Definition dmap dl := map (map f) dl.

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
  Lemma dmap_cons : forall l dl, dmap (l :: dl) = (map f l) :: (dmap dl).
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** dmap distributive law by append *)
  Lemma dmap_app : forall dl1 dl2,
      dmap (dl1 ++ dl2) = (dmap dl1) ++ (dmap dl2).
  Proof.
    induction dl1; destruct dl2; simpl in *; rewrite ?app_nil_r; try easy.
    rewrite IHdl1. easy.
  Qed.
  
  (** dmap dnil = dnil *)
  Lemma dmap_dnil : forall n, dmap (dnil n) = dnil n.
  Proof.
    induction n; simpl; try easy. rewrite IHn. easy.
  Qed.
  
End dmap_A_B.


(* ==================================== *)
(** ** map of dlist with f : A -> B *)
Section dmap_A_B.
  Context {A B:Type}.

  (** dmap extensional law  *)
  Lemma dmap_ext : forall dl (f g : A -> B) (H : forall a, f a = g a),
      (dmap f dl = dmap g dl)%dlist.
  Proof.
    intros. unfold dmap.
    apply map_ext. intros. induction a; simpl; auto. f_equal; auto.
  Qed.
  
End dmap_A_B.


(* ==================================== *)
(** ** map of dlist with f : A -> A *)
Section dmap_A_A.
  Context {A:Type} {Azero:A}.

  (** dmap (fun x => Azero) dl = dlzero Azero r c *)

  Lemma dmap_eq_zero : forall {r c} dl,
      length dl = r -> width dl c ->
      dmap (fun (x:A) => Azero) dl = dlzero Azero r c.
  Proof.
    intros. unfold dmap,dlzero.
    
    (* Note that, use "map_eq_zero" cannot prove this lemma.
       Although this method looks very simple. *)
    (* apply map_eq_zero; auto. intros. apply map_eq_zero; try easy. *)
    
    revert r c H H0.
    induction dl; intros; simpl in *.
    - subst. easy.
    - destruct r; try easy. inv H. inv H0. simpl. f_equal.
      + apply map_eq_zero; auto.
      + apply IHdl; auto.
  Qed.

End dmap_A_A.


(* ==================================== *)
(** ** map2 of dlist *)
Section dmap2.
  Context {A B C:Type}.
  Variable f : A -> B -> C.
  
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
      dmap2 (l1 :: dl1) (l2 :: dl2) =
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
      dmap2 (consc l1 dl1) (consc l2 dl2) =
        consc (map2 f l1 l2) (dmap2 dl1 dl2).
  Proof.
    unfold width; induction l1,dl1,l2,dl2; simpl; intros; try easy.
    (* destruct r,t; try easy. *)
    inv H. inv H0. inv H1. inv H2. inv H3. inv H4.
    f_equal; try easy. apply IHl1 with (c:=length l); auto.
  Qed.
  
  (** dmap2 and add *)
  Lemma dmap2_app : forall dla1 dla2 dlb1 dlb2,
      length dla1 = length dlb1 ->
      length dla2 = length dlb2 ->
      dmap2 (dla1 ++ dla2) (dlb1 ++ dlb2) =
        (dmap2 dla1 dlb1) ++ (dmap2 dla2 dlb2).
  Proof.
    intros. unfold dmap2. apply map2_app; auto.
  Qed.
  
  (** dmap2 dnil dl = dnil *)
  Lemma dmap2_dnil_l : forall dl n,
      length dl = n ->
      dmap2 (dnil n) dl = dnil n.
  Proof.
    intros. unfold dmap2. rewrite map2_dnil_l; easy.
  Qed.

  (** dmap2 dl dnil = dnil *)
  Lemma dmap2_dnil_r : forall dl n,
      length dl = n ->
      dmap2 dl (dnil n) = dnil n.
  Proof.
    intros. unfold dmap2. rewrite map2_dnil_r; easy.
  Qed.

  Lemma dmap2_tail : forall dl1 dl2,
      length dl1 = length dl2 ->
      tl (dmap2 dl1 dl2) = dmap2 (tl dl1) (tl dl2).
  Proof.
    intros. unfold dmap2. apply tail_map2_dlist.
  Qed.

  (** Relationship between dltrans and dmap2 *)
  Lemma dltrans_dmap2 : forall dl1 dl2 c,
      length dl1 = length dl2 ->
      width dl1 c -> width dl2 c ->
      dltrans (dmap2 dl1 dl2) c =
        dmap2 (dltrans dl1 c) (dltrans dl2 c).
  Proof.
    unfold width; induction dl1; intros; simpl in *; subst.
    rewrite dmap2_dnil_l; auto using dltrans_length.
    destruct dl2; simpl.
    - inv H.
    - inv H. inv H0. inv H1. rewrite IHdl1; auto.
      erewrite dmap2_consc; auto using dltrans_width, dltrans_length; try easy.
      rewrite dltrans_length; auto.
      rewrite dltrans_length; auto.
  Qed.
  
End dmap2.


(* ==================================== *)
(** ** dmap2 with same base type *)
Section dmap2_sametype.
  Context {A:Type} {Aadd:A->A->A}.
  Infix "+" := Aadd.
  
  Context {Comm : Commutative Aadd}.
  (** dl1 . dl2 = dl2 . dl1 *)
  Lemma dmap2_comm : forall (dl1 dl2 : list (list A)),
      dmap2 Aadd dl1 dl2 = dmap2 Aadd dl2 dl1.
  Proof.
    induction dl1,dl2; simpl; auto. f_equal; auto.
    apply map2_comm. auto.
  Qed.

  (** (dl1 . dl2) . dl3 = dl1 . (dl2 . dl3) *)
  Context {Assoc : Associative Aadd}.
  Lemma dmap2_assoc : forall (dl1 dl2 dl3 : list (list A)),
      dmap2 Aadd (dmap2 Aadd dl1 dl2) dl3 =
        dmap2 Aadd dl1 (dmap2 Aadd dl2 dl3).
  Proof.
    induction dl1,dl2,dl3; simpl; auto. f_equal; auto.
    apply map2_assoc. auto.
  Qed.
  
  (** dmap2 with dmap of two components *)
  Lemma dmap2_dmap_dmap : forall (f1 f2 g : A -> A) (h : A -> A -> A) 
                            (H : forall x, g x = h (f1 x) (f2 x)) l,
      dmap2 h (dmap f1 l) (dmap f2 l) = dmap g l.
  Proof.
    induction l; simpl; auto. rewrite IHl. f_equal; try easy.
    apply map2_map_map. easy.
  Qed.

  (** dmap2 over dmap is homorphism *)
  Lemma dmap2_dmap_hom : forall (Aopp : A -> A)
                           (H : forall a b : A, (Aopp (a + b) = (Aopp a) + (Aopp b)))
                           d1 d2,
      dmap2 Aadd (dmap Aopp d1) (dmap Aopp d2) = dmap Aopp (dmap2 Aadd d1 d2).
  Proof.
    intros. revert d2.
    induction d1,d2; simpl; try easy. rewrite IHd1. rewrite map2_map_hom. easy.
    easy.
  Qed.
  
End dmap2_sametype.


(* ==================================== *)
(** ** Square Zero dlist *)
Section sdlzero.
  Context {A:Type} (Azero:A).

  (** Square dlist with element zero *)
  Definition sdlzero n := repeat (repeat Azero n) n.
  
  (** dim(sdl0) = rows(dl0) = cols(dl0) -> sdl0 = dl0 *)
  Lemma sdlzero_eq_dlzero_r : forall r c,
      r = c -> sdlzero r = dlzero Azero r c.
  Proof.
    intros. subst. unfold sdlzero, dlzero. easy.
  Qed.
  
  (** dim(sdl0) = rows(dl0) = cols(dl0) -> sdl0 = dl0 *)
  Lemma sdlzero_eq_dlzero_c : forall r c,
      r = c -> sdlzero c = dlzero Azero r c.
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


(* ==================================== *)
(** ** dmap2 is considered as dladd *)
Section dladd.

  Context `{AG:AGroup}.
  Infix "+" := Aadd.
  
  (** dl + 0 = dl *)
  Lemma dladd_zero_l : forall dl r c, 
      length dl = r -> width dl c ->
      dmap2 Aadd (dlzero Azero r c) dl = dl.
  Proof.
    unfold width, dlzero in *.
    induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - destruct r. easy. inv H. inv H0.
      simpl. f_equal; auto.
      rewrite map2_zero_l. easy. apply AG.
  Qed.
  
  (** 0 + dl = dl *)
  Lemma dladd_zero_r : forall dl r c, 
      length dl = r -> width dl c ->
      dmap2 Aadd dl (dlzero Azero r c) = dl.
  Proof.
    intros. rewrite dmap2_comm; auto. apply dladd_zero_l; auto.
  Qed.

End dladd.


(* ==================================== *)
(** ** dmap2 is considered as dlsub *)
Section dlsub.

  Context `{AG:AGroup}.
  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  Infix "-" := (fun a b => a + (-b)).
  
  (** dl1 - dl2 = - (dl2 - dl1) *)
  Lemma dlsub_comm : forall dl1 dl2 c,
      let Asub := fun a b => a + (-b) in
      length dl1 = length dl2 ->
      width dl1 c -> width dl2 c ->
      dmap2 Asub dl1 dl2 = dmap Aopp (dmap2 Asub dl2 dl1).
  Proof.
    induction dl1,dl2; simpl; intros; auto. f_equal.
    - rewrite map2_sub_comm with (Azero:=Azero). easy. apply AG.
    - inv H. inv H0. inv H1.
      apply IHdl1 with (c:=length a); auto.
  Qed.
  
  (** (dl1 - dl2) - dl3 = dl1 - (dl2 + dl3) *)
  Lemma dlsub_assoc : forall dl1 dl2 dl3 c, 
      let Asub := fun a b => a + (-b) in
      length dl1 = length dl2 -> length dl2 = length dl3 ->
      width dl1 c -> width dl2 c ->
      dmap2 Asub (dmap2 Asub dl1 dl2) dl3 =
        dmap2 Asub dl1 (dmap2 Aadd dl2 dl3).
  Proof.
    induction dl1,dl2,dl3; simpl; intros; auto. f_equal.
    - apply map2_sub_assoc with (Azero:=Azero); apply AG.
    - inv H. inv H0. unfold width in *. inv H1. inv H2.
      apply IHdl1 with (c:=length a); auto.
  Qed.
  
  (** 0 - dl = - dl *)
  Lemma dlsub_zero_l : forall dl r c, 
      let Asub := fun a b => a + (-b) in
      length dl = r -> width dl c ->
      dmap2 Asub (dlzero Azero r c) dl =
        dmap Aopp dl.
  Proof.
    induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - induction r. easy. inv H. inv H0. simpl.
      unfold dlzero in *. f_equal; auto.
      apply lsub_zero_l; auto.
  Qed.
  
  (** dl - 0 = dl *)
  Lemma dlsub_zero_r : forall dl r c, 
      let Asub := fun a b => a + (-b) in
      length dl = r -> width dl c ->
      dmap2 Asub dl (dlzero Azero r c) = dl.
  Proof.
    induction dl; simpl; intros; auto. destruct r; simpl. easy.
    inv H. inv H0. f_equal; auto.
    - apply lsub_zero_r; auto.
    - apply IHdl; auto. 
  Qed.
  
  (** dl - dl = 0 *)
  Lemma dlsub_self : forall dl r c, 
      let Asub := fun a b => a + (-b) in
      length dl = r -> width dl c ->
      dmap2 Asub dl dl = (dlzero Azero r c).
  Proof.
    induction dl; simpl; intros; subst; try easy. inv H0.
    rewrite (IHdl (length dl) (length a)); auto.
    unfold dlzero in *. simpl. f_equal; try easy.
    apply map2_sub_self; auto. apply AG.
  Qed.

End dlsub.


(* ==================================== *)
(** ** list dot dlist, and dlist dot dlist *)
Section ldotdl_dldotdl.
  Context `{R:Ring}.
  Add Ring ring_inst : make_ring_theory.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- b" := (Aopp b) : A_scope.
  Notation Asub := (fun a b => a + (-b)).
  Infix "-" := Asub : A_scope.
  
  (* a convenient notation in this section *)
  Notation ldot := (ldot (Aadd:=Aadd) (Azero:=Azero) (Amul:=Amul)).
  
  (** list dot product to dlist *)
  Fixpoint ldotdl (l : list A) (dl : list (list A)) : list A :=
    match dl with
    | h :: t => (ldot l h) :: (ldotdl l t)
    | [] => []
    end.
  
  (** ldotdl left with nil *)
  Lemma ldotdl_nil_l : forall dl r,
      length dl = r -> (ldotdl [] dl = lzero Azero r).
  Proof.
    induction dl; simpl; intros; subst; try easy.
    rewrite ldot_nil_l. rewrite IHdl with (r:=length dl); simpl; auto.
  Qed.
  
  (** ldotdl right with nil *)
  Lemma ldotdl_nil_r : forall r l, (ldotdl l (dnil r) = lzero Azero r).
  Proof.
    induction r; simpl; intros; auto. rewrite IHr. rewrite ldot_nil_r. easy.
  Qed.

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
      (ldotdl (map2 Aadd l1 l2) dl = 
         map2 Aadd (ldotdl l1 dl) (ldotdl l2 dl)).
  Proof.
    induction dl; intros; simpl; auto. inv H1. f_equal.
    - apply ldot_map2_distr_l with (r:=length l1); auto.
    - apply IHdl with (c:=length dl); auto.
  Qed.

  (** ldotdl right distributve over dmap2 *)
  Lemma ldotdl_dmap2_distr_r : forall l dl1 dl2 {c},
      length l = c ->
      width dl1 c -> width dl2 c ->
      (ldotdl l (dmap2 Aadd dl1 dl2) = 
         map2 Aadd (ldotdl l dl1) (ldotdl l dl2)).
  Proof.
    induction dl1,dl2; simpl; intros; auto. inv H0. inv H1.
    f_equal.
    - apply ldot_map2_distr_r with (r:=length a); auto. lia.
    - apply IHdl1 with (c:=length l); auto.
  Qed.
  
  (** ldotdl left with zero *)
  Lemma ldotdl_zero_l : forall dl r c,
      length dl = r -> width dl c ->
      (ldotdl (lzero Azero c) dl = lzero Azero r).
  Proof.
    induction dl; simpl; intros; auto.
    - subst; easy.
    - inv H0. rewrite IHdl with (r:=length dl); auto.
      rewrite ldot_zero_l; easy.
  Qed.
  
  (** ldotdl right with zero *)
  Lemma ldotdl_zero_r : forall l r c,
      length l = c ->
      (ldotdl l (dlzero Azero r c) = lzero Azero r).
  Proof.
    induction r; simpl; intros; auto. unfold dlzero in *. rewrite IHr; auto.
    rewrite ldot_zero_r. easy.
  Qed.
  
  (** ldotdl of consr and consc *)
  Lemma ldotdl_consr_consc : forall l2 dl2 l1 x1 r c,
      length l2 = c -> length dl2 = c -> width dl2 r ->
      (ldotdl (x1 :: l1) (consc l2 dl2) =
         ladd (Aadd:=Aadd) (lcmul (Amul:=Amul) x1 l2) (ldotdl l1 dl2)).
  Proof.
    induction l2, dl2; simpl; intros; auto. inv H1.
    rewrite ldot_cons. f_equal.
    eapply IHl2; auto. apply H5.
  Qed.

  (** ldot and ldotdl could swap first two operands.
    l1 . (l2 . dl) = l2 . (l1 . dl^T) *)
  Lemma ldot_ldotdl_swap12 : forall dl l1 l2 r c,
      length l1 = r -> length l2 = c -> length dl = r -> width dl c ->
      (ldot l1 (ldotdl l2 dl) =
         ldot l2 (ldotdl l1 (dltrans dl c))).
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
      (ldotdl l1 (l2 :: dl2) = (ldot l1 l2) :: (ldotdl l1 dl2)).
  Proof.
    induction l1,l2,dl2; simpl; intros; easy.
  Qed.
  
  (** ldotdl right distributive over ladd.
    (l1 + l2) . dl = l1 . dl + l2.dl *)
  Lemma ldotdl_ladd_distr_r : forall l1 l2 dl r c,
      length l1 = r -> length l2 = r -> length dl = c -> width dl r ->
      (ldotdl (ladd (Aadd:=Aadd) l1 l2) dl = 
         ladd (Aadd:=Aadd) (ldotdl l1 dl) (ldotdl l2 dl)).
  Proof.
    induction dl; simpl; intros; auto. inv H2.
    rewrite <- IHdl with (r:=length l1) (c:=length dl); auto.
    rewrite ldot_ladd_distr_r with (r:=length l1); easy.
  Qed.
  
  (** ldotdl with lcmul is assocociative.
    cmul a (dot l dl) = dot (cmul a l) dl *)
  Lemma ldotdl_lcmul_assoc : forall dl a l r c,
      length l = r -> length dl = c -> width dl r ->
      (lcmul (Amul:=Amul) a (ldotdl l dl) = ldotdl (lcmul (Amul:=Amul) a l) dl).
  Proof.
    induction dl; simpl; intros; auto. inv H1.
    rewrite IHdl with (r:=length l) (c:=length dl); auto.
    rewrite ldot_lcmul_distr_l. easy.
  Qed.
  
  (** a * (x :: l) = (a * x) :: (a * l) *)
  Lemma lcmul_cons : forall a x l,
      (lcmul (Amul:=Amul) a (x :: l) = (Amul a x) :: (lcmul (Amul:=Amul) a l)).
  Proof.
    intros. easy.
  Qed.
  
  (** a * 0 = 0 *)
  Lemma lcmul_zero_r : forall a n,
      lcmul (Amul:=Amul) a (lzero Azero n) = lzero Azero n.
  Proof.
    intros. unfold lcmul. rewrite map_repeat. unfold lzero. f_equal. ring.
  Qed.
  
  (** l dotdl E = l *)
  Lemma ldotdl_dlunit : forall l {n},
      length l = n -> (ldotdl l (dlunit Azero Aone n) = l).
  Proof.
    induction l; simpl; intros; auto.
    - subst. simpl. easy.
    - destruct n. easy. inv H. simpl. f_equal.
      + rewrite ldot_cons. rewrite ldot_zero_r. ring.
      + erewrite (ldotdl_consr_consc);
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
      dldotdl (l1 :: dl1) dl2 = (ldotdl l1 dl2) :: (dldotdl dl1 dl2). 
  Proof.
    simpl. easy.
  Qed.
  
  (** dldotdl consr right *)
  Lemma dldotdl_consr_r : forall dl1 l2 dl2 c,
      length l2 = c ->
      width dl1 c ->
      width dl2 c ->
      dldotdl dl1 (l2 :: dl2) = consc (ldotdl l2 dl1) (dldotdl dl1 dl2).
  Proof.
    induction dl1; simpl; intros; auto. inv H0.
    rewrite ldot_comm.
    rewrite IHdl1 with (c:=length l2); auto.
  Qed.
  
  (** dldotdl left distributve over dmap2 *)
  Lemma dldotdl_dmap2_distr_l : forall dl1 dl2 dl3 {c},
      width dl1 c -> width dl2 c -> width dl3 c -> 
      dldotdl (dmap2 Aadd dl1 dl2) dl3 = 
        dmap2 Aadd (dldotdl dl1 dl3) (dldotdl dl2 dl3).
  Proof.
    induction dl1; destruct dl2; intros; simpl in *; try easy.
    inv H. inv H0. f_equal.
    - apply ldotdl_map2_distr_l with (c:=length dl3); auto.
    - apply IHdl1 with (c:=length a); auto. 
  Qed.
  
  (** dldotdl right distributve over dmap2 *)
  Lemma dldotdl_dmap2_distr_r : forall dl1 dl2 dl3 {c},
      width dl1 c -> width dl2 c -> width dl3 c -> 
      dldotdl dl1 (dmap2 Aadd dl2 dl3) =
        dmap2 Aadd (dldotdl dl1 dl2) (dldotdl dl1 dl3).
  Proof.
    induction dl1; simpl; intros; auto. inv H. f_equal.
    - apply ldotdl_dmap2_distr_r with (c:=length a); auto.
    - apply IHdl1 with (c:=length a); auto.
  Qed.

  (** dldotdl [] dl = dnil *)
  Lemma dldotdl_nil_l : forall dl, dldotdl dl [] = dnil (length dl).
  Proof.
    induction dl; simpl; intros; subst; simpl; subst; try easy.
    f_equal; auto.
  Qed.
  
  (** dldotdl dl [] = dnil *)
  Lemma dldotdl_nil_r : forall dl, dldotdl dl [] = dnil (length dl).
  Proof.
    induction dl; simpl; intros; subst; simpl; subst; try easy.
    f_equal; auto.
  Qed.

  (** dldotdl zero dl = zero *)
  Lemma dldotdl_zero_l : forall r dl c,
      width dl c ->
      dldotdl (dlzero Azero r c) dl = dlzero Azero r (length dl).
  Proof.
    induction r; simpl; intros; simpl; unfold dlzero in *; simpl; try easy.
    rewrite (IHr _ c); auto.
    erewrite (ldotdl_zero_l _); auto.
  Qed.
  
  (** dldotdl dl zero = zero *)
  Lemma dldotdl_zero_r : forall dl c t,
      width dl c ->
      dldotdl dl (dlzero Azero t c) = dlzero Azero (length dl) t.
  Proof.
    induction dl; simpl; intros; auto. inv H.
    unfold dlzero; simpl. f_equal.
    - rewrite dlzero_rw. rewrite ldotdl_zero_r; auto.
    - apply IHdl. auto.
  Qed.
  
  (** dltrans for dldotdl with right decomposition *)
  Lemma dltrans_dldotdl_right : forall d1 d2 l2 r,
      dltrans (dldotdl d1 (l2 :: d2)) (S r) =
        (ldotdl l2 d1) :: (dltrans (dldotdl d1 d2) r).
  Proof.
    unfold width; induction d1; intros; simpl in *. easy.
    specialize (IHd1 d2 l2 r).
    destruct (dltrans (dldotdl d1 (l2 :: d2)) (S r)); try easy. inv IHd1.
    f_equal. f_equal; auto. apply ldot_comm.
  Qed.
  
  (** dldotdl commutation *)
  Lemma dldotdl_comm : forall d1 d2 r c,
      length d1 = r -> width d1 c -> width d2 c ->
      dldotdl d1 d2 = dltrans (dldotdl d2 d1) r.
  Proof.
    induction d1; simpl; intros; subst.
    - rewrite dldotdl_nil_r. rewrite dltrans_nil. easy.
    - inv H0. rewrite dltrans_dldotdl_right.
      f_equal; try easy. apply IHd1 with (c:=length a); auto.
  Qed.
  
  (** l * (d1 . d2)^T = (l . d1^T) . d2 *)
  Lemma ldotdl_dldotdl_dltrans_assoc : forall d1 d2 l {r c},
      width d1 c ->
      length d2 = r -> width d2 c ->
      (ldotdl l (dltrans (dldotdl d1 d2) r) =
         ldotdl (ldotdl l (dltrans d1 c)) d2).
  Proof.
    unfold width. induction d1; intros.
    - subst. simpl. rewrite ?ldotdl_nil_r.
      rewrite ldotdl_zero_l with (r:=length d2); auto.
    - inv H. simpl. destruct l.
      + rewrite ldotdl_nil_l with (r:=length d2).
        2:{ apply consc_length.
            apply ldotdl_length; auto.
            apply dltrans_length. apply dldotdl_width with (c:=length a); auto. }
        rewrite ldotdl_nil_l with (r:=length a).
        2:{ apply consc_length; auto.
            apply dltrans_length; auto. }
        rewrite ldotdl_zero_l with (r:=length d2); auto.
      + erewrite ldotdl_consr_consc with (r:=length d1);
          auto using dltrans_length, dltrans_width.
        2:{ rewrite dltrans_length.
            rewrite ldotdl_length with (r:=length d2); auto.
            apply dldotdl_width with (c:=length a); auto. }
        2:{ apply dltrans_width. apply dldotdl_length; auto.
            apply dldotdl_width with (c:=length a); auto. }
        rewrite ldotdl_consr_consc with (r:=length d1) (c:=length a);
          auto using dltrans_length, dltrans_width.
        erewrite ldotdl_lcmul_assoc with (r:=length a); auto.
        rewrite ldotdl_ladd_distr_r with (r:=length a) (c:=length d2);
          auto using lcmul_length, ldotdl_length, dltrans_length.
        rewrite IHd1 with (c:=length a); auto.
  Qed.

  (** dldotdl association *)
  Lemma dldotdl_assoc : forall d1 d2 d3 r c,
      width d2 c ->
      length d3 = r -> width d3 c ->
      dldotdl (dldotdl d1 (dltrans d2 c)) d3 =
        dldotdl d1 (dltrans (dldotdl d2 d3) r).
  Proof.
    induction d1; simpl; intros; auto.
    f_equal.
    - rewrite ldotdl_dldotdl_dltrans_assoc with (c:=c); auto.
    - apply IHd1; auto.
  Qed.
  
  (** dldotdl left with dlunit *)
  Lemma dldotdl_dlunit_l : forall (dl : list (list A)) {c},
      width dl c -> 
      dldotdl (dlunit Azero Aone c) dl = dltrans dl c.
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
      dldotdl dl (dlunit Azero Aone c) = dl.
  Proof.
    induction dl; simpl; intros; auto. inversion H.
    rewrite IHdl; auto. rewrite ldotdl_dlunit; easy.
  Qed.
  
End ldotdl_dldotdl.


(* ==================================== *)
(** ** Properties of dlcmul *)
Section dlcmul_properties.
  Context `{F:Field}.
  Context `{Dec_Aeq:Decidable A}.
  
  (** Mapping cmul to dlist keep unchanged imply k = 1 or dlist is zero *)
  Lemma dlcmul_fixpoint_imply_k1_or_dlzero : 
    forall {r c} k (dl : list (list A)) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Amul k x)) dl = dl ->
      ((k = Aone) \/ dl = dlzero Azero r c).
  Proof.
    unfold width,dlzero; induction r; intros.
    - rewrite length_zero_iff_nil in H1. subst. right. cbv. easy.
    - simpl. destruct dl. easy. simpl in *. inv H.
      pose proof (lcmul_fixpoint_imply_k1_or_lzero l eq_refl k H3).
      inversion H1. inversion H2.
      specialize (IHr c k dl H5 H8 H4). clear H1 H2.
      destruct IHr, H; auto. right.
      rewrite H3,H4. rewrite H7 in *. rewrite <- H. f_equal.
      rewrite H, H5. auto.
  Qed.
  
  (** Mapping mulc to dlist keep unchanged imply k = 1 or dlist is zero *)
  Lemma dlmulc_fixpoint_imply_k1_or_dlzero : 
    forall {r c} k (dl : list (list A)) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Amul x k)) dl = dl ->
      ((k = Aone) \/ dl = dlzero Azero r c).
  Proof.
    intros. apply dlcmul_fixpoint_imply_k1_or_dlzero; auto.
    rewrite <- H at 2.
    apply map_ext. intros.
    apply map_ext. intros. apply commutative. 
  Qed.

  (** Mapping cmul to dlist got zero imply k = 0 or dlist is zero *)
  Lemma dlcmul_zero_imply_k0_or_dlzero : 
    forall {r c} k (dl : list (list A)) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Amul k x)) dl = (dlzero Azero r c) ->
      ((k = Azero) \/ dl = dlzero Azero r c).
  Proof.
    unfold width, dlzero; induction r; intros.
    - rewrite length_zero_iff_nil in H1. subst. cbv. right. easy.
    - destruct dl. easy. simpl in *.
      inversion H1. inversion H2. inversion H. clear H1 H2 H.
      specialize (IHr c k dl H3 H6).
      rewrite H3, <- H9, H8. subst.
      assert (map (map (fun x : A => Amul k x)) dl =
                repeat (lzero Azero (length l)) (length dl)).
      { rewrite H9. rewrite H8. auto. }
      apply IHr in H.
      (*  {k = 0} + {k <> 0} *)
      destruct (decidable k Azero); auto.
      destruct H; auto. right. f_equal.
      + apply lcmul_eq0_imply_k0_or_lzero in H8; auto.
        destruct H8; auto. easy.
      + rewrite H9. rewrite H at 1. f_equal. rewrite H8. auto.
  Qed.
  
End dlcmul_properties.
