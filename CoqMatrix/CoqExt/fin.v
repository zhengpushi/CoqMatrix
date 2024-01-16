(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Fin in Coq Standard Library
  author    : ZhengPu Shi
  date      : 2023.09
 *)

Require Import Fin.

(** * Motivation examples *)

(* fin 可以有多种实现，经过简单对比，暂时选用标准库的做法 *)
Module fin.
  
  (* 第一种方式，来自于标准库 *)
  Module fin1.
    Inductive t : nat -> Set :=
    | F1 : forall n : nat, t (S n)
    | FS : forall n : nat, t n -> t (S n).

    (* 空集 *)
    Compute t 0.
    (* 1个元素 *)
    Compute t 1.
    Compute F1 0 : t 1.
    (* 2个元素 *)
    Compute t 2.
    Compute F1 1 : t 2.
    Compute FS 1 (F1 0) : t 2.
    (* 3个元素 *)
    Compute t 3.
    Compute F1 2 : t 3.
    Compute FS 2 (F1 1) : t 3.
    Compute FS 2 (FS 1 (F1 0)) : t 3.
  End fin1.

  (* 第一种方式，修改了的定义。区别是没有空集 *)
  Module fin2.
    Inductive t : nat -> Set :=
    | F1 : forall n : nat, t n
    | FS : forall n : nat, t n -> t (S n).

    (* 没有空集 *)
    (* 1个元素 *)
    Compute t 0.
    Compute F1 0 : t 0.
    (* 2个元素 *)
    Compute t 1.
    Compute F1 1 : t 1.
    Compute FS 0 (F1 0) : t 1.
    (* 3个元素 *)
    Compute t 2.
    Compute F1 2 : t 2.
    Compute FS 1 (F1 1) : t 2.
    Compute FS 1 (FS 0 (F1 0)) : t 2.
  End fin2.

  (* 可以在两个集合之间转换 *)

  (* 从 fin2 转换到 fin1 *)
  Fixpoint fin2_to_fin1 (n : nat) (f : fin2.t n) : fin1.t (S n) :=
    match f with
    | fin2.F1 _ => fin1.F1 _
    | fin2.FS n' f' => fin1.FS _ (fin2_to_fin1 n' f')
    end.
  Compute fin2_to_fin1 _ (fin2.F1 2).

  (* 从 fin1 转换到 fin2，有个空集问题 *)
  (* Fixpoint fin1_to_fin2 (n : nat) (f : fin1.t (S n)) : option (fin2.t n) := *)
  (*   match n with *)
  (*   | O => None *)
  (*   | S n' => *)
  (*       match f with *)
  (*       | fin1.F1 _ => Some (fin2.F1 _) *)
  (*       | fin1.FS _ f' => *)
  (*           match fin1_to_fin2 _ (fin1.FS _ f') with *)
  (*           | None => Some (fin2.F1 _) *)
  (*           | Some f' => Some (fin2.FS _ f') *)
  (*           end *)
  (*       end *)
  (*   end. *)

End fin.



Notation fin := Fin.t.

(** ** 先学习 Fin *)
Section learn_fin.

  (* --------- 有限的情形(少量数据) --------- *)
  
  (* 交互式的构造 *)
  Let ex1 : fin 2 -> nat.
    intro f. destruct f.
    exact 1. exact 2.
  Defined.
  (* Print ex1. *)
  (* Compute ex1. *)

  (* 直接写出构造过程 *)
  Let ex1' : fin 2 -> nat :=
        fun f =>
          match f with
          | F1 => 1
          | FS _ => 2
          end.
  (* Compute ex2. *)

  (* --------- 有限的情形(大量数据) --------- *)
  
  (* 交互式的构造 *)
  Let ex2 : fin 4 -> nat.
    intro f. destruct f.
    exact 1. destruct f. exact 2. destruct f. exact 3. exact 4.
  Defined.
  (* Compute ex2. *)

  (* 直接写出构造过程 *)
  Let ex2' : fin 4 -> nat :=
        fun f =>
          match f with
          | F1 => 1
          | FS F1 => 2
          | FS (FS F1) => 3
          | FS (FS (FS F1)) => 4
          | FS _ => 5
          end.
  (* Compute ex2'. *)

  (* --------- 向量的map --------- *)

  (* 看起来在给定向量上操作是很简单的 *)
  Let vmap (n : nat) (v1 v2 : fin n -> nat) : fin n -> nat :=
        fun f => v1 f + v2 f.

  (* Compute ex2. *)
  (* Compute (vmap 4 ex2 ex2) F1. *)

  (* 困难的可能是动态的构造一个向量(主要是 fin 的处理，例如 fin <-> nat) *)
End learn_fin.

(** ** Converting between fin and nat *)

(** Convert fin to nat. *)
Fixpoint fin2nat (n : nat) (f : fin n) : nat :=
  match f with
  | F1 => O
  | FS f' => S (fin2nat _ f')
  end.
Compute fin2nat _ F1.
Compute fin2nat _ (FS F1).

(* 将 Fin.t (S n) 转换为 Fin.t n。即：第一个索引返回None，后来的依次左移 *)
Definition convert_fin {n : nat} (f : Fin.t (S n)) : option (Fin.t n) :=
  match f with
  | Fin.F1 => None (* 0 不能转换为 Fin.t n *)
  | Fin.FS f' => Some f'
  end.
Compute @convert_fin 5 (FS F1).

Fixpoint count_elements {n : nat} (f : Fin.t n) : nat :=
  match f with
  | Fin.F1 => 1
  | Fin.FS f' => 1 + count_elements f'
  end.

Fixpoint reverse_elements {n : nat} (f : Fin.t n) : Fin.t n :=
  match f with
  | Fin.F1 => Fin.F1
  | Fin.FS f' => let reversed_tail := reverse_elements f' in
                 match reversed_tail in Fin.t m' return Fin.t (S m') with
                 | Fin.F1 => Fin.FS Fin.F1
                 | Fin.FS x => Fin.FS (Fin.FS x)
                 end
  end.

Compute @Fin.of_nat_lt 1 3.
(* 我暂时写不出 fin 的后继函数 (以及增加多步后的索引)，也许要查查Coq标准库，
   虽然这个库很难写，但也许这就是它的优势所在。 *)
?
Require Import Coq.Arith.PeanoNat.
Fixpoint increment_index_with_offset {n : nat} (f : Fin.t n) (offset : nat) : Fin.t n :=
  match f with
  | Fin.F1 => Fin.FS Fin.F1
  | Fin.FS f' => match increment_index_with_offset f' offset in Fin.t m return Fin.t (S m) with
                 | Fin.F1 => Fin.FS (Fin.of_nat_lt (Nat.lt_succ_diag_r offset))
                 | Fin.FS x => Fin.FS x
                 end
  end.
Fixpoint increment_index {n : nat} (f : Fin.t n) (offset : nat) : Fin.t n :=
  match f with
  | Fin.F1 => Fin.FS Fin.F1
  | Fin.FS f' => Fin.FS (increment_index_with_offset f' offset)
  end.

Fixpoint increment_index {n : nat} (f : Fin.t n) : Fin.t n :=
  match f with
  | Fin.F1 => Fin.FS Fin.F1
  | Fin.FS f' => Fin.FS (increment_index f')
  end.
Fixpoint reverse_elements {n : nat} (f : Fin.t n) : Fin.t n :=
  match f in Fin.t m return Fin.t m with
  | Fin.F1 => Fin.F1
  | Fin.FS f' => let reversed_tail := reverse_elements f' in
                 match reversed_tail in Fin.t m' return Fin.t (S m') with
                 | Fin.F1 => Fin.FS Fin.F1
                 | Fin.FS x => Fin.FS (Fin.FS x)
                 end
  end.

Fixpoint next_index {n : nat} (f : Fin.t n) : option (Fin.t n) :=
  match f in Fin.t m return (option (Fin.t m)) with
  | Fin.F1 => None
  | Fin.FS _ => Some (Fin.FS Fin.F1)
  end.
Definition next_index {n : nat} (f : Fin.t n) : option (Fin.t n) :=
  match f in Fin.t m return (option (Fin.t m)) with
  | Fin.F1 => None
  | Fin.FS _ => Some (Fin.FS Fin.F1)
  end.
Definition next_index {n : nat} (f : Fin.t n) : option (Fin.t n) :=
  match f in Fin.t m return (option (Fin.t m)) with
  | Fin.F1 => Some (Fin.FS Fin.F1)
  | Fin.FS _ => Some (Fin.FS Fin.F1)
  end.
Definition next_index {n : nat} (f : Fin.t n) : option (Fin.t n) :=
  match n with
  | 0 => None
  | S _ =>
    match f with
    | Fin.F1 => Some (Fin.FS Fin.F1)
    | Fin.FS _ => Some (Fin.FS Fin.F1)
    end
  end.
Definition next_index {n : nat} (f : Fin.t n) : option (Fin.t n) :=
  match n with
  | 0 => None
  | S n' =>
    match f in (Fin.t (S n')) return option (Fin.t (S n')) with
    (* match f as f' in (Fin.t (S n')) return option (Fin.t (S n')) with *)
    | Fin.F1 => Some (Fin.F1)
    | Fin.FS f' => Some (Fin.FS f')
    end
  end.

Definition next_index {n : nat} (f : Fin.t n) : Fin.t n :=
  match f with
  | Fin.F1 => Fin.FS Fin.F1
  | Fin.FS _ => Fin.FS Fin.F1
  end.
Definition next_index {n : nat} (f : Fin.t n) : Fin.t n :=
  match f with
  | Fin.F1 => Fin.FS Fin.F1
  | Fin.FS f' => Fin.FS f'
  end.

Definition next_index {n : nat} (f : Fin.t n) : Fin.t n :=
  match f with
  | Fin.FS _ => Fin.F1
  | Fin.F1 => Fin.FS Fin.F1
  end.
Definition next_index {n : nat} (f : Fin.t n) : Fin.t n :=
  match f with
  | Fin.FS _ => f
  | Fin.F1 => Fin.FS Fin.F1
  end.
Definition next_index {n : nat} (f : Fin.t n) : Fin.t n :=
  match f with
  (* 如果 f 是最后一个索引（Fin.FS Fin.F1），则返回第一个索引（Fin.F1） *)
  | Fin.FS Fin.F1 => Fin.F1
  (* 其他情况下，返回 f 的后继 *)
  | Fin.FS f' => Fin.FS f'
  end.

Definition convert_fin {n : nat} (f : Fin.t (S n)) : Fin.t n :=
  match f in (Fin.t (S n)) with
  | Fin.F1 => Fin.F1
  | Fin.FS f' => Fin.FS_inj f'
  end.
Definition example_fin : Fin.t 4 := Fin.FS (Fin.FS (Fin.FS Fin.F1)).
Compute convert_fin example_fin.
Check Fin.FS_inj.

(** Convert nat to fin. *)
Fixpoint nat2fin (n : nat) (i : nat) : option (fin n) :=
  match n with
  | O => None
  | S n' =>
      match i with
      | O => Some F1
      | S i' =>
          let o := nat2fin n' i' in
          match o with
          | None => None
          | Some x => Some (FS x)
          end
      end
  end.
Compute nat2fin 0 0.
Compute nat2fin 1 0.
Compute nat2fin 2 0.
Compute nat2fin 2 1.
Compute nat2fin 2 2.

(* 无option的版本，做了如下改动：
   1. 生成的是 fin (S n) ，而不是 fin n。所以 nat2fin (S n) 等价于 nat2fin' n。
   2. 如果 n 为 0 时，i 应当必须是 0，而当 i 不是 0 时，这里也没有报错
*)
Fixpoint nat2fin' (n : nat) (i : nat) : fin (S n) :=
  match n, i with
  | O, O => F1
  | O, _ => F1                   (* 这是错误。因为要求 i <= n，而上面已经有了 *)
  | S n', O => F1
  | S n', S i' => FS (nat2fin' n' i')
  end.
Compute nat2fin' 0 0.
Compute nat2fin' 1 0.
Compute nat2fin' 1 1.

(* Convert type from "fin n" to "fin (S n)" *)
Fixpoint fin2finS {n:nat} (i : fin n) : fin (S n):=
  match i with
  | F1 => F1
  | FS i' => FS (fin2finS i')
  end.

Compute @fin2finS 3 (F1).
Compute @fin2finS 3 (FS F1).

(* Convert type from "fin (S n)" to "fin n" *)

Variable fi : fin 3.

Check @F1 2.
Check @FS 2 (@F1 1).
Check @FS 2 (@FS 1 (@F1 0)).

Check @F1 1.
Check @FS 1 (@F1 0).

(* Fixpoint finS2fin {n} : fin (S n) -> option (fin n) := *)
(*   match n with *)
(*   | S n' => *)
(*       fun (i : fin (S (S n'))) => *)
(*         match i with *)
(*         (* | @FS n' fi' => Some (@FS n' (finS2fin fi')) *) *)
(*         | _ => None *)
(*         end *)
(*   | O => fun _ => None *)
(*   end. *)
(*   match fi with *)
(*   | @F1 2 => @F1 1 *)
(*   | @FS 2 fi' => @FS 1 (finS2fin fi') *)
(*   (* | @FS 2 (@FS 1 (@F1 0)) => @F1 1 *) *)
(*   | @F1 k => F1 *)
(*   end. *)

(* Fixpoint finS2fin (fi:fin 3): fin 2 := *)
(*   match fi with *)
(*   | @F1 2 => @F1 1 *)
(*   | @FS 2 fi' => @FS 1 (finS2fin fi') *)
(*   (* | @FS 2 (@FS 1 (@F1 0)) => @F1 1 *) *)
(*   | _ => @F1 1 *)
(*   end. *)

(* Fixpoint finS2fin {n:nat} : fin (S n) -> option (fin n) := *)
(*   match n with *)
(*   | O => fun _ => None *)
(*   | S n' => *)
(*       fun (i : fin (S (S n'))) => *)
(*         match i return option (fin (S n')) with *)
(*         | F1 => Some F1 *)
(*         | FS i' => *)
(*             let i'' := finS2fin (fin2finS i') in *)
(*             Some F1 *)
(*         end *)
(*   end. *)


(* 计算 fin (S n) 集合中的最大值 *)
Fixpoint fin_max (n : nat) : fin (S n) :=
  match n with
  | O => @F1 0
  | S n' => FS (fin_max n')
  end.
Compute fin_max 0.              (* @F1 0 *)
Compute fin_max 1.              (* @FS 1 (@F1 0) *)
Compute fin_max 2.              (* @FS 2 (@FS 1 (@F1 0) *)

(* 计算 fin n 的某个给定元素的后一个 *)
(* Fixpoint fin_next (n : nat) (f : fin n) : option (fin n) := *)
(*   match n, f with *)
(*   | O, _ => None *)
(*   | 1, @F1 0 => None *)
(*   | 2, @F1 1 => Some (@FS 1 (@F1 0)) *)
(*   | 2, @FS 1 f' => *)
(*   end. *)

(* 计算 fin n 的某个给定元素的前一个 *)
(* Fixpoint fin_next (n : nat) (f : fin n) : option (fin n) := *)
(*   match f with *)
(*   | F1 => None *)
(*   | FS f' => f' *)
(*   end. *)
    

(** 计算 fin n 的所有元素？由于是依赖类型，所以与 nat 有很大的不同 *)

(* 计算 < n 的所有元素 *)
Fixpoint all_nat (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => n' :: (all_nat n')
  end.
Compute all_nat 3.

(* 计算在 fin n 内的所有元素 *)

(* 第1次尝试。因使用了 nat2fun, seq, map, concat，可能太繁琐了 *)
Definition all_fin' (n : nat) : list (fin n) :=
  concat (map (fun i => match nat2fin n i with
         | None => []
         | Some fi => [fi]
         end) (seq 0 n)).
Compute all_fin' 3.

(* 第2次尝试。*)
Fixpoint all_fin (n : nat) : list (fin n) :=
  match n with
  | O => []
  | S n' => F1 :: (map FS (all_fin n'))
  end.
Compute all_fin 0.
Compute all_fin 1.
Compute all_fin 2.

(* 判断 fin n 的两个元素布尔相等 *)

Set Printing Implicit.
Compute FS F1 : fin 4.
Compute FS (FS F1) : fin 4.
Fixpoint eqb {m} : t m -> t m -> bool :=
  match m with
  | O => fun _ _ => true
  | S m' =>
      fun (i:t (S m')) (j:t (S m')) =>
        match i, j with
        (* | @F1 a, @F1 b => Nat.eqb a b *)
        | @FS m'' i', @FS _ j' => @eqb _ i' j'
        | _, _ => false
        end
  end.

  match p, q with
  | @F1 m', @F1 n' => Nat.eqb m' n'
  | FS _, F1 => false
  | F1, FS _ => false
  | FS p', FS q' => eqb p' q'
  end.

Fixpoint eqb {m n} (p : t m) (q : t n) :=
  match p, q with
  | @F1 m', @F1 n' => Nat.eqb m' n'
  | FS _, F1 => false
  | F1, FS _ => false
  | FS p', FS q' => eqb p' q'
  end.

Fixpoint eqb {n:nat} : fin n -> fin n -> bool :=
  match n with
  | O => fun i j => true
  | S n' =>
      fun (f:fin (S n')) (g:fin (S n')) =>
        match f, g with
        | F1, F1 => true
        | FS f', FS g' =>
            let f'' : fin n' := f' in
            let g'' : fin n' := g' in
            eqb f'' g''
        | _, _ => false
        end
  end
    
.

Fixpoint mk_vec {m:nat} : (fin m -> A) -> vector m:=
  match m with
  | 0 => fun ( _:_ ) => tt :vector 0
  | S m' => fun ( u: fin (S m') -> A) =>
      (mk_vec (fun i => u (fin2finS i)), (* 构造前m'个元素 *)
       u (exist _ m' (Nat.lt_succ_diag_r m'))) (* 构造最后一个元素 *)
  end.

      
  fun f g => 
Print eqb.

(** ** Matrix  *)
Section Matrix.
  Variable A : Type.

  Let mat (r c:nat) := fin r -> fin c -> A.
  Let smat n := mat n n.
  Let vec (n:nat) := fin n -> A.

  Section convert_between_matrix_and_vector.
    Variable m2 : mat 2 3.
    Check m2 F1 : vec 3.
  End convert_between_matrix_and_vector.
End Matrix.


(** ** Auxiliary functions of list  *)

(** nth of a list (fin version) *)
Fixpoint ith {A : Type} {n : nat} (fi : fin n) (l : list A) (default : A) : A :=
  match l with
  | [] => default
  | hl :: tl => 
      match fi with
      | F1 => hl
      | FS fi' => ith fi' tl default
      end
  end.

(** list to vector *)
Definition l2v {A:Type} {n} (l:list A) (default : A) : fin n -> A :=
  fun fi => ith fi l default.

(** vector to list *)
Fixpoint v2l {A:Type} {n} (v : fin n -> A) : list A :=
  map v (all_fin n).

Section test.
  Let v1 (f: fin 2) : nat :=
        match f with
        | F1 => 1
        | FS _ => 2
        end.
  Compute v2l v1.
End test.

(* 取出头部的某个元素 *)
Section vhd.
  Context {A:Type} {n:nat}.
  Definition vhd1 (v : fin (S n) -> A) := v F1.
  Definition vhd2 (v : fin (S (S n)) -> A) := v (FS F1).
  Definition vhd3 (v : fin (S (S (S n))) -> A) := v (FS (FS F1)).
  Definition vhd4 (v : fin (S (S (S (S n)))) -> A) := v (FS (FS (FS F1))).
End vhd.
