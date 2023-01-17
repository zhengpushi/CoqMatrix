(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : learn matrix in MC project
  author    : ZhengPu Shi
  date      : 2022.07.16
*)

(* 首先，引入一些基础库，尤其是 all_algebra 库，包含了 matrix *)
From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import all_fingroup. *)
From mathcomp Require Import all_algebra.
(* From mathcomp Require Import all_solvable. *)
(* From mathcomp Require Import all_field. *)
(* From mathcomp Require Import all_character. *)

(* MC建议的一些flag设定 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* eqType类型，在Type上构造，要求 eqb 与 eq 是反射的，即布尔相等和莱布尼兹相等一致。*)
Section eqType.
  Print eqType.
  Print Equality.type. (* Record type : Type := Pack 
    { sort : Type;  _ : Equality.mixin_of sort } *)
  Print Equality.mixin_of. (* Record mixin_of (T : Type) : Type := Mixin 
    { op : rel T;  _ : Equality.axiom op } *)
  Print Equality.axiom.
  
  (* 几乎所有常见的类型，都已经被装备为 eqType，因为它们几乎都是可判定相等的 *)
(*   Search eqType. *)
  Check nat_eqType : eqType.  (* 自然数 *)
  Check int_eqType : eqType.  (* 整数 *)
  Check rat_eqType : eqType.  (* 有理数 *)
  Check seq_eqType : eqType -> eqType.  (* 列表 *)
  Check interval_eqType : eqType -> eqType. (* 区间 *)
  Check bin_nat_eqType : eqType. (* 二进制自然数 *)
  Check prod_eqType : eqType -> eqType -> eqType.
  Check sum_eqType : eqType -> eqType -> eqType.
  
  (* 具体的项 *)
  
  (* 自然数 *)
  Check 1 : nat_eqType.
  
  (* int，该整数类型与Z不同，是直接对nat进行了扩展，应该很方便递归 *)
  Print int. (* Variant int : Set :=  Posz : nat -> int | Negz : nat -> int *)
  Check Posz 5 : int_eqType.
  
  (* 有理数，与Q不同。直接定义了它的规范：分母不为0，且分子分母互质 *)
  Print rat. (* Record rat : Set := Rat
  { valq : (int * int)%type;
    _ : is_true ((0 < valq.2)%R && coprime `|valq.1| `|valq.2|) } *)

  (* 计算绝对值，比较特别，将 |Negz 0| 计算为 1，而不是 0，与互质的定义有关 *)
  Print absz.
  (* 有理数有关的运算 *)
  Let rat_1_1 := oneq.
  Let rat_0_1 := zeroq.
  Let rat_2_1 := addq oneq oneq.
  Let rat_5_1 := ratz (Posz 5).  (* 由 int 构造 rat *)
  Let rat_4_2 := divq (ratz (Posz 4)) (ratz (Posz 2)). (*
    这一步表示，(4,1) / (2,1) 得到了有理数 (2,1) *)
  Compute rat_4_2.  (* 这个结果有点奇怪，数据是(2,1)，但证明是(4,2)，如何通过类型检查?*)
  
  (* 测试，只要数值正确，后面的证明但凡分母不为0即可 *)
  Check @Rat (@pair int int (Posz 3) (Posz 2))
         (fracq_subproof (@pair int int (Posz 4) (Posz 2)))
     : rat.
  Check @Rat (@pair int int (Posz 3) (Posz 2))
         (fracq_subproof (@pair int int (Posz 12) (Posz 6)))
     : rat.
  Compute normq rat_4_2.  (* 这一步，连证明项都给规约掉了 *)
  
  (* 列表 *)
  Check [::1;2] : seq_eqType nat_eqType.
  
End eqType.


(* choiceType 类型，暂不太理解。它依赖于 eqType *)
Section choiceType.
  Print choiceType.
  Print Choice.type. (* Record type : Type := Pack { 
    sort : Type;  _ : Choice.class_of sort } *)
  Print Choice.class_of. (* Record class_of (T : Type) : Type := Class
    { base : Equality.mixin_of T;  mixin : Choice.mixin_of T } *)
  Print Choice.mixin_of. (* Record mixin_of (T : Type) : Type := Mixin
  { find : pred T -> nat -> option T;
    _ : forall (P : pred T) (n : nat) (x : T), find P n = Some x -> P x;
    _ : forall P : pred T, (exists x : T, P x) -> exists n : nat, find P n;
    _ : forall P Q : pred T, P =1 Q -> find P =1 find Q } *)
  (* 还是尝试理解一下：
    find : (T -> bool) -> nat -> option T, 将谓词和一个自然数关联
    _ : find P n = Some x -> P x，要求find函数若返回Some x，则P x必为true。
    _ : (∃x, P x) -> (∃n, find P n)，要求若某个 P x真，则必有某个n使得find P n为Some
    _ : P = Q -> find P = find Q，要求find函数保持 eqfun 关系（外延相等)
  *)
  Print eqfun.  (* 函数外沿相等 *)
  
  (* 具体类型 *)
  Check nat_choiceType : choiceType.
  Check int_choiceType : choiceType.
  Check bool_choiceType : choiceType.
  Check rat_choiceType : choiceType.
  Check seq_choiceType : choiceType -> choiceType.
  Check prod_choiceType : choiceType -> choiceType -> choiceType.
  Check sum_choiceType : choiceType -> choiceType -> choiceType.
  
  (* 具体的项 *)
  Check 3 : nat_choiceType.
  (* 使用 Typeclass，这些类型非常灵活，上下兼容 *)
  Check (3 : nat_eqType) : nat_choiceType.
  Check (3 : nat_choiceType) : nat_eqType.
  
  (* 再次理解 choiceType，以 nat 为例 *)
  Print nat_choiceType.
  Print nat_choiceMixin.
(*   Let nat_find := [fun P (n : nat) => if P n then Some n else None]. *)
(*   Compute nat_find (fun x => Nat.even x). *)
  (* 手动构造一个 choiceType，大概理解了，是通过选择函数来构造一个子集 *)
  Goal choiceType.
    Print Choice.type.
    refine (@Choice.Pack nat _).
    Print Choice.class_of.
    constructor.
    apply nat_eqMixin.
    Print choiceMixin.
    Print Choice.mixin_of.
    pose ([fun P (n : nat) => if P n then Some n else None]) as find.
    refine (@Choice.Mixin nat find _ _ _); unfold find; clear find; simpl.
    { unfold pred in *. Admitted. 
  
  (* 测试 find 函数，以 nat 为例 *)
  Compute Choice.find nat_choiceMixin (fun n => Nat.even n) 1.
  
End choiceType.


(* countType类型，表示可数类型，依赖于 choiceType *)
Section countType.
  Print countType.
  Print Countable.type. (* Record type : Type := Pack 
    { sort : Type;  _ : Countable.class_of sort } *)
  Print Countable.class_of. (* Record class_of (T : Type) : Type := Class
  { base : Choice.class_of T;  mixin : Countable.mixin_of T } *)
  Print Countable.mixin_of. (* Record mixin_of (T : Type) : Type := Mixin
    { pickle : T -> nat;  
      unpickle : nat -> option T;  
      pickleK : pcancel pickle unpickle } *)
  (* 简单理解：
    pickle 将元素对应到一个序号
    unpickle 将序号对应到元素
    pickleK 表示两个函数互逆
  *)
  Print pcancel.  (* paritial cancle *)
  (* fun rT aT (f : aT -> rT) (g : rT -> option aT) =>
    forall x : aT, g (f x) = Some x *)
  
  (* 按照惯例，基本数据类型都是 countTyp 结构 *)
  Check nat_countType : countType.
  Check int_countType : countType.
  Check bool_countType : countType.
  Check rat_countType : countType.
  Check seq_countType : countType -> countType.
  Check prod_countType : countType -> countType -> countType.
  Check sum_countType : countType -> countType -> countType.
  
  (* 看看 pickle 和 unpickle 函数 *)
  Compute Countable.pickle nat_countMixin 2.
  Compute Countable.pickle bool_countMixin true.
  Compute Countable.pickle bool_countMixin false.
  Compute Countable.pickle int_countMixin 0.
  Compute Countable.pickle int_countMixin 1.
  Compute Countable.pickle int_countMixin 2.
  Compute Countable.pickle int_countMixin (Negz 0).
  Compute Countable.pickle int_countMixin (Negz 1).
  Compute Countable.pickle int_countMixin (Negz 2).
  Compute Countable.pickle int_countMixin (Posz 0).
  Compute Countable.pickle int_countMixin (Posz 1).
  Compute Countable.pickle int_countMixin (Posz 2).
  (* 这些编码是人为构造的 *)
  Compute Countable.unpickle int_countMixin 5.
  Compute Countable.unpickle int_countMixin 48.

End countType.


(* finType 类型，表示有限类型。它依赖于 countType *)
Section finType.
  Print finType.
  Print Finite.type. (* Record type : Type := Pack { 
    sort : Type;  _ : Finite.class_of sort } *)
  Print Finite.class_of.  (* Record class_of (T : Type) : Type := Class {
    base : Choice.class_of T;  mixin : Finite.mixin_of (Equality.Pack base) } *)
  Print Finite.mixin_of. (* Record mixin_of (T : eqType) : Type := Mixin
  { mixin_base : Countable.mixin_of T;
    mixin_enum : seq T;
    _ : Finite.axiom mixin_enum } *)
  Print Finite.axiom. (* fun (T : eqType) (e : seq T) 
    => forall x : T, count_mem x e = 1
     : forall T : eqType, seq T -> Prop *)
  (* 表示，给定类型T，列表e，任意T类型元素x在e中有且只有1个 *)
  Print count_mem.  (* count_mem x := (count (pred1 x)) *)
  Print pred1.      (* 是否等于 a1 的函数类型 *)
  Print simpl_pred. (* 从T -> bool的函数类型 *)
  Print simpl_fun.  (* 将一元函数封装为 Inductive 构造 *)
  Print xpred1.   (* (fun a1 x => eq_op x a1)，一个判断函数 *)
  Print eq_op.    (* 在 eqType 上的bool相等判定函数 *)
  
  (* 整体表示的含义是：给定 可数类型T + 列表e，该列表枚举了所有T类型的元素。
    因为既然能够用列表来罗列，那么就必要是有限吗？？*)
  
  Check bool_finType : finType.
  Check set_finType : finType -> finType.
  Check option_finType : finType -> finType.
  Check finfun_finType : finType -> finType -> finType.
  Check prod_finType : finType -> finType -> finType.
  Check sum_finType : finType -> finType -> finType.
  Check ordinal_finType : nat -> finType. (* 序数集构造 finType *)
  
  (* 以 option_finType 为例 *)
  Compute Finite.mixin_base (option_finMixin bool_finType).
  Compute Finite.mixin_enum (option_finMixin bool_finType).
  
  (* 以 ordinal_finType 为例 *)
  Check (ordinal_finType 3) : finType.

End finType.


(* ordinal 类型，序数集，通过计算来构造，而不是手工构造证明 *)
Section ordinal.
  
  (* 序数集合，所提供的证明特别巧妙，是一个bool函数，而非Prop命题 *)
  Print ordinal. (* Inductive ordinal (n : nat) : predArgType :=  
    Ordinal : forall m : nat, is_true (m < n) -> 'I_n *)
  Compute leq 2 3.  (* 2 <= 3 *)
  
  (* 构造小于n的集合，也就是小于n的所有序数。 *)
  
  (* 补充一点知识：基数cardinal number，序数 ordinal number
   1. 日常生活中，
      数字有两种属性，作为基数的数字和作为序数的数字。
      英语中，有明确的区分。基数：one,two,... 序数:first,second,...
      基数用于描述数量，如1个水果，3头牛。序数代表顺序或位置，如第三天。
   2. 数学中，
      数学家写了一本《基数和序数》的书；从集合论，选择公理，到基数等。
      参考：https://zh.wikipedia.org/zh-hant/序数
      可能用集合的方式定义更加严谨。
  *)
  
  (* 手动构造，非常简单，Coq在做类型检查时使用规约就完成了，不需要手动构造证明 *)
  Compute (@Ordinal 3 0 is_true_true).

End ordinal.


(* finfun_on 类型 *)
Section finfun_on.
  
  Print finfun_on. (* 
  Inductive finfun_on (aT : finType) (rT : aT -> Type) : seq aT -> Type :=
    finfun_nil : finfun_on rT [::]
  | finfun_cons : forall (x : aT) (s : seq aT),
                  rT x -> finfun_on rT s -> finfun_on rT (x :: s) *)
  (* 含义：从aT出发，利用rT得到新类型，然后构造一个列表 *)
  
  (* 构造一些例子 *)
  Compute (@finfun_nil (ordinal_finType 3)).
  
  Let ex1 : Finite.sort (ordinal_finType 3) -> Type.
    simpl. intros X.
    destruct X as [n H].
    destruct n as [|n];[exact nat|].
    destruct n as [|n];[exact bool|].
    exact (prod nat bool).
    Defined.
  Print ex1.
  
  Let ex2 : Finite.sort (ordinal_finType 3) -> Type :=
    fun x => match x with
    | @Ordinal _ 0 _ => unit
    | @Ordinal _ 1 _ => bool
    | @Ordinal _ 2 _ => prod nat bool
    | _ => nat
    end.
  Compute ex2 (@Ordinal _ 0 _).
  Compute ex2 (@Ordinal _ 1 _).
  Compute ex2 (@Ordinal _ 2 _).
  Compute ex2 (@Ordinal _ 3 _).
  
  Let i3_0 := @Ordinal 3 0 is_true_true.
  Let i3_1 := @Ordinal 3 1 is_true_true.
  Let i3_2 := @Ordinal 3 2 is_true_true.
  Compute ex2 i3_0.
  
  Compute (@finfun_nil (ordinal_finType 3)) ex2.
  Compute (@finfun_cons (ordinal_finType 3)) ex2.
  Compute (@finfun_cons (ordinal_finType 3)) ex2 i3_0.
  Compute (@finfun_cons (ordinal_finType 3)) ex2 i3_0 [::].
  Compute (@finfun_cons (ordinal_finType 3)) ex2 i3_0 [::] tt.
  Compute (@finfun_cons (ordinal_finType 3)) ex2 i3_0 [::] tt 
    ((@finfun_nil (ordinal_finType 3)) ex2).
  Compute (@finfun_cons (ordinal_finType 3)) ex2 i3_1 [::] true 
    ((@finfun_nil (ordinal_finType 3)) ex2).
    
  Compute (@finfun_cons (ordinal_finType 3)) ex2 i3_0 [::i3_1].
  Compute (@finfun_cons (ordinal_finType 3)) ex2 i3_0 [::i3_1] tt.
  Compute (@finfun_cons (ordinal_finType 3)) ex2 i3_0 [::i3_1] tt
    ((@finfun_cons (ordinal_finType 3)) ex2 i3_1 [::] true 
      ((@finfun_nil (ordinal_finType 3)) ex2)).

End finfun_on.
  

(* finfun_of 类型 *)
Section finfun_of.

  Print finfun_of. (* Variant
finfun_of (aT : Finite.type) (rT : forall _ : aT, Type)
(ph : phant (forall x : aT, rT x)) : predArgType :=
    FinfunOf : forall _ : finfun_on rT (enum_mem (mem aT)), finfun_of ph *)
  
  Compute (FinfunOf).
  
  Let i3_0 := @Ordinal 3 0 is_true_true.
  Let i3_1 := @Ordinal 3 1 is_true_true.
  
  Let aT := ordinal_finType 3.
  Let rT : Finite.sort aT -> Type :=
    fun x => match x with
    | @Ordinal _ 0 _ => unit
    | @Ordinal _ 1 _ => bool
    | @Ordinal _ 2 _ => prod nat bool
    | _ => nat
    end.
  Compute @FinfunOf aT rT.
  Compute Phant (forall x : Finite.sort aT, rT x).
  
  (* 这两个包装器是为了构造类型 *)
  Print phantom.
  Print phant.
  
  Let phant1 := Phant (forall x : Finite.sort aT, rT x).

  (* mem_pred 是将一个 T->bool 的函数封装为谓词类型 *)
  Print mem_pred.
  Check (Nat.even) : pred nat.
  Check Mem (Nat.even).
  
  (* 将 mem_pred类型 转换为 seq，使用 filter 来构造 *)
  Print enum_mem.
  Let ex3 : mem_pred (ordinal 3) := @Mem (ordinal 3) 
    (fun X : ordinal 3 => match X with
    | @Ordinal _ 0 _ => true
    | @Ordinal _ 1 _ => false
    | @Ordinal _ 2 _ => true
    | _ => false
    end).
  
  Check @enum_mem aT ex3 : seq aT.
  Compute List.hd _ (@enum_mem aT ex3).   (* 无法求值 *)
  Compute List.length (@enum_mem aT ex3).
  
  Goal @finfun_on aT rT (enum (pred_of_simpl (pred_of_argType 
    (Equality.sort (Finite.eqType aT))))).
    simpl. unfold pred_of_simpl.
    unfold pred_of_argType. unfold fun_of_simpl. simpl.
    unfold predPredType.
    unfold enum. simpl.
    unfold PredOfSimpl.coerce.
    unfold mem. unfold simpl_of_mem.
    unfold SimplPred. unfold fun_of_simpl.
    unfold in_mem. unfold pred_of_mem.
(*     refine (finfun_nil _). *)
(*     refine (finfun_cons _ _). *)
    Abort.

End finfun_of.


(* matrix类型 *)
Section matrix.

  Print matrix. (* Variant matrix (R : Type) (m n : nat) : predArgType :=
    Matrix : {ffun 'I_m * 'I_n -> R} -> 'M_(m, n) *)
  (* Variant matrix (R : Type) (m n : nat) : predArgType :=
    Matrix : 
      forall _ : finfun_of (Phant (forall _ : prod (ordinal m) (ordinal n), R)),
             matrix R m n *)
  Print predArgType.  (* = Type *)
  
  Print Phant. (* Variant phant (p : Type) : Prop :=  Phant : phant p *)
  (* 用于将某个类型 p 按照依赖类型包装为 Prop *)
  
  (* 暂时无法手工构造 *)
  Print finfun_of.
  
  (* 测试一些实例 *)
  
  (* 自然数上 *)
  Section nat.
    
    (* 基本矩阵，只有第 (i,j) 的元素是1，其余都是 0 *)
    Check delta_mx (@Ordinal 3 0 is_true_true) (@Ordinal 3 0 is_true_true).
  
    (* 看看能否得到更简洁的形式，比如直接 求值 *)
    Section test.
      Let m1 := @delta_mx int_Ring _ _ (@Ordinal 3 0 is_true_true) 
        (@Ordinal 3 0 is_true_true).
(*       Compute m1 (@Ordinal 3 0 is_true_true) (@Ordinal 3 0 is_true_true). *)
      Variable x : nat.
      Let m2 := @const_mx nat 2 3 1.
      Let x00 := m2 (@Ordinal 2 0 is_true_true) (@Ordinal 3 0 is_true_true).
      Eval simpl in x00.
(*       Compute x00. *)
      
    End test.
    
    (* 常数矩阵 *)
    Example m_34 := @const_mx nat 3 4 1.
    
    (* 取出元素 *)
    Print const_mx_key. (* 因其被声明为 Opaque，导致无法计算，
      咱不知道这个设计意图，也许需要修改源码重新编译来尝试 *) 
    Check m_34 (@Ordinal _ 0 _) (@Ordinal _ 0 _).
    
    (* 矩阵形状改变 *)
    Example shape_cond : (3 = (1+2)) * (4 = 2*2).
      split; auto. Qed.
    Check castmx shape_cond m_34.
   
    (* 转置 *)
    Print trmx_key.
    Print trmx.
    Print matrix_of_fun.  (* 新的矩阵构造方式 *)
    
    (* 再次尝试手动构造矩阵，终于成功 *)
    Check @matrix_of_fun nat 2 3 tt.
    Example gen1 : (ordinal_finType 2 -> ordinal_finType 3 -> nat) :=
      fun i j => match i,j with
      | @Ordinal _ 0 _, @Ordinal _ 0 _ => 0
      | _, _ => 1
      end.
    Check matrix_of_fun tt gen1.
    
    (* 置换矩阵的行 *)
    Check row_perm _ m_34.
    
    (* 构造置换条件 *)
    Check @perm.perm_of (ordinal_finType 3) (Phant 'I_3).
(*     Search (@perm.perm_of (ordinal_finType _)). *)
    Check perm.perm_one.
    Check lift0_perm.
    
    (* 置换矩阵的列 *)
    Check col_perm _ m_34.
    
    (* 交换行、列 *)
    Check xrow (@Ordinal 3 0 is_true_true) (@Ordinal 3 2 is_true_true) m_34.
    Check xcol (@Ordinal 4 0 is_true_true) (@Ordinal 4 1 is_true_true) m_34.
    
    (* 取出一行、一列 *)
    Check row (@Ordinal 3 0 is_true_true) m_34.
    Check col (@Ordinal 4 0 is_true_true) m_34.
    
    (* 删除一行、一列 *)
    Check row' (@Ordinal 3 0 is_true_true) m_34.
    Check col' (@Ordinal 4 0 is_true_true) m_34.
    
    (* 重新索引一个矩阵，例如把 3x4改变为2x6，尚未测试 *)
    Check mxsub.
    
    (* 连接两个矩阵，行、列两个方向 *)
    Check row_mx m_34 m_34.
    Check col_mx m_34 m_34.
    
    (* 矩阵的左、右、上、下方位的子矩阵 *)
    Example shape_cond2 : (3 = (1+2)) * (4 = 2 + 2).
      split; auto. Qed.
    Example m_34' := castmx shape_cond2 m_34. (* 构造出这种维数为加法形式的矩阵 *)
    Check lsubmx m_34'. (* 左侧 *)
    Check rsubmx m_34'. (* 右侧 *)
    Check usubmx m_34'. (* 上侧 *)
    Check dsubmx m_34'. (* 下侧 *)
    (* 这些实现都只是处理上下标即可。但MC类型系统复杂，需要非常熟悉这些构造。*)
    
    (* 从四个矩阵来构造一个分块矩阵：左上、右上、左下、右下 *)
    (* 例如，m_2x3, m_2x4, m_3x3, m_3x4 *)
    Variable m1 : matrix nat 2 3.
    Variable m2 : matrix nat 2 4.
    Variable m3 : matrix nat 3 3.
    Variable m4 : matrix nat 3 4.
    Definition m5 := block_mx m1 m2 m3 m4.
    Check m5.
    
    (* 拆分矩阵，一个 M_(m1+m2)_(n1+n2) 形式的矩阵，分别取出四个角 *)
    Check ulsubmx m5.
    Check ursubmx m5.
    Check dlsubmx m5.
    Check drsubmx m5.
    
    (* 分块矩阵的转置有关的性质 *)
    Goal trmx (block_mx m1 m2 m3 m4) = block_mx m1^T m3^T m2^T m4^T.
    apply tr_block_mx. Qed.
    
    (* 分块矩阵的结合律。总共9个子矩阵，以 4 2 2 1 或 2 4 1 2 来结合 *)
    
    (* 将矩阵 'M(m,n) 和 向量 'rV(m*n) 互转的函数 *)
    Check mxvec m1.
    Check vec_mx (mxvec m1).
    
    (* 矩阵映射 *)
    Check map_mx S m1.
    
    (*********************************************
      很有特色的一点是，除了上面的常规性质，下面开始在数学结构上定义性质，
      包括 Zmodule, ring, ...  *)
    
    (* 先来了解 zmodType 和 ringType *)
    Section zmodType_ringType.
      
      (* 具体的结构 *)
      Check int_ZmodType : zmodType.
      Check rat_ZmodType : zmodType.
      Check pair_zmodType.
      
(*       Search ringType. *)
      Check int_Ring : ringType.
      Check rat_Ring : ringType.
      Check poly_ringType : ringType -> ringType. (* 多项式环 *)
      Check pair_ringType.
      
      (* 具体的元素 *)
      Check 1 : int_ZmodType.
      Check oneq : rat_ZmodType.
      Check (Posz 1, Posz 2) : pair_ringType int_Ring int_Ring.
      Check 1 : int_Ring.
      
      (* 看看多项式 *)
      Print poly_ringType.
      Print poly_zmodType.
      Print poly. (* : forall R : ringType, nat -> (nat -> R) -> {poly R} *)
        (* 可能每个位置上的系数，用 nat -> R 来表示 *)
      
    End zmodType_ringType.
    
    (* 在 Zmodule (additive) 结构上，就有了矩阵加法、减法等，
      相应的，对元素的要求也更高，需要构造 *)
    Example m10 := @const_mx (int_Ring) 3 4 (Posz 1).
    Example m11 := @const_mx (int_Ring) 3 4 (Posz 2).
    Check addmx m10 m11.
    Check oppmx m10.
    (* 在 Zmodule 上，有交换律、结合律、左加零、右加零等性质 *)
    
    (* 在 ring 上有了数乘等运算 *)
    Check scalemx 1 m10.
    
    (* ************************ linear，线性空间？？ *)
    Check swizzle_mx_scalable.
    
    (* 对角矩阵，需要一个向量来构造 *)
    Check diag_mx (mxvec m10).  (* 暂不知如何构造向量，先用 mxvec 凑合 *)
    (* 在MC中，向量就是矩阵 *)
    
    (* 用常数来构造矩阵 *)
    Check @scalar_mx int_Ring 3 1.  (* 对角线全是1的对角矩阵 *)
    
    (* 矩阵乘法 *)
    Open Scope ring_scope.
    Check mulmx m10 (trmx m10).
    Check m10 *m (m10^T).
    
    (* partial identity matrix: 部分单位阵，在对角线上且小于第i行时为1 *)
    Check pid_mx 3. (* 仅 0_0, 1_1, 2_2 是1 *)
    
    (* 将向量的线性函数转换为矩阵 *)
    Check lin1_mx.
    (* 将矩阵到矩阵之间的线性函数转换为更高阶的矩阵 *)
    Check lin_mx.
    
    (* 矩阵的迹 *)
    Example m20 := @const_mx (int_Ring) 3 3 (Posz 1). (* 3x3的方阵 *)
    Check mxtrace m20.
    
    (*********************** 最精彩的部分，构造方阵上的 ring structure *)
    Check matrix_ringType int_Ring 3. (* 3x3整数矩阵 *)
    
    (*************** 以下又是一些不太熟悉的内容 *)
    
    (*
      Cormen LUP 上三角分解
      list0_perm 置换？？
    *)
    
    (* 行列式 *)
    Check determinant m20.
    
    (* 第(i,j)个余子式 *)
    Check cofactor m20 (@Ordinal 3 0 _) (@Ordinal 3 0 _).
    
    (* adjugate 共轭伴随矩阵 *)
    Check adjugate m20. (* 每个元素都是一个代数余子式计算后的值 *)
    
    (* 矩阵乘法是否可交换，Prop版本，bool版本 *)
    Check comm_mx m20 m20.
    Check comm_mxb m20 m20.
    
    (* 是否为单位阵？ *)
    Check unitmx m20.
    
    (* 逆矩阵，利用行列式、伴随矩阵来表示 *)
    Check invmx m20.
    
    (* 逆矩阵、行列式、乘法的一系列性质 *)
    Check invmxK m20.
    Check mulVmx.
    
    (* Finite inversible matrices and the general linear group,
     有限可逆矩阵，一般线性群 *)
    Check GLtype.
    
    (*************** Matrix over a domain *)
    
    (* 在 Field 上的矩阵，有更多的运算和性质 *)
    
    (** LUP分解：给定矩阵A，分解为 P A = L U，其中 P 是置换矩阵，L和U分别是下、上三角 *)
    Check cormen_lup.
    
    (* 还有一堆的性质，略。 *)
    
    (* 总结起来，已经实现的功能有：
    ??
    问题也有：
    不能直观的得到运算结果，甚至取不到元素值。也许数学性质很好。
    *)
  End nat.
  
End matrix.

