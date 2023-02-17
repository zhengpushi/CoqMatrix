(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Block Matrix
  author    : ZhengPu Shi
  date      : 2022.06
  
  ref       :
  1. https://zhuanlan.zhihu.com/p/133330692
  
  remark    :
  1. 分块相加要能进行，则每一块的形状相同。
  2. 分块相乘要能进行，则第一个矩阵的列划分要与第二个矩阵的行划分匹配。
    例如：
              1 2 | 3     1 | 2
              4 5 | 6     3 | 4
      A * B = - - - -  *  - - -
              7 8 | 9     5 | 6
    记为
        A11 A12    B11 B12
        A21 A22  * B21 B22
    其中，
      A的列划分是：2,1
      B的行划分是：2,1 
  3. 所以，想到了分块矩阵乘法的一些关键步骤
    a. partion, 对A矩阵的列划分，以及对B矩阵的行划分
    b. assign, 对划分好的每个小矩阵，起一个名字，要能管理好自己的形状和数据
    c. multiply，使用矩阵乘法公式，对每个矩阵做乘法
    d. combine，将执行结果合并起来得到最后的结果
      这一步，可以预测到新矩阵对每个结果的位置管理，然后直接copy。
    这个工作最重要的一步，就是考虑 cpu对数组和指针的抽象，以及将来GPU的模型，
    这样的话，验证完的算法才有可能落地。
  4. 为什么要做矩阵分块？
    a. 有时候矩阵分块是非常自然的选择，合理分块可以简化计算。例如
                  1 2
                  3 4
    1 0 1 0 1 0   0 0               A         1 2
    0 1 0 1 0 1 x 0 0   = [I I I] x 0 = IxA = 3 4
                  0 0               0
                  0 0
    b. 分块表达可以递归或循环的解决问题，适合数值解法。
    3. 在 Csdp 中的用途
      这里是 Csdp 使用了分块矩阵的例子
      https://github.com/coin-or/Csdp/blob/master/example/example.c
      Csdp是Coq使用Zify作为求解器的后端，在Micromega库的介绍中看到的
      https://coq.inria.fr/distrib/V8.13.2/refman/addendum/micromega.html
*)

Require Import FieldStruct.

Require Import Function.MatrixThy.

Require Import ListListExt.
Require Import Lia.

Require Import Setoid.  (* ==> *)

Open Scope R.

(* ######################################################################### *)
(** * Block Matrix theory *)
Module BMatrixThy (E : FieldSig).
  
  (* ======================================================================= *)
  (** ** Matrix theory *)
  Module MatrixThy := MatrixThy E.
  Export MatrixThy.

  
End BMatrixThy.
