(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix with abstract function (similiar with PArray, but different)
  author    : ZhengPu Shi
  date      : 2023.04
  remark    :
  1. 基于函数的矩阵模型效率较低，能否有一些改进？
     比如，PArray是基于OCaml的Array模块，
     而OCaml还有 Bigarray 模块，提供了多维数组的实现。
     另外，C语言中的数组的实现思想也可以考虑。
  2. 结构化的矩阵实现（基于list，tuple等），在处理矩阵转置/乘法时都不太方便，需要较
     复杂的结构和算法。后续还有更复杂的矩阵理论，也许这种结构过于复杂。
  3. 目前，对于符号矩阵的行列式等复杂运算，在两种理论下均可行。
     而高斯消元法的最佳应用场景是矩阵元素为具体数字，因此一定要抽取出OCaml代码。
  4. 总体来讲，如何设计一种数据结构，能够同时考虑到效率和验证时的高的表达能力？
     使得：
     (1). 方便形式验证（可以使用一定的公理化实现），即，验证矩阵算法的正确性？
     (2). 适用与控制系统中的高效数值计算？
     主要难点：
     (1). 表达矩阵类型中的维度，以便在验证时自动实现类型推到，保持一定的类型安全。
     (2). 具有一定的元素多态的能力（有理数域，实数域，复数域，实函数域等）
          不过，在实际的程序中，只有整数和浮点数之分（有理数和实数都用浮点数来近似，
          所以，没有区别；复数用一个对偶来实现；实函数估计不会用于计算？？）
     
 *)


Section def.

Context {A:Type}.

Parameter mat : nat -> nat -> Type.

(* Record mat (r c : nat) := { *)
(*     mat_data : nat -> nat  *)
  
