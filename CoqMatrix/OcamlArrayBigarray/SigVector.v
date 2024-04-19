(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : vector implemented with sig type
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
  1. Motivation:
     如何避开依赖类型的限制（比如 vec (n+m) 和 vec (m+n) 不同），
     同时，如何保持静态检查维度？比如 vec 3 和 vec 4 不能相加。
     若不使用依赖类型，静态检查应该是做不到的。

     (1) 使用非依赖的子类型。参考 SF/vol3_vfa/ADT.v
     Definition vector (A : Type) :=
       {'(n, xs, d) : nat * list A * A | length xs = n}
     特点：list处理rank>=2的张量（例如矩阵）有关的算法时较为复杂，提取元素效率低

     (2) 函数式风格
     Inductive vector (A : Type) :=
       mk_vector (n : nat) (f : nat -> A) (d :A).
     特点：n无法和f产生联系

     (3) 基于有限集的函数式风格
     Inductive vector (A : Type) :=
       mk_vector (n : nat) (ff : fin n -> A) (d : A).
     特点：fin稍嫌繁琐，仍然是依赖类型陷阱

     (4) 基于公理化Array
     Inductive vector (A : Type) :=
       mk_vector (n : nat) (a : array A) (d : A).
     特点：n无法和f产生联系
     
*)

Require Export TupleExt ListExt Hierarchy Sequence.
Require Export RExt RealFunction.
Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt MyExtrOCamlR.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv Ale Alt Altb Aleb a2r.
Generalizable Variable B Badd Bzero.

(** Control the scope *)
Open Scope R_scope.
Open Scope nat_scope.
Open Scope A_scope.
Open Scope vec_scope.

(* ======================================================================= *)
(** ** Definition of vector type [vec] *)

Definition vec (A : Type) :=
  {'(xs, n, d) : list A * nat * A | length xs = n}.

?
Definition vget {A} (v : vec A) (i : nat) : A :=
