(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector theory of real numbers based on Function
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. Use real numbers to represent components.
  2. it is based on VectorThySig
  
  ref:
  1. 《高等数学学习手册》徐小湛，p173
  2. Vector Calculus - Michael Corral
  3. https://github.com/coq/coq/blob/master/test-suite/success/Nsatz.v
     注意，这里有Coq库中定义的几何学形式化内容，包括点，平行，共线等。
*)

Require Export NatFun.VectorThy.
Require Export FieldStruct.
Require Export ListListExt RExt.

Module VectorThyR := VectorThy FieldR.FieldDefR.
Export VectorThyR.

Open Scope R.


(* ######################################################################### *)
(** * 向量理论在实数域上的扩充 *)
