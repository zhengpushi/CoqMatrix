(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

	2022/06/23 12:15
	用法
	#use "seq.ml";;
	#use "seq_test.ml";;
*)

(* 奇数序列：1,3,5,... *)
let f1 = fun (i : int) -> Float.of_int (2 * i + 1);;

(* 偶数序列：0,2,4,... *)
let f2 = fun (i : int) -> Float.of_int (2 * i);;

(* 序列相等判定：前n项是否都相同 *)
let b = SequenceR.seqeqb 10 f1 f2;;

(* 序列求和：1 + 3 + 5 = 9 *)
let x = SequenceR.seqsum f1 3;;

(* 两个索引的序列：(i,j) *)
let g1 = fun (i : int) (j : int) -> (Float.of_int i, Float.of_int j);;
