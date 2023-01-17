(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

	2022/06/23 12:16
	
	注意：
	1. 需要手动注释 mat.mli 和 mat.ml 中有关 coq_Rabst/coq_Rrepr 的代码，因为对实数构造尚不了解。
*)

open Mat;;
open MatrixR;;
open Inv;;
open InversionR;;

print_string " ====== 矩阵测试 =======\r\n";;

(* 生成内置的二维数组，内容随机生成 *)
let mk_array2 (r : int) (c : int) : int array array =
	let m = Array.make_matrix r c 0 in
		(for ri = 0 to r - 1 do
			for ci = 0 to c - 1 do
				m.(ri).(ci) <- Random.int 100
			done
		done);
		m;;

(* 内置的二维数值转换为 NatFun矩阵 *)
let array2_to_mat (m : int array array) : int -> int -> float =
	fun i j -> float_of_int m.(i).(j);;

(* 生成NatFun随机矩阵 *)
let mkMatRand (n : int) : int -> int -> float =
	array2_to_mat (mk_array2 n n);;

(* 矩阵打印函数 *)
let mprint (r : int) (c : int) (m : int -> int -> float) =
	for ri = 0 to r - 1 do
		for ci = 0 to c - 1 do
			Format.printf "% 4.4f  " (m ri ci);
			print_string (if (ci + 1) mod 20 = 0 then "\n" else "")
		done;
		Format.printf("\r\n")
	done;;

(* 测试运行时间，返回浮点数的秒。原理是返回处理器当前时间，精度大概是几十毫秒可分辨，即0.015s *)
let time f x =
	let t = Sys.time() in
	let fx = f x in
	Printf.printf "Execution time: %.3fs\n" (Sys.time() -. t);
	fx

(* fib测试基准。 time fib 40, 约1.5s *)
let rec fib n = if n < 3 then 1 else fib (n-1) + fib (n-2);;

(** 主程序部分 *)

print_string "m1 = 2x2矩阵\r\n";;
let m1 = l2m' [[1.0;2.0];[3.0;4.0]];;

Format.printf "(0,0):%f, (0,1):%f, (1,2):%f\r\n"
(m1 0 0)
(m1 0 1)
(m1 1 2);;

print_string "全部元素\r\n";;
mprint 2 2 m1;;

print_string "m2 = 5x5矩阵, a_ij = i + j\r\n";;
let m2 = fun (ri:int) (ci:int) -> Float.of_int ri +. Float.of_int ci;;
mprint 5 5 m2;;

print_string "5x5单位矩阵\r\n";;
mprint 5 5 (mat1 5);;

(* 矩阵加法 *)
print_string "m2 + m2\r\n";;
mprint 5 5 (madd 5 5 m2 m2);;


let f dims =
	let m = mk_array2 dims dims in		(* 生成本地二维数组 *)
	let m = array2_to_mat m in				(* 转换为NatFun矩阵 *)
		mprint dims dims m;
		Format.printf "打印 %dx%d 的随机矩阵\r\n" dims dims;;

(* time f 100;; *)

let f dims =
	let m1 = mkMatRand dims in			(* 生成NatFun矩阵 *)
	let m2 = minv dims m1 in				(* 计算逆矩阵 *)
		Format.printf "%dx%d 的随机矩阵\r\n" dims dims;
		Format.printf "原始矩阵:\r\n";
		mprint dims dims m1;
		Format.printf "det = %f\n" (det dims m1);
		Format.printf "逆矩阵:\r\n";
		mprint dims dims m2;;
	
time f 3;;

(* ############################################################################################# *)
(** 为排除Coq引起的问题，使用OCaml手写逆矩阵算法重新测试 *)

(* ========================================================================= *)
(* 版本1，仍然用函数风格，但是使用原生的int作为下标 *)
module Inv1 =
	struct
	
	(* 子矩阵，去掉某行某列 *)
	let submat (f : int -> int -> 'a) (r : int) (c : int) =
		fun i j ->
			let i' = if i < r then i else i + 1 in
			let j' = if j < c then j else j + 1 in
				f i' j'
	
	(* 计算行列式 *)
  let rec det (n : int) (m : int -> int -> 'a) (a0 : 'a) (a1 : 'a) (an1 : 'a) 
      (add:'a->'a->'a) (mul:'a->'a->'a) : 'a =
    if n <= 0 
    then a1
    else
      (let n' = n - 1 in
       (List.fold_left add a0
          (List.map (fun i -> 
               let s = if i mod 2 = 0 then a1 else an1 in
               let a = mul s (m 0 i) in
               let d = det n' (submat m 0 i) a0 a1 an1 add mul in
               mul a d) (List.init n (fun i -> i)))))
	
	(* 伴随矩阵 *)
	let madj (n : int) (f : int -> int -> 'a) (a0 : 'a) (a1 : 'a) (an1 : 'a) 
      (add:'a->'a->'a) (mul:'a->'a->'a) : int -> int -> 'a =
		if n <= 0
		then f
		else
			(let n' = n - 1 in
				(fun i j ->
					let s = if (i + j) mod 2 = 0 then a1 else an1 in
					let d = det n' (submat f j i) a0 a1 an1 add mul in
						mul s d))
	
	(* 逆矩阵 *)
	let minv (n : int) (f : int -> int -> 'a) (a0 : 'a) (a1 : 'a) (an1 : 'a) 
      (add:'a->'a->'a) (mul:'a->'a->'a) (inv: 'a -> 'a) : int -> int -> 'a =
		let d = det n f a0 a1 an1 add mul in
		let d1 = inv d in
		let f' = madj n f a0 a1 an1 add mul in
			MatrixThyInst.mcmul n n d1 f' 
end

open Inv1;;

Format.printf " ======== 新方法1（OCaml原生int和函数）\r\n";;

(* 固定在浮点数上 *)
let det n f = det n f 0. 1. (-1.) (+.) ( *. );;
let madj n f = madj n f 0. 1. (-1.) (+.) ( *. );;
let minv n f = minv n f 0. 1. (-1.) (+.) ( *. ) (fun x -> 1. /. x);;

(* 测试 *)
let g dims =
	let m1 = mkMatRand dims in			(* 生成NatFun矩阵 *)	
	let m2 = minv dims m1 in				(* 计算逆矩阵 *)
		Format.printf "%dx%d 的随机矩阵\r\n" dims dims;
		Format.printf "原始矩阵:\r\n";
		mprint dims dims m1;
		Format.printf "det = %f\n" (det dims m1);
		Format.printf "逆矩阵:\r\n";
		mprint dims dims m2;;
	
time g 7;;


(* ========================================================================= *)
(* 版本2，进一步 使用 Array 替代 Function *)
module Inv2 =
	struct

	(* 矩阵拷贝 *)
	let mat_copy (r:int) (c:int) (m:'a array array) : 'a array array =
		let m' = Array.make_matrix r c (m.(0).(0)) in
			for i = 0 to r - 1 do
				for j = 0 to c - 1 do
					m'.(i).(j) <- m.(i).(j)
				done
			done; m'
	
	(* 取出数组中除去第 i 个元素的剩余部分。用户自行保证 i 在 n 的内部 *)
	let pick (n: int) (f: 'a array) (i: int) : 'a array =
		let f = Array.copy f in
		Array.concat [Array.sub f 0 i; Array.sub f (i+1) (n-i-1)];;

	(* 子矩阵，去掉某行某列 *)
	let submat (n : int) (f : 'a array array) (r : int) (c : int) =
		let f1 = pick n f r in
		let l1 = Array.to_list f1 in
		let l2 = List.map (fun a -> pick n a c) l1 in
			Array.of_list l2;;
	
	(* 计算行列式 *)
  let rec det (n : int) (m : 'a array array) (a0 : 'a) (a1 : 'a) (an1 : 'a) 
      (add:'a->'a->'a) (mul:'a->'a->'a) : 'a =
    if n <= 0 
    then a1
    else
      (let n' = n - 1 in
       (List.fold_left add a0
          (List.map (fun i -> 
               let s = if i mod 2 = 0 then a1 else an1 in
               let a = mul s (m.(0).(i)) in
               let d = det n' (submat n m 0 i) a0 a1 an1 add mul in
               mul a d) (List.init n (fun i -> i)))))
	
	(* 伴随矩阵 *)
	let madj (n : int) (f : 'a array array) (a0 : 'a) (a1 : 'a) (an1 : 'a) 
      (add:'a->'a->'a) (mul:'a->'a->'a) : 'a array array =
		let g = mat_copy n n f in
			if n <= 0
			then g
			else
				(let n' = n - 1 in
					for i = 0 to n' do
						for j = 0 to n' do
							g.(i).(j) <- (
									let s = if (i + j) mod 2 = 0 then a1 else an1 in
									let d = det n' (submat n f j i) a0 a1 an1 add mul in
										mul s d)
						done
					done;
					g);;
	
	(* 矩阵数乘 *)
	let mcmul (r : int) (c : int) (x : 'a) (f : 'a array array) (mul: 'a->'a->'a)
				: 'a array array =
		for i = 0 to r - 1 do
			for j = 0 to c - 1 do
				f.(i).(j) <- mul x f.(i).(j)
			done
		done;
		f;;
	 
	(* 逆矩阵 *)
	let minv (n : int) (f : 'a array array) (a0 : 'a) (a1 : 'a) (an1 : 'a) 
      (add:'a->'a->'a) (mul:'a->'a->'a) (inv: 'a -> 'a) : 'a array array =
		let d = det n f a0 a1 an1 add mul in
		let d1 = inv d in
		let f1 = madj n f a0 a1 an1 add mul in
			mcmul n n d1 f1 mul 

end

open Inv2;;
 
Format.printf " ======== 新方法2（OCaml原生Array）\r\n";;

(* 固定在浮点数上 *)
let det n f = det n f 0. 1. (-1.) (+.) ( *. );;
let madj n f = madj n f 0. 1. (-1.) (+.) ( *. );;
let minv n f = minv n f 0. 1. (-1.) (+.) ( *. ) (fun x -> 1. /. x);;


(* 创建内容为随机浮点数的矩阵 *)
let mkMatRand (n : int) : float array array =
	let m = Array.make_matrix n n 0. in
		(for ri = 0 to n - 1 do
			for ci = 0 to n - 1 do
				m.(ri).(ci) <- Random.float 1000.
			done
		done);
		m;;

(* 矩阵打印函数 *)
let mprint (r : int) (c : int) (m : float array array) =
	for ri = 0 to r - 1 do
		for ci = 0 to c - 1 do
			Format.printf "% 4.4f  " (m.(ri).(ci));
			print_string (if (ci + 1) mod 20 = 0 then "\n" else "")
		done;
		Format.printf("\r\n")
	done;;

(* 测试 *)
let g (dims : int) =
	let m1 = mkMatRand dims in			(* 生成NatFun矩阵 *)
	let m2 = minv dims m1 in				(* 计算逆矩阵 *)
		Format.printf "%dx%d 的随机矩阵\r\n" dims dims;
		Format.printf "原始矩阵:\r\n";
		mprint dims dims m1;
		Format.printf "逆矩阵:\r\n";
		mprint dims dims m2;;

time g 8;;
