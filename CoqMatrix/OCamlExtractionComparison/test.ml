(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Test matrix ocaml program which extracted from Coq
  author    : ZhengPu Shi
  date      : Nov 1, 2022

 *)

(** 这些指令在REPL下使用，编译时需要去掉 *)
#use "topfind";;
#require "unix";;
#use "matrix.ml";;

open Printf
open Unix

(* calculate the computation time of executing a function. *)
let calc_exe_time (f : 'a -> unit) (n:'a) =
  let start_time = Sys.time () in
  let _ = f n in
  let end_time = Sys.time () in
  let elapsed = end_time -. start_time in
    printf "Execution of f () takes %6.2f seconds\n" elapsed

(** 精度为秒的当前时间的整数 *)
let current_time_get () = Float.to_int (Unix.time ())

(** 更新随机数生成器，使用固定种子，或当前时间为种子 *)
let random_update =
  (* 固定种子的好处时，每次执行的随机序列都是相同的 *)
  let seed = 1 in
  (* 当前时间种子的好处时，随机性更好。*)
  (* let seed = current_time_get () in *)
  Random.init seed

(** 生成 m * n 的列表 *)
let dl_gen (m:int) (n:int) : float list list =
  let max = Float.of_int (m * n) in
  let half = max /. 2. in
  let get_randomval (i:int) = Random.float max -. half in
  random_update;
  List.init m (fun _ -> List.init n get_randomval);;

(** 生成数据测试 *)
(* dl_gen 5 3;; *)

(** 矩阵模型类别*)
type matmodel =
  | MM_DL | MM_DP | MM_DR | MM_NF | MM_FF

(** 打印嵌套列表到字符串 *)
let dl2str (dl:'a list list) (a2str:'a -> string) : string =
  let l2str l = List.fold_left (fun s i -> s^(a2str i)) "" l in
  List.fold_left (fun s l -> s^(l2str l)^"\n") "" dl;;

(** 打印嵌套实数列表到字符串 *)
let float_dl2str (dl:float list list) : string =
  (* let f2str = Printf.sprintf "%10.2f" in *)
  let f2str = Printf.sprintf "%10.1e" in
  dl2str dl f2str;;

(** 生成数据并打印的测试 *)
let gen_then_print_test () =
  let dl : float list list = dl_gen 5 8 in
  print_endline (float_dl2str dl);;

(** list中的某个元素，越界返回默认值 *)
let nth_def l n def_val  =
  if n < 0 then def_val else
  let rec nth_aux l n =
    match l with
    | [] -> def_val
    | a::l -> if n = 0 then a else nth_aux l (n-1)
  in nth_aux l n;;

(** list中的前n项，不足填充默认值 *)
let list_top_def l n def_val =
  let idx = List.init n (fun i -> i) in
  List.map (fun i -> nth_def l i def_val) idx;;

(** 取出 dl 中的部分内容，比如 4*5的内容，不足填充 0 *)
let dl_top_def (dl:'a list list) (rows:int) (cols:int) (defval:'a) =
  let dl = list_top_def dl rows [] in
  List.map (fun l -> list_top_def l cols defval) dl;;

(* calc_exe_time (fun _ -> ignore (dl_top_def [[1;2;3];[4;5;6]] 4 5 0)) ();; *)
  
(** 矩阵乘法实验 *)

(** 根据不同模型，返回一组函数。因为类型不同，无法用match写出 *)
(* let get_fcns_of_mm (mm:matmodel) = *)
(*   match mm with *)
(*   | MM_DL -> (DL.l2m, DL.m2l, DL.mmul) *)
(*   | MM_DP -> (DP.l2m, DP.m2l, DP.mmul) *)
(*   | MM_DR -> (DR.l2m, DR.m2l, DR.mmul) *)
(*   | MM_NF -> (NF.l2m, NF.m2l, NF.mmul) *)
(*   | MM_FF -> (FF.l2m, FF.m2l, FF.mmul);; *)

(** 第1版，矩阵模型参数未使用，需要手动修改注释来切换模型 *)
let mmul_ex ?(mm=MM_DL) (r:int) (c:int) (s:int) (is_print:bool) =
  (* 这些模型要手动指定 *)
  let (l2m,m2l,mmul) = (DL.l2m, DL.m2l, DL.mmul) in
  (* let (l2m,m2l,mmul) = (DP.l2m, DP.m2l, DP.mmul) in *)
  (* let (l2m,m2l,mmul) = (DR.l2m, DR.m2l, DR.mmul) in *)
  (* let (l2m,m2l,mmul) = (NF.l2m, NF.m2l, NF.mmul) in *)
  (* let (l2m,m2l,mmul) = (FF.l2m, FF.m2l, FF.mmul) in *)
  let l1 = dl_gen r c in
  let l2 = dl_gen c s in
  let m1 = l2m r c l1 in
  let m2 = l2m c s l2 in
  let m3 = mmul r c s m1 m2 in
  let l3 = m2l r c m3 in
  let dl_top dl = dl_top_def dl 2 8 0.0 in
  let show_dl dl r c prefix =
    print_endline (Printf.sprintf "%s_%dx%d:"prefix r c);
    print_endline (float_dl2str (dl_top dl)) in
  if is_print then
    (show_dl l1 r c "A";
    show_dl l2 c s "B";
    show_dl l3 r s "AxB");;

(* calc_exe_time (mmul_ex 4 5 6) true;; *)

(** 第二版，矩阵模型参数启用 *)
let mmul_ex ?(mm=MM_DL) (r:int) (c:int) (s:int) (is_print:bool) =
  (* 生成两个矩阵的数据 *)
  let l1 = dl_gen r c in
  let l2 = dl_gen c s in
  (* 虽然函数类型不同，但计算结果却可以统一 *)
  let l3 =
    match mm with
    | MM_DL -> let (l2m,m2l,mmul) = (DL.l2m, DL.m2l, DL.mmul) in
               m2l r c (mmul r c s (l2m r c l1) (l2m c s l2))
    | MM_DP -> let (l2m,m2l,mmul) = (DP.l2m, DP.m2l, DP.mmul) in
               m2l r c (mmul r c s (l2m r c l1) (l2m c s l2))
    | MM_DR -> let (l2m,m2l,mmul) = (DR.l2m, DR.m2l, DR.mmul) in
               m2l r c (mmul r c s (l2m r c l1) (l2m c s l2))
    | MM_NF -> let (l2m,m2l,mmul) = (NF.l2m, NF.m2l, NF.mmul) in
               m2l r c (mmul r c s (l2m r c l1) (l2m c s l2))
    | MM_FF -> let (l2m,m2l,mmul) = (FF.l2m, FF.m2l, FF.mmul) in
               m2l r c (mmul r c s (l2m r c l1) (l2m c s l2))
  in
  (* 输出数据 *)
  let dl_top dl = dl_top_def dl 2 8 0.0 in
  let show_dl dl r c prefix =
    print_endline (Printf.sprintf "%s_%dx%d:"prefix r c);
    print_endline (float_dl2str (dl_top dl)) in
  if is_print then
    (show_dl l1 r c "A";
    show_dl l2 c s "B";
    show_dl l3 r s "AxB");;

(* calc_exe_time (mmul_ex 4 5 6) true;; *)

(** command option processing *)

(* global variables for command options. *)
let cmdopt_matrix_model : matmodel ref = ref MM_DL
let cmdopt_matrix_size : int ref = ref 10
let cmdopt_show_matrix : bool ref = ref true
let cmdopt_benchmark : bool ref = ref false

(* global variable setting functions. *)
let set_matrix_model (s:string) =
  let mm = match s with
    | "DL" -> MM_DL | "DP" -> MM_DP | "DR" -> MM_DR
    | "NF" -> MM_NF | "FF" -> MM_FF | _ -> failwith "model error, see -help" in
  cmdopt_matrix_model := mm

let show_matrix_model mm =
  let msg = match mm with
    | MM_DL -> "DL" | MM_DP -> "DP" | MM_DR -> "DR"
    | MM_NF -> "NF" | MM_FF -> "FF" in
  print_endline (sprintf "matrix model : %s" msg)

let set_matrix_size (i:int)   = cmdopt_matrix_size := i

let show_matrix_size n =
  let r = n in
  let c = r in
  let s = r in
  let msg = sprintf "matrix size : %dx%d * %dx%d -> %dx%d"
              r c c s r s in
  print_endline msg;;

let set_show_matrix (b:bool)  = cmdopt_show_matrix := b
let set_benchmark (b:bool)  = cmdopt_benchmark := b

let read_options () : string =
  let speclist =
    [
      ("-mm", Arg.String set_matrix_model, "Set matrix model (DL/DP/DR/NF/FF)");
      ("-size", Arg.Int set_matrix_size, "Set matrix dimension");
      ("-print", Arg.Bool set_show_matrix, "Show matrix content");
      ("-benchmark", Arg.Bool set_benchmark, "Benchmark mode, automatic test");
    ]
  in
  let usage_msg = "Usage: ./test [option] where options are:" in
  let _ = Arg.parse speclist (fun s -> ()) usage_msg in
  ""

let show_hello_msg () =
  let hello_msg = "Program for test matrix." in
  print_endline hello_msg

(** 基准测试，自动对前四个模型测试，并输出运行时间 *)
let benchmark_run () =
  (* 模型列表 *)
  let mm_lst = [MM_DL; MM_DP; MM_DR; MM_NF] in
  (* 更新模型序号，并同时判断是否模型循环完成 *)
  let next_mmidx i : int * bool =
    if (i+1) mod 4 = 0 then (0,true) else (i+1,false) in
  (* 更新矩阵规模 *)
  let next_size size =
    Float.to_int ((Float.of_int size) *. 1.2) in
  (* 无限循环 *)
  let rec run mm_idx size : unit =
    let mm = List.nth mm_lst mm_idx in (* 取出矩阵模型 *)
    show_matrix_model mm; (* 打印矩阵模型 *)
    show_matrix_size size; (* 打印矩阵大小 *)
    calc_exe_time (mmul_ex ~mm size size size) false; (* 矩阵乘法 *)
    print_endline "---------------------------------";
    let (mm_idx,mm_loop_ok) = next_mmidx mm_idx in (* 更新模型序号、循环标志 *)
    let size = if mm_loop_ok then next_size size else size in (* 更新规模 *)
    run mm_idx size in (* 再次循环 *)
  run 0 50;;

let main () =
  let _ = read_options () in
  let mm = !cmdopt_matrix_model in
  let r = !cmdopt_matrix_size in
  let is_print = !cmdopt_show_matrix in
  let is_benchmak = !cmdopt_benchmark in
  show_hello_msg ();
  if is_benchmak then
    benchmark_run ()
  else (
    show_matrix_model mm;
    show_matrix_size r;
    calc_exe_time (mmul_ex ~mm r r r) is_print
  );;
  
main ();;
