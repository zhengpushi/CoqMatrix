(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Test matrix ocaml program which extracted from Coq
  author    : ZhengPu Shi
  date      : Nov 1, 2022

 *)

(** These indicatos only using in REPL, and need to be removed when compiling *)
#use "topfind";;
#require "unix";;
#use "matrix.ml";;

open Printf
open Unix

(* calculate the computation time of executing a function. *)
let calc_exe_time_core (f : 'a -> unit) (n:'a) : float =
  let start_time = Sys.time () in
  let _ = f n in
  let end_time = Sys.time () in
  let elapsed = end_time -. start_time in
  elapsed

(* calculate the computation time of executing a function, and print time elapsed. *)
let calc_exe_time (f : 'a -> unit) (n:'a) =
  let elapsed = calc_exe_time_core f n in
  printf "Execution of f () takes %6.2f seconds\n" elapsed
  
(** Get the current time in seconds with an integer type *)
let current_time_get () = Float.to_int (Unix.time ())

(** Update random generator, using fixed seed or use current time as seed. *)
let random_update =
  (* when using fixed seed, the random output every time are same from first start *)
  let seed = 1 in
  (* when using current time as seed, there are better randomness *)
  (* let seed = current_time_get () in *)
  Random.init seed

(** Trim a float number to given length precision.
    E.g. f 123.45678 2 ==> 123.45 *)
let float_trim (x : float) (n : int) : float =
  let coef = 10.0 ** (float_of_int n) in
  let i = int_of_float (x *. coef) in
  let x' = (float_of_int i) /. coef in
  x'

(** Generate a list with m*n length *)
let dl_gen (m:int) (n:int) : float list list =
  let max = Float.of_int (m * n) in
  let half = max /. 2. in
  let get_randomval (i:int) = Random.float max -. half in
  (* let get_randomval (i:int) = float_trim (Random.float max -. half) 2 in *)
  random_update;
  List.init m (fun _ -> List.init n get_randomval);;

(** Create test data *)
(* dl_gen 5 3;; *)

(** matrix model types*)
type matmodel =
  | MM_DL | MM_DP | MM_DR | MM_NF | MM_SF

(** Print a dlist of any type to string *)
let dl2str (dl:'a list list) (a2str:'a -> string) : string =
  let l2str l = List.fold_left (fun s i -> s^(a2str i)) "" l in
  List.fold_left (fun s l -> s^(l2str l)^"\n") "" dl;;

(** Print a dlist of float type to string *)
let float_dl2str (dl:float list list) : string =
  (* let f2str = Printf.sprintf "%10.2f" in *)
  let f2str = Printf.sprintf "%10.1e" in
  dl2str dl f2str;;

(** Generate random data and print *)
let gen_then_print_test () =
  let dl : float list list = dl_gen 5 8 in
  print_endline (float_dl2str dl);;

(** Get n-th element of a list, get def_val when index-out-of-bounds *)
let nth_def l n def_val  =
  if n < 0 then def_val else
  let rec nth_aux l n =
    match l with
    | [] -> def_val
    | a::l -> if n = 0 then a else nth_aux l (n-1)
  in nth_aux l n;;

(** Get top n items of a list, fill def_val when not enough *)
let list_top_def l n def_val =
  let idx = List.init n (fun i -> i) in
  List.map (fun i -> nth_def l i def_val) idx;;

(** Get top rows*cols items of a dlist, fill def_val when not enough *)
let dl_top_def (dl:'a list list) (rows:int) (cols:int) (defval:'a) =
  let dl = list_top_def dl rows [] in
  List.map (fun l -> list_top_def l cols defval) dl;;

(* calc_exe_time (fun _ -> ignore (dl_top_def [[1;2;3];[4;5;6]] 4 5 0)) ();; *)
  
(** Experinemt for matrix multiplication *)

(** Get a function by given model. Because type mismatch in all cases, we failed to
    write out this function. *)
(* let get_fcns_of_mm (mm:matmodel) = *)
(*   match mm with *)
(*   | MM_DL -> (DL.l2m, DL.m2l, DL.mmul) *)
(*   | MM_DP -> (DP.l2m, DP.m2l, DP.mmul) *)
(*   | MM_DR -> (DR.l2m, DR.m2l, DR.mmul) *)
(*   | MM_NF -> (NF.l2m, NF.m2l, NF.mmul) *)
(*   | MM_FF -> (FF.l2m, FF.m2l, FF.mmul);; *)

(** Version 1: use fixed parameter of model, we need switch model manually *)
let mmul_ex ?(mm=MM_DL) (r:int) (c:int) (s:int) (is_print:bool) =
  (* These functions need to be specify manally *)
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

(** Version 2: the model parameter is available *)
let mmul_ex ?(mm=MM_DL) (r:int) (c:int) (s:int) (is_print:bool) =
  (* create data for two matrices *)
  let l1 = dl_gen r c in
  let l2 = dl_gen c s in
  (* although matrix type are different, but m2l get unified type *)
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
    | MM_SF -> let (l2m,m2l,mmul) = (SF.l2m, SF.m2l, SF.mmul) in
               m2l r c (mmul r c s (l2m r c l1) (l2m c s l2))
  in
  (* output the data *)
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
let cmdopt_benchmarkall : bool ref = ref false

(* global variable setting functions. *)
let set_matrix_model (s:string) =
  let mm = match s with
    | "DL" -> MM_DL | "DP" -> MM_DP | "DR" -> MM_DR
    | "NF" -> MM_NF | "SF" -> MM_SF | _ -> failwith "model error, see -help" in
  cmdopt_matrix_model := mm

(* model to string *)
let mm2str (mm : matmodel) : string =
  let str = match mm with
  | MM_DL -> "DL" | MM_DP -> "DP" | MM_DR -> "DR"
  | MM_NF -> "NF" | MM_SF -> "SF" in
  str

let show_matrix_model mm =
  let msg = mm2str mm in
  print_endline (sprintf "matrix model : %s" msg)

let set_matrix_size (i:int)   = cmdopt_matrix_size := i

let show_matrix_size n =
  let r = n in
  let c = r in
  let s = r in
  let msg = sprintf "matrix size : %dx%d * %dx%d -> %dx%d"
              r c c s r s in
  print_endline msg;;

let show_benchmark_result_once id mm size time =
  let str_id = sprintf "%d: " id in
  let str_mm = mm2str mm in
  let str_size = sprintf  "%d" size in
  let str_time = sprintf "%6.2f seconds" time in
  let str =
    str_id
    ^ "model:" ^ str_mm
    ^ ", size:" ^ str_size
    ^ ", time:" ^ str_time in
  print_endline str;;

let set_show_matrix (b:bool)  = cmdopt_show_matrix := b
let set_benchmark (b:bool)  = cmdopt_benchmark := b
let set_benchmarkall (b:bool)  = cmdopt_benchmarkall := b

let read_options () : string =
  let speclist =
    [
      ("-mm", Arg.String set_matrix_model, "Set matrix model (DL/DP/DR/NF/SF)");
      ("-size", Arg.Int set_matrix_size, "Set matrix dimension");
      ("-print", Arg.Bool set_show_matrix, "Show matrix content");
      ("-benchmark", Arg.Bool set_benchmark, "Benchmark mode, test one model");
      ("-benchmarkall", Arg.Bool set_benchmarkall, "Benchmark mode, test all models");
    ]
  in
  let usage_msg = "Usage: ./test [option] where options are:" in
  let _ = Arg.parse speclist (fun s -> ()) usage_msg in
  ""

let show_hello_msg () =
  let hello_msg = "Program for test matrix." in
  print_endline hello_msg

(** Benchmark, automatic test one model, also output running time *)
let benchmark_run_one mm =
  (* update matrix size *)
  let next_size size =
    Float.to_int ((Float.of_int size) *. 1.2) in
  (* infinite loop *)
  let rec run id size : unit =
    let elapsed = calc_exe_time_core (mmul_ex ~mm size size size) false in (* matrix multiplication *)
    show_benchmark_result_once id mm size elapsed;
    run (id+1) (next_size size) in (* next loop *)
  run 1 50;;

(** Benchmark, automatic test first four models, also output running time *)
let benchmark_run_all () =
  (* list of models *)
  let mm_lst = [MM_DL; MM_DP; MM_DR; MM_SF] in
  (* update model index, and check if finished the model loop *)
  let next_mmidx i : int * bool =
    if (i+1) mod 4 = 0 then (0,true) else (i+1,false) in
  (* update matrix size *)
  let next_size size =
    Float.to_int ((Float.of_int size) *. 1.2) in
  (* infinite loop *)
  let rec run id mm_idx size : unit =
    let mm = List.nth mm_lst mm_idx in (* get matrix model *)
    let elapsed = calc_exe_time_core (mmul_ex ~mm size size size) false in (* matrix multiplication *)
    show_benchmark_result_once id mm size elapsed;
    let (mm_idx,mm_loop_ok) = next_mmidx mm_idx in (* update model index, loop flag *)
    let size = if mm_loop_ok then next_size size else size in (* update matirx size *)
    run (id+1) mm_idx size in (* next loop *)
  run 1 0 50;;

let main () =
  let _ = read_options () in
  let mm = !cmdopt_matrix_model in
  let r = !cmdopt_matrix_size in
  let is_print = !cmdopt_show_matrix in
  let is_benchmark = !cmdopt_benchmark in
  let is_benchmarkall = !cmdopt_benchmarkall in
  show_hello_msg ();
  if is_benchmark then
    benchmark_run_one mm
  else if is_benchmarkall then
    benchmark_run_all ()
  else (
    show_matrix_model mm;
    show_matrix_size r;
    calc_exe_time (mmul_ex ~mm r r r) is_print
  );;
  
main ();;
