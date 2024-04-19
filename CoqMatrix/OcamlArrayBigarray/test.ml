(*
  Copyright 2024 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Test matrix ocaml program which extracted from Coq
  author    : ZhengPu Shi
  date      : Mar 22, 2024

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
  (* let seed = 1 in *)
  (* when using current time as seed, there are better randomness *)
  let seed = current_time_get () in
  Random.init seed

(** Trim a float number to given length precision.
    E.g. f 123.45678 2 ==> 123.45 *)
let float_trim (x : float) (n : int) : float =
  let coef = 10.0 ** (float_of_int n) in
  let i = int_of_float (x *. coef) in
  let x' = (float_of_int i) /. coef in
  x'

(** Generate a float number with default precision *)
let gen_float () : float =
  float_trim (Random.float 1.0) 3

(** Convert `float` to string *)
let float2str (f:float) : string =
  Printf.sprintf "%8.3f" f
  
(** matrix type *)
type matrix = int * int * (mat);;

  
(* (\** aa : float array array *\)
 * type aa = float array array;;
 * 
 * (\** Generate an `aa` with r*c shape *\)
 * let gen_aa (r:int) (c:int) : aa =
 *   random_update;
 *   Array.init r (fun _ -> Array.init c (fun _ -> gen_float()));;
 * 
 * (\** Get shape of an `aa` *\)
 * let shape4aa (x:aa) : int * int =
 *   (Array.length x, Array.length (Array.get x 0));; *)

(** Convert `mat` to string *)
let arr2str (a:float array) : string =
  Array.fold_left (fun s f -> s^(float2str f)) "" a

(** Convert an `aa` to string *)
let aa2str (x:aa) : string =
  Array.fold_left (fun s a -> s^(arr2str a)^"\n") "" x
  
(** Print an `aa` *)
let prt_aa (x:aa) : unit =
  print_endline (aa2str x);;

(** Convert `float array array` to matrix *)
let aa2mat (x:aa) : matrix =
  let (r,c) = shape4aa x in
  let f : int->int->float =
    fun i j -> if (i >= r) || (j >= c) then 0. else Array.get (Array.get x i) j in
  (r,c,f);;

(** Generate a `matrix` with r*c shape *)
let gen_mat (r:int) (c:int) : matrix =
  aa2mat (gen_aa r c);;

(** Convert `int->float` to string *)
let f2str (n:int) (f:int->float) : string =
  let rec loop (i:int) (acc:string) : string =
    if i < n
    then loop (i+1) (acc ^ float2str (f i))
    else acc in
  loop 0 "";;

(** Convert `int->int->float` to string *)
let ff2str (r:int) (c:int) (ff:int->int->float) : string =
  let rec loop (i:int) (acc:string) : string =
    if i < r
    then loop (i+1) (acc ^ f2str c (ff i) ^ "\n")
    else acc in
  loop 0 "";;
  
(** Print a `matrix` *)
let prt_mat (prefix:string) (m:matrix) : unit =
  let (r,c,ff) = m in
  let s = Printf.sprintf "%s matrix_%dx%d:\n%s" prefix r c (ff2str r c ff) in
  print_endline s;;

(** matrix multiplication *)
let mmulR (m1:matrix) (m2:matrix) : matrix =
  let (r1,c1,f1) = m1 in
  let (r2,c2,f2) = m2 in
  (r1,c2, mmul_R r1 c1 c2 f1 f2);;

(** matrix inversion *)
let minvR_GE (m:matrix) : matrix =
  let (r,c,f) = m in
  (r,c, minvGE_R r f);;

let minvR_AM (m:matrix) : matrix =
  let (r,c,f) = m in
  (r,c, minvAM_R r f);;

(** command option processing *)

(* global variables for command options. *)
let cmdopt_matrix_size : int ref = ref 10
let cmdopt_show_matrix : bool ref = ref true
let cmdopt_test_GE : bool ref = ref false
let cmdopt_test_AM : bool ref = ref false

let set_matrix_size (i:int)   = cmdopt_matrix_size := i
let set_show_matrix (b:bool)  = cmdopt_show_matrix := b
let set_test_GE (b:bool)  = cmdopt_test_GE := b
let set_test_AM (b:bool)  = cmdopt_test_AM := b

let read_options () : string =
  let speclist =
    [
      ("-size", Arg.Int set_matrix_size, "Set matrix dimension");
      ("-print", Arg.Bool set_show_matrix, "Show matrix content?");
      ("-GE", Arg.Bool set_test_GE, "Is test minvGE?");
      ("-AM", Arg.Bool set_test_AM, "Is test minvAE?");
    ]
  in
  let usage_msg = "Usage: ./matrix [option] where options are:" in
  let _ = Arg.parse speclist (fun s -> ()) usage_msg in
  "";;

let show_hello_msg () =
  let hello_msg = "Program for test matrix." in
  print_endline hello_msg

(* 测试矩阵乘法 *)
let test_mmul (n:int) : unit =
  let m1 = gen_mat n n in
  let m2 = gen_mat n n in
  let m3 = mmulR m1 m2 in
  
  (* let (r,c,ff) = m3 in
   * print_endline (Printf.sprintf "m3(0,0)=%s" (float2str (ff 0 0)));; *)

  print_endline "Test matrix multiplication:";
  prt_mat "m1=" m1;
  prt_mat "m2=" m2;
  prt_mat "m1*m2=" m3;;

(* 测试矩阵求逆 *)
let test_minvGE (n:int) : unit =
  let m = gen_mat n n in
  let m' = minvR_GE m in
  print_endline "Test matrix inversion GE";
  prt_mat "m=" m;
  prt_mat "m'" m';;

let test_minvAM (n:int) : unit =
  let m = gen_mat n n in
  let m' = minvR_AM m in
  print_endline "Test matrix inversion AM";
  prt_mat "m=" m;
  prt_mat "m'" m';;
  
let main () =
  let _ = read_options () in
  let n = !cmdopt_matrix_size in
  let is_test_GE = !cmdopt_test_GE in
  let is_test_AM = !cmdopt_test_AM in
  (* let is_print = !cmdopt_show_matrix in *)
  show_hello_msg ();
  (* test_mmul n;; *)
  if is_test_GE then
    test_minvGE n;
  if is_test_AM then
    test_minvAM n;;
  
main ();;
       
