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
open MatrixModel
open MatrixTheory
   

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


(** command option processing *)

(* global variables for command options. *)
let cmdopt_matrix_size : int ref = ref 10

let set_matrix_size (i:int)   = cmdopt_matrix_size := i

let read_options () : string =
  let speclist =
    [
      ("-n", Arg.Int set_matrix_size, "Set matrix dimension");
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
  (* let m1 = minit n n (fun i j -> float_of_int (i + j)) in
   * let m2 = minit n n (fun i j -> float_of_int (i + j + 1)) in *)
  let m1 = minit n n (fun i j -> Random.float 1.0) in
  let m2 = minit n n (fun i j -> Random.float 1.0) in
  let m3 = mmul m1 m2 in
  let r = mrows m1 in
  let c = mcols m2 in
  let s = mcols m2 in
  let str = Printf.sprintf
              "(%d,%d) * (%d,%d) = (%d,*%d), m[%d,%d]=%f"
              r c c s (mrows m3) (mcols m3) (r-1) (s-1) (mget m3 (r-1) (s-1)) in
  print_endline str;;
  
let main () =
  let _ = read_options () in
  let n = !cmdopt_matrix_size in
  show_hello_msg ();
  test_mmul n;;
  
main ();;
