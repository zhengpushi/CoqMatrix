(* #load "matrix.cmo" *)
    
open Printf
open Matrix
   
   
(* let _ = mk_mat 3 3 *)

let welcome_msg =
  print_endline "test program v0.1\n";;

(* let main () =
 *   let a = Array.make 10 10 in
 *   let b = is_even 10 in
 *   printf "a.[0] = %d\n" a.(0);
 *   printf "10 is even? %b\n" b;; *)

(* let _ = main ();; *)
  
let _ =
  let a = Matrix.mk_mat (i2n 10) (S O) in
  a;;
  
    
