(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on RAST (short as A).
  author    : ZhengPu Shi
  date      : 2023.03
*)

Require Import StrExt.
Require Import MatrixAll.


(* ######################################################################### *)
(** * Export matrix theory on concrete elements *)

Module MatrixAllA.
  Include EqDecidableFieldMatrixTheory BaseTypeA DecidableFieldElementTypeA.
  Export RAST.
  Open Scope A_scope.
  Open Scope mat_scope.
End MatrixAllA.
  
Module MatrixA_DL.
  Include MatrixAllA.DL.
  Export RAST.
  Open Scope A_scope.
  Open Scope mat_scope.
End MatrixA_DL.

Module MatrixA_DP.
  Include MatrixAllA.DP.
  Export RAST.
  Open Scope A_scope.
  Open Scope mat_scope.
End MatrixA_DP.

Module MatrixA_DR.
  Include MatrixAllA.DR.
  Export RAST.
  Open Scope A_scope.
  Open Scope mat_scope.
End MatrixA_DR.

Module MatrixA_NF.
  Include MatrixAllA.NF.
  Export RAST.
  Open Scope A_scope.
  Open Scope mat_scope.
End MatrixA_NF.

Module MatrixA_SF.
  Include MatrixAllA.SF.
  Export RAST.
  Open Scope A_scope.
  Open Scope mat_scope.
End MatrixA_SF.

Module MatrixA_FF.
  Include MatrixAllA.FF.
  Export RAST.
  Open Scope A_scope.
  Open Scope mat_scope.
End MatrixA_FF.


(* ######################################################################### *)
(** * Extended matrix theory *)

(** Set a default model *)
Export MatrixA_SF.


(** Try to get a direct form of inversion matrix of symbol matrix,
    with the help of RAST (Abstract Syntax Tree of R type) *)
Module Simplify_by_RAST.

  Notation "0" := A0.
  Notation "1" := A1.
  Notation "2" := (1 + 1)%A.
  Notation "3" := (1 + 2)%A.
  Infix "+" := Aadd.
  Infix "-" := Asub.
  Infix "*" := Amul.
  
  (** simplify each element of a list n times *)
  Definition dl_nsimp (dl : list (list A)) (n : nat) :=
    map (map (fun t => nsimp t n)) dl.
  
  (** convert a dlist of A type to dlist of R type *)
  Definition dl_A2R (dl : list (list A)) : list (list R) :=
    map (map A2R) dl.
  
  (** ** We will test the simplification effect of symbol matrix expression with the 
      help of RAST *)
  
  (** Version 1, a general test *)
  Section TestV1.
    
    Variable a00 a01 a02 a10 a11 a12 a20 a21 a22 : A.
    
    Let m1 := mk_mat_1_1 a00.
    Let m2 := mk_mat_2_2 a00 a01 a10 a11.
    Let m3 := mk_mat_3_3 a00 a01 a02 a10 a11 a12 a20 a21 a22.

    (* inverse matrix *)
    Let l1 := Eval cbv in m2l (minv m1).
    Let l2 := Eval cbv in m2l (minv m2).
    Let l3 := Eval cbv in m2l (minv m3).

    (* We can observed that, there are redundant things in an expression *)
    Compute l1.

    (* After using the "simp" or "nsimp", the result is better *)
    Compute (dl_nsimp l1 3).
    Compute (dl_nsimp l1 6). (* better result *)
    (* But, if we simplify a term more times, the result will be expanded too much. *)
    Compute (dl_nsimp l1 7).

    (* So, we should give an abstract expression with the help of "ALit x" *)
  End TestV1.
  
  (** Version 2, use "ALit (r : R)" to write more abstract expression *)
  Section TestV2.
    Open Scope R.
    Variable r00 r01 r02 r10 r11 r12 r20 r21 r22 : R.
    Let a00 := ALit r00. Let a01 := ALit r01. Let a02 := ALit r02.
    Let a10 := ALit r10. Let a11 := ALit r11. Let a12 := ALit r12.
    Let a20 := ALit r20. Let a21 := ALit r21. Let a22 := ALit r22.
    
    Let m1 := mk_mat_1_1 a00.
    Let m2 := mk_mat_2_2 a00 a01 a10 a11.
    Let m3 := mk_mat_3_3 a00 a01 a02 a10 a11 a12 a20 a21 a22.

    (* Determinant *)
    Compute det m1.
    Compute A2R (det m1).
    Compute A2R (nsimp (det m1) 5).   (* = r00 *)
    
    Compute A2R (nsimp (det m2) 10).  (* = r00 * r11 + - r01 * r10 *)
    
    Compute A2R (nsimp (det m3) 30).
    (* = r00 * r11 * r22 + r00 * - r12 * r21 + - r01 * r10 * r22 
       + - r01 * - r12 * r20 + r02 * r10 * r21 + r02 * - r11 * r20 *)
    
    (* Inverse matrix *)
    Let l1 := Eval cbv in m2l (minv m1).
    Let l2 := Eval cbv in m2l (minv m2).
    Let l3 := Eval cbv in m2l (minv m3).
    Compute dl_A2R (dl_nsimp l1 10). (*  = [[/ r11]] *)
    
    Compute dl_A2R (dl_nsimp l2 20).
    (*
      = [[/ (r00 * r11 + - r01 * r10) * r11; - / (r00 * r11 + - r01 * r10) * r01];
      [- / (r00 * r11 + - r01 * r10) * r10; / (r00 * r11 + - r01 * r10) * r00]]
     *)
    
    Compute dl_A2R (dl_nsimp l3 50).
    
  End TestV2.

  (** Version 3, test with matrix of any dimension *)
  Module TestV3_any_dim.
    
    Open Scope nat.

    (** Firstly, we want to represent a variable with a string.
        For example, "a00" "a01"  *)

    (** Convert two natural numbers to a string.
        For exmaple, "a" 2 3 => "a23" *)
    Definition nn2s (prefix:string) (i j:nat) : string :=
      (prefix ++ (nat2str i) ++ (nat2str j))%string.
    
    (** Construct a dlist of strings of a matrix elements *)
    Definition mat_vars_s (r c:nat) : list (list string) :=
      map (fun i => map (nn2s "a" i) (seq 0 c)) (seq 0 r).
    
    Compute mat_vars_s 2 3.
    (* = [["a00"; "a01"; "a02"]; ["a10"; "a11"; "a12"]] *)
        
    (** Secondly,let's give an abstract environment function, which could 
        convert a string to variable of R type *)
    Variable env_s2r : string -> R.
    Definition env_s2a (s : string) : A := ALit (env_s2r s).

    (* And, let it be an automatic coercion *)
    Coercion env_s2a : string >-> A.
    
    (** Now, we can make a matrix with these abstract functions *)
    Definition m1 r c : mat r c :=
      mk_mat (fun i j => env_s2a (nth j (nth i (mat_vars_s r c) []) "")).
    
    (* Time Compute m1 9 9. *)
    (* Time Compute (m1 100 100)!80!90. *)
    
    (* Give the dimension of a square matrix *)
    Definition ORDERS := 4.
    Definition ROWS := ORDERS.
    Definition COLS := ORDERS.
    
    (** We can eval the strings beforehand, then construct a matrix with
        these strings. Thus, the access speed will be faster *)
    Definition mat_vars_given := Eval cbv in (mat_vars_s ROWS COLS).
    
    Definition m2 : mat ROWS COLS :=
      mk_mat (fun i j =>
                env_s2a (nth j (nth i mat_vars_given []) "")).

    Time Definition d2 := Eval cbv in (m2l (minv m2)).
    
    (* Check d2. *)
    (* Check (hd [] d2). *)
    (* Check (hd A0 (hd [] d2)). *)
    (* Compute (hd A0 (hd [] d2)). *)
    (* Compute (hd A0 (hd [] (dl_nsimp d2 3))). *)
    Let t1 := Eval cbv in (hd A0 (hd [] (dl_nsimp d2 0))).

    (* Compute (nsimp t1 150). *)

    Notation a00 := (ALit (env_s2r "a00")).
    Notation a01 := (ALit (env_s2r "a01")).
    Notation a02 := (ALit (env_s2r "a02")).
    Notation a03 := (ALit (env_s2r "a03")).
    Notation a04 := (ALit (env_s2r "a00")).
    Notation a10 := (ALit (env_s2r "a10")).
    Notation a11 := (ALit (env_s2r "a11")).
    Notation a12 := (ALit (env_s2r "a12")).
    Notation a13 := (ALit (env_s2r "a13")).
    Notation a14 := (ALit (env_s2r "a14")).
    Notation a20 := (ALit (env_s2r "a20")).
    Notation a21 := (ALit (env_s2r "a21")).
    Notation a22 := (ALit (env_s2r "a22")).
    Notation a23 := (ALit (env_s2r "a23")).
    Notation a24 := (ALit (env_s2r "a24")).
    Notation a30 := (ALit (env_s2r "a30")).
    Notation a31 := (ALit (env_s2r "a31")).
    Notation a32 := (ALit (env_s2r "a32")).
    Notation a33 := (ALit (env_s2r "a33")).
    Notation a34 := (ALit (env_s2r "a34")).
    
    (* Compute (nsimp t1 150). *)

    (* finally, we got the simplified result. *)
    (* Compute (dl_nsimp d2 150). *)
    
  End TestV3_any_dim.

End Simplify_by_RAST.





