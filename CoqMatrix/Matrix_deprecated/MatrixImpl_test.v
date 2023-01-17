(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : test for Matrix implemented with Function
  author    : ZhengPu Shi
  date      : 2021.12
*)


From FCS Require Import RingType.
From FCS Require Import RingTypeZ.
From FCS Require Import RingTypeR.
From FCS Require Import MatrixSig.

From FCS Require Export Function.MatrixImpl.


(** * 整数域矩阵的测试 *)
Module Test_for_ModuleZ.
  
  (** Initialized matrix functor to concrete module *)
  Module MatrixZ := MatrixImpl RingTypeZ.
  Import MatrixZ.
  
  (* 控制作用域优先级 *)
  Open Scope nat_scope.
  Open Scope Z_scope.
  Open Scope matrix_scope.
  
  (* ################################################################# *)
  (** * 对一个数列求和，将来用于矩阵乘法等运算 *)

  (* 定义求和运算 *)
  Compute Tsum (fun x => Z.of_nat x) 4. (* 0 + 1 + 2 + 3 = 6 *)


  (** 求和再点积的一个等式，将来可能能用于矩阵乘法 *)
  (*
    (1 + 2 + 3) * (4 + 5) =
    m = 3, n = 2, m * n = 6
    
    x   x/n   x%n   f(x/n)  f(x%n)  f(x/n)*f(x%n)
    0   0     0     1       4       1*4
    1   0     1     1       5       1*5
    2   1     0     2       4       2*4
    3   1     1     2       5       2*5
    4   2     0     3       4       3*4
    5   2     1     3       5       3*5
    所以，新的求和序列是
    = 1*4 + 1*5 + 2*4 + 2*5 + 3*4 + 3*5
    非常巧妙！
  *)

  Section Tsum_product.
    (* 1,2,3 ... *)
    Local Definition f := fun (x : nat) => Z.of_nat (S x).
    (* 4,5 ... *)
    Local Definition g := fun (x : nat) => Z.of_nat (4 + x).
    
    Compute Tsum f 3.   (* 1 + 2 + 3 = 6 *)
    Compute Tsum g 2.   (* 4 + 5 = 9 *)
    
    Local Definition m : nat := 3.
    Local Definition n : nat := 2.
    
    Check Tsum f m * Tsum g n.
    Check Tsum (fun x => f (x / n)%nat * g (x mod n)%nat) (m * n). 

    Compute Tsum f m * Tsum g n.
    Compute Tsum (fun x => f (x / n)%nat * g (x mod n)%nat) (m * n). 

  End Tsum_product.


  (** Convert between Lists and Vectors / Matrices *)

  Module Cvt_List_Vec_Mat_test.
    Example lst1 := [1;2;3].
    Example lst2 := [4;5;6].
    Example v1 : Vector 3 := l2V lst1.
    Example v2 : Vector 3 := l2V lst2.
    Example m1 : mat 3 3 := l2m [lst1;lst2].
    Compute v1.
    Compute m1 0%nat 0%nat.
    Compute m1 0%nat 2%nat.

    Compute MRow 0 m1.
    Compute MRow 1 m1.
    Compute MRow 2 m1.

    Compute MCol 0 m1.
    Compute MCol 1 m1.
    Compute MCol 2 m1.
    Compute MCol 3 m1.

    Compute V2l v1.
    Compute V2l v2.

    Compute m2l m1.
    
  End Cvt_List_Vec_Mat_test.

End Test_for_ModuleZ.


(** * 实数域矩阵的测试 *)
Module Test_for_ModuleR.

  (** Initialized matrix functor to concrete module *)
  Module MatrixR := MatrixImpl RingTypeR.
  Export MatrixR.

  (* 控制作用域优先级 *)
  Open Scope nat_scope.
  Open Scope R_scope.
  Open Scope matrix_scope.

  (** ** mat Automation *)

  Module matrix_calc_test.
    (* ref:
    https://en.wikipedia.org/wiki/Mat_(mathematics)#Basic_operations
    *)
    
    Definition m1 := @l2m 2 3 [[1;3;1];[1;0;0]].
    Definition m2 := @l2m 2 3 [[0;0;5];[7;5;0]].
    Definition m3 := @l2m 2 3 [[1;3;6];[8;5;0]].

    Example mplus_m1_m2_eq_m3 : m1 + m2 == m3. lma. Qed.
    
    Definition m4 := @l2m 2 3 [[1;8;-3];[4;-2;5]].
    Definition m5 := @l2m 2 3 [[2;16;-6];[8;-4;10]].

    Example mscale_2_m4_eq_m5 : 2 c* m4 == m5. lma. Qed.
    
    Definition m6 := @l2m 2 3 [[1;2;3];[0;-6;7]].
    Definition m7 := @l2m 2 3 [[1;0];[2;-6];[3;7]].
    Example mtrans_m6_eq_m7 : m6 ⊤ == m7. lma. Qed.
    
    Open Scope R.
    Parameter θ ψ φ : R.
    Definition Rx (α : R) : mat 3 3 := @l2m 3 3
      [[1;  0;        0      ];
       [0;  cos α;    sin α ];
       [0;  -sin α;   cos α ]].

    Definition Ry (β : R) : mat 3 3 := @l2m 3 3 
      [[cos β;  0;  -sin β];
       [0;      1;  0     ];
       [sin β;  0;  cos β ]].

    Definition Rz (γ : R) : mat 3 3 := @l2m 3 3 
      [[cos γ;    sin γ;  0];
       [-sin γ;   cos γ;  0];
       [0;        0;       1]].
    
    Definition R_b_e_direct : mat 3 3 := @l2m 3 3 [
      [cos θ * cos ψ; 
       cos ψ * sin θ * sin φ - sin ψ * cos φ;
       cos ψ * sin θ * cos φ + sin φ * sin ψ];
      [cos θ * sin ψ; 
       sin ψ * sin θ * sin φ + cos ψ * cos φ;
       sin ψ * sin θ * cos φ - cos ψ * sin φ];
      [-sin θ; sin φ * cos θ; cos φ * cos θ]
      ].
     
    Open Scope M.
    Opaque cos sin.
    Lemma Rx_Ry_Rz_eq_Rbe : (Rz ψ)⊤ × (Ry θ)⊤ × (Rx φ)⊤ == R_b_e_direct.
    Proof. lma. Qed.
    
  End matrix_calc_test.

End Test_for_ModuleR.
