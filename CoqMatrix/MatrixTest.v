(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Test for matrix.
  author    : ZhengPu Shi
  date      : 2021.12
 *)

From FCS Require Export MatrixAll.


Module Test_Mat_R_MLL.
  Import MatrixAllR.MLL.
  Open Scope R.

  Check T.
  Check 3 : T.
  
  Parameter m1 : mat 3 4.
  Parameter m2 : mat 3 4.
  Check m1 == m2.
  
  (* build concrete matrix *)
  Definition ex_m_1_1 : mat 1 1 := mat_1_1 2.
  Definition ex_m_3_3 : mat 3 3 := mat_3_3 1 2 3 4 5 6 7 8 9.
  Compute ex_m_1_1.
  Compute ex_m_3_3.
  
  (* zero matrix, identity matrix *)
  Compute mat0 3 4.
  Compute mat1 3.
  
  (* matrix mapping *)
  Compute mmap (fun x => x * 2) (ex_m_3_3).
  Compute mmap2 (Rminus) ex_m_3_3 ex_m_3_3.
  
  (* matrix addition *)
  Check madd m1 m2.
  Compute madd ex_m_3_3 ex_m_3_3.
  Example ex_madd : forall r c (m1 m2 : mat r c), madd m1 m2 == madd m2 m1.
  intros. apply madd_comm. Qed.
  
  (* matrix subtraction *)
  Compute msub ex_m_3_3 (mat1 3).
  
  (* matrix scalar multiplication *)
  Compute mcmul 3 ex_m_3_3.
  Compute mmulc ex_m_3_3 3.
  
  (* matrix transpose *)
  Compute mtrans ex_m_3_3.
  
  (* matrix multiplication *)
  Compute mmul ex_m_3_3 (mtrans ex_m_3_3).
  Compute mmul ex_m_3_3 ex_m_3_3.

  (* Example for coordinate transform *)
  
  (*   Import List.
  Import ListNotations. *)
  
  Section coordinate_transform_test.
    Variable θ ψ φ : R.
    Definition Rx (α : R) : mat 3 3 :=
      mat_3_3
        1         0           0
        0         (cos α)     (sin α)
        0         (-sin α)    (cos α).

    Definition Ry (β : R) : mat 3 3 :=
      mat_3_3
        (cos β)   0           (-sin β)
        0         1           0
        (sin β)   0           (cos β).

    Definition Rz (γ : R) : mat 3 3 :=
      mat_3_3 
        (cos γ)   (sin γ)   0
        (-sin γ)  (cos γ)   0
        0         0         1.
    
    Definition R_b_e_direct : mat 3 3 :=
      mat_3_3
        (cos θ * cos ψ) 
        (cos ψ * sin θ * sin φ - sin ψ * cos φ)
        (cos ψ * sin θ * cos φ + sin φ * sin ψ)
        
        (cos θ * sin ψ) 
        (sin ψ * sin θ * sin φ + cos ψ * cos φ)
        (sin ψ * sin θ * cos φ - cos ψ * sin φ)
        
        (-sin θ)
        (sin φ * cos θ)
        (cos φ * cos θ).
    
    Open Scope M.
    Opaque cos sin.
    
    Lemma Rx_Ry_Rz_eq_Rbe : (Rz ψ)⊤ × (Ry θ)⊤ × (Rx φ)⊤ == R_b_e_direct.
    Proof.
      lma.
    Qed.
    
  End coordinate_transform_test.
  
End Test_Mat_R_MLL.
