(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : Vector theory following a textbook
  author      : ZhengPu Shi
  date        : 2022.05
  
  remark      :
  1. reference book : Vector Calculus, Michael Corral
  
    ch1, Vectors in Euclidean Space
      1.1 Vector Algebra
      1.2 Dot Product
      1.3 Cross Product
      1.4 Lines and Planes
      1.5 Surfaces
      1.6 Curvilinear Coordinates
      1.7 Vector-Valued Functions
      1.8 Arc Length
    
*)


Require Export Block.

        

(* ######################################################################### *)
(** * 1.1 Introduction *)
Module Sec_1_1_Introduction.
  
  (* ======================================================================= *)
  (** ** Def 1.1 *)
  (* 
    (1). A (nonzero) vector is a directed line segment from a point P to 
    a point Q.
    (2). Its magnitude is the length of the line segment.
    (3). Its direction is the the same as that of the directed line segment. 
    (4). The zero vector is just a point, and it is denoted by 0. *)
  Section Def_1_1.
    
    (** Definitions *)
    Section Defs.
      
      Variable A : Type.
      Variable A0 : A.
      Variable n : nat.
      
      Definition point := @Block A n.
      
      (** vector is a pair of two points.
        Although, this definition is no problem, but zero vector is special and 
        it have no well-defined direction, lots of opinion:
        (1) someone say that zero vector have arbitrary direction,
        (2) some say that it has indeterminate direction (i.e., the direction 
          can not be determined), 
        (3) while others say that it has no direction.
        
        Our definition of the zero vector, does not require a direction, we 
        will leave it at that.
        When in the subject of linear algebra there is a more abstract way of 
        definint a vector where the concept of "direction" is not really used.
        
        So, we use a restricted subset which exclude the zero vector for good 
        mathematical properties, so that the [vector] type.
        
        We use [vector_raw] to means a original vector, and [vector] to means a 
        restricted type of [vector_raw] which exclude zero vector.
        
        Some conventions:
        1. use "vraw**" to represent functions about vector.
        2. use "v**" to represent functions about nonzero vector.
      *)
      
      (** vector_raw is original definition of vector *)
      Definition vector_raw := (point * point)%type.
      
      (** Get magnitude of a vector. *)
      Parameter vraw_mag : forall (v : vector_raw), A.
      
      (** Get direction of a vector. *)
      Parameter vraw_dir : forall (v : vector_raw), A.
      
      (** Create a zero vector *)
      Definition vraw_zero (p : point) : vector_raw := (p, p).
      
      (** Proposition that v is a nonzero vector *)
      Definition vraw_is_nonzero (v : vector_raw) : Prop := 
        let (p1, p2) := v in (p1 <> p2).
      
      (** Assert that magnitude of a zero vector is 0 *)
      Axiom vraw_zero_imply_mag_zero: forall p, vraw_mag (vraw_zero p) = A0.
      
      
      (** A subset of nonzero vectors produced by excluding zero vectors, short 
        as vector. *)
      Record vector := mk_vector {
        vdata : vector_raw;
        vcond : vraw_is_nonzero vdata
      }.
      
      (** Get magnitude of a nonzero vector. *)
      Definition vmag v := vraw_mag (vdata v).

      (** Get direction of a nonzero vector. *)
      Definition vdir v := vraw_dir (vdata v).
    
    End Defs.
  
    Global Arguments point {A n}.
    
    Global Arguments vector_raw {A n}.
    Global Arguments vraw_mag {A n}.
    Global Arguments vraw_dir {A n}.
    Global Arguments vraw_zero {A n}.
    
    Global Arguments vector {A n}.
    Global Arguments mk_vector {A n}.
    
    Global Arguments vmag {A n}.
    Global Arguments vdir {A n}.
  
    
    (** test or applications *)
    Section test.
      
      (** Examples in one dimension *)
      Section One_dimension.
        
        (** assume the coordinates of P and Q *)
        Variable Px Qx : nat.
        
        (** define two points *)
        Let P : point := [Px].
        Let Q : point := [Qx].
        
        (** assume P and Q have different coordinates *)
        Variable P_Q_coord_diff : Px <> Qx.
        
        (** It follows that P and Q are not the same point *)
        Let P_neq_Q : P <> Q.
        Proof. intro. inversion H. auto. Qed.
        
        (** define a vector from P to Q *)
        Let vecPQ : vector := mk_vector (P,Q) P_neq_Q.
      
      End One_dimension.
      
      
      (** Examples in two dimensions *)
      Section Two_dimensions.
        
        (** assume the coordinates of P and Q *)
        Variable Px Qx Py Qy : nat.
        
        (** define two points *)
        Let P : point := [Px;Py].
        Let Q : point := [Qx;Qy].
        
        (** assume P and Q have different coordinates *)
        Variable P_Q_coord_diff : Px <> Qx \/ Py <> Qy.
        
        (** It follows that P and Q are not the same point *)
        Let P_neq_Q : P <> Q.
        Proof. intro. inversion H. destruct P_Q_coord_diff; auto. Qed.
        
        (** define a vector from P to Q *)
        Let vecPQ : vector := mk_vector (P,Q) P_neq_Q.
      
      End Two_dimensions.
      
      
      (** Examples in three dimensions *)
      Section Three_dimensions.
        
        (** assume the coordinates of P and Q *)
        Variable Px Qx Py Qy Pz Qz : nat.
        
        (** define two points *)
        Let P : point := [Px;Py;Pz].
        Let Q : point := [Qx;Qy;Qz].
        
        (** assume P and Q have different coordinates *)
        Variable P_Q_coord_diff : Px <> Qx \/ Py <> Qy \/ Pz <> Qz.
        
        (** It follows that P and Q are not the same point *)
        Let P_neq_Q : P <> Q.
        Proof. intro. inversion H. destruct P_Q_coord_diff; auto.
          destruct H0; auto. Qed.
        
        (** define a vector from P to Q *)
        Let vecPQ : vector := mk_vector (P,Q) P_neq_Q.
        Compute vecPQ.
      End Three_dimensions.
    
    End test.
    
  End Def_1_1.
  
  (* ======================================================================= *)
  (** ** Def 1.2 *)
  (*
    (1). Two nonzero vectors are equal if they have the same magnitude and the 
    same direction.
    (2). Any vector with zero magnitude is equal to the zero vector.
  *)
  Section Def_1_2.
    
    (** Definitions *)
    Section Defs.
    
      Variable A : Type.
      Variable A0 : A.
      Variable n : nat.
      
      Variable v1 v2 : @vector A n.
      
      Definition veq (v1 v2 : @vector A n) := 
        vmag v1 = vmag v2 /\ vdir v1 = vdir v2.
      
      Axiom vraw_mag_zero_imply_eq_vzero : forall (v : @vector_raw A n) 
        (p : point),
        vraw_mag v = A0 -> v = vraw_zero p.
      
    End Defs.
    
    
    (** test or applications *)
    Section test.
      
      Import QArith.
      
      (** define a vector u *)
      Let u_p0 : point := [1;3].
      Let u_p1 : point := [3;4].
      Let u : @vector Q 2.
        refine(mk_vector (u_p0,u_p1) _); intro H; inversion H.
      Defined.
      
      (** define a vector v *)
      Let v_p0 : point := [3;3].
      Let v_p1 : point := [1;2].
      Let v : @vector Q 2.
        refine(mk_vector (v_p0,v_p1) _); intro H; inversion H.
      Defined.
      
      (** define a vector w *)
      Let w_p0 : point := [0;0].
      Let w_p1 : point := [2;1].
      Let w : @vector Q 2.
        refine(mk_vector (w_p0,w_p1) _); intro H; inversion H.
      Defined.
      
      (** todo: we will finish this example later. *)
      
      (** the vectors u,v and w all have the same magnitude sqrt(5) *)
      Compute vmag u.
      
      (** u and w are parallel, since they lie on lines having the same slope 
        1/2, and point the same direction, so u = w, even though they have 
        different initial points *)
      
      (** v is parallel to u but points in the opposite direction, So u <> v *)
    
    End test.
    
    
  End Def_1_2.
  
End Sec_1_1_Introduction.




(* ######################################################################### *)
(** * 1.2 Vector Algebra *)
Module Sec_1_2_VectorAlgebra.
  
  (* ======================================================================= *)
  (** ** Def 1.3 *)
  (** A scalar is a quantity that can be represented by a single number. *)
  
  (** For our purposes, scalars will always be real numbers *)
  



End Sec_1_2_VectorAlgebra.


