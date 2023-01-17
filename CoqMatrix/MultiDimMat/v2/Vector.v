(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : Vector theory implemented on block structure
  author      : ZhengPu Shi
  date        : 2022.05
  
  remark      :
  1. reference book : Vector Calculus, Michael Corral
  
  2. Vectors in Euclidean Space
    (1). 1-,2-,3- and higher dimensional space
      a. in single-variable calculus, for such a function, y = f(x), the graph
        of the the function f consists of the points(x,y)=(x,f(x)). These 
        points lie in the Euclidean plane 
        Euclidean plane
      b. in vector (or multivariable) calculus, 
    (2). Point
    (3). Vector, from initial point to terminal point
      it's operations: magnitude, angle, dot product, cross porduct
    (4). Lines
    (5). Planes
    (6). Surfaces
   
  3. History
    (1). followed the textbook and developped a prototype in Vector_textbook.v
    (2). we reorganized the content and use functor to make a general 
      implementation.
*)


Require Export Block.
Require        Reals.     (* concrete numbers *)


(* ######################################################################### *)
(* * Abstract number for vector *)
Module Type Number.
  
  (** Base type of number *)
  Parameter A : Type.
  
  (** Zero and One *)
  Parameter A0 A1 : A.
  
  (** Addition of two numbers *)
  Parameter add : A -> A -> A.
  
  (** Opposite of a number *)
  Parameter opp : A -> A.
  
  (** Multiplication of two numbers *)
  Parameter mult : A -> A -> A.
  
  (** Sqrt of a number *)
  Parameter sqrt : A -> A.
  
  Infix "+" := add.
  Notation "- x" := (opp x).
  Infix "*" := mult.

End Number.


(* ######################################################################### *)
(** ** Concrete number over R *)
Module NumberR <: Number.
  
  Export Reals.
  Export Lra.

  Open Scope R.
  
  Definition A := R.
  Definition A0 := 0.
  Definition A1 := 1.
  Definition add := Rplus.
  Definition opp := Ropp.
  Definition mult := Rmult.
  Definition sqrt := sqrt.

End NumberR.



(* ######################################################################### *)
(* * Vector theory *)
Module VectorTheory (N : Number).

  (** Import base-number *)
  Export N.
  
  (** Subtraction *)
  Definition Nsub x y := x + (- y).
  Infix "-" := Nsub.
  
  (** Square *)
  Definition Nsqr x := x * x.
  
  
  (* ======================================================================= *)
  (** ** Point *)
  Section Point.
  
    Variable n : nat.
  
    (** Point is a n-dim block *)
    Definition point := @Block N.A n.
    
    (** Origin point *)
    Definition point_origin : point := bzero N.A0 n.
  
  End Point.

  Global Arguments point {n}.
  Global Arguments point_origin {n}.
  
  
  (* ======================================================================= *)
  (** ** Definition of vector *)
  Section VectorDef.
  
    (** Dimension of the vector space *)
    Variable n : nat.
    
    (** vector is a pair of two points. *)
    Definition vector := (@point n * @point n)%type.
    
    (** Get initial and terminal point of a vector *)
    Definition v_p0 (v : vector) := let (p0,p1) := v in p0.
    Definition v_p1 (v : vector) := let (p0,p1) := v in p1.
    
    (** Construct a vector with terminal point and assuming that origin point 
      is the initial point of the vector. *)
    Definition v_by_terminal (p : @point n) : vector := 
      (point_origin, p).
    
    
    (** Proposition that v is a zero vector *)
    Definition v_is_zero (v : vector) : Prop := 
      let (p1, p2) := v in (p1 = p2).
      
    (** Proposition that v is a nonzero vector *)
    Definition v_is_nonzero (v : vector) : Prop := 
      let (p1, p2) := v in (p1 <> p2).
    
    (** Create a zero vector *)
    
    (* old definition need a point *)
    Definition vzero' (p : @point n) : vector := (p, p).
    
    (* new definition use default origin point *)
    Definition vzero : vector := (point_origin, point_origin).
    
  End VectorDef.
  
  Global Arguments vector {n}.
  Global Arguments v_is_zero {n}.
  Global Arguments v_is_nonzero {n}.
  Global Arguments vzero {n}.
  
  
  (* ======================================================================= *)
  (** ** Basic operations of vector *)
  Section VectorBasicOp.
    
    (** Get distance of two points *)
    Definition distance {n} (p1 p2 : @point n) : N.A :=
      let 'mkBlock l1 H1 := p1 in
      let 'mkBlock l2 H2 := p2 in
      let dist x y := N.sqrt (Nsqr (x - y)) in
        fold_left N.add (map2 dist l1 l2) N.A0.
  
    (** Get magnitude of a vector. *)
    Definition vmag {n} (v : @vector n) : N.A :=
      let (p1,p2) := v in
        distance p1 p2.
    
    (** Get direction of a vector. *)
    Parameter vdir : forall {n} (v : @vector n), A.
    
    (** Assert that magnitude of a zero vector is 0 *)
    Lemma vmag0_imply_vzero : forall n (v : @vector n), 
      vmag v = A0 -> v_is_zero v.
    Proof.
      intros n [[l1 H1] [l2 H2]]. simpl. intros H. apply beq_iff; simpl.
      gd H. gd H2. gd H1. gd l2. gd l1. induction n; intros.
      - apply length_zero_iff_nil in H1,H2; subst; auto.
      - destruct l1 as [|x1 l1], l2 as [|x2 l2]; try easy.
        remember (fun x y : A => sqrt (Nsqr (x - y))) as f.
        simpl in *.
        Abort.
        
  End VectorBasicOp.
  
  Global Arguments distance {n}.
  Global Arguments vraw_mag {n}.
  Global Arguments vraw_by_terminal {n}.
  
  
  (* ======================================================================= *)
  (** ** Basic properties of vector *)
  Section VectorBasicProps.
    
  
  End VectorBasicProps.

End VectorTheory.



(* ######################################################################### *)
(* * Concrete vector theory *)
Module Vector.
  
  (* ======================================================================= *)
  (** ** Vector theory over R *)
  Module VectorR.
    
    (** Instantialize vector theory *)
    Module VectorTheoryR := VectorTheory (NumberR).
    Export VectorTheoryR.
    
    (** Add more functions and properties *)
    
    (** Decompose a point in R3 to three components *)
    Definition point_decomp_R3 (p : @point 3) : (R * R * R) :=
      match Bdata p with
      | [x;y;z] => (x,y,z)
      | _ => (R0,R0,R0)
      end.
    
    (** Th1.1, the distance d between points P and Q in R^3 is following. *)
    Theorem dist_R3 : forall (p1 p2 : @point 3), distance p1 p2 = 
      let '(x1,y1,z1) := point_decomp_R3 p1 in
      let '(x2,y2,z2) := point_decomp_R3 p2 in
        sqrt (Rsqr (x2-x1) + Rsqr (y2-y1) + Rsqr (z2-z1)).
    Admitted.
    
    (** Th1.2, the magnitude of v=(a,b,c) in R^3 is following. *)
    Theorem vmag_R3 : forall (v : @point 3),
      let '(a,b,c) := point_decomp_R3 v in
        vraw_mag (vraw_by_terminal v) =
        sqrt (Rsqr a + Rsqr b + Rsqr c).
    Proof.
      intros. destruct v as [l H].
      do 4 (destruct l as [|? l]; try easy). simpl.
      unfold add,Nsqr,A0,mult,sqrt,Nsub,add,opp.
      Admitted.
  End VectorR.
  
  (** Usage demo *)
  Section test.
    Import VectorR.
    Check [1;2] : point.
  End test.
End Vector.

Export Vector.
 


(* ######################################################################### *)
(* * Vector test over R *)
Module Vector_test_R.
  
  Import VectorR.
  
  (** vector v by a point P *)
  Section example_1_1.
  
    Let origin : point := [0;0;0].
    Let P : point := [3;4;5].
    Let v : @vector 3.
      refine (mkVector (origin,P) _). simpl. intro H; inversion H. lra.
      Defined.
    
    Goal distance [0;0] [2;1] = sqrt 5.
    clear. compute. destruct (Rcase_abs); try field; try lra.
    Abort.
    
  End example_1_1.

  (* does vec(PQ) = vec(RS) ? *)
  Section example_1_2.

    Let origin : point := [0;0;0].
    Let P : point := [2;1;5].
    Let Q : point := [3;5;7].
    Let PQ : @vector 3.
      refine (mkVector (P,Q) _). simpl. intro H; inversion H. lra. Qed.
    
    Let R : point := [1;-3;-2].
    Let S : point := [2;1;0].
    Let RS : @vector 3.
      refine (mkVector (R,S) _). simpl. intro H; inversion H. lra. Qed.
    
    (* we havn't defined the angle and equal of two vectors *)
(*     Goal PQ = RS. *)
    
  End example_1_2.
  
    
 (N : Number).




  
  
  End VectorBasicOp.
  
  Global Arguments vraw_mag {n}.
  Global Arguments vraw_dir {n}.
  Global Arguments vraw_zero {A n}.
  
  
  Global Arguments vmag {A n}.
  Global Arguments vdir {A n}.
    
  
  (* --------------------------------------------------------------------- *)
  (** *** Vector *)
  Section Vector.
  
  

    (* --------------------------------------------------------------------- *)
    (** *** test *)
    Section test.
      
      Let w0 := l2b [0;0].
      Let w1 := l2b [2;1].
      Compute magnitude w0 w1.
    
    End test.
    
  End AbstractOperations.
  
  
  (* ======================================================================= *)
  (** ** Concrete operations over Q *)
  Module OperationsQ.
    
    Module Operations := AbstractOperations (NumberQ).
    Export Operations.
    

    
  
  End OperationsQ.
  
  
  (* ======================================================================= *)
  (** ** Concrete operations over R *)
  Module OperationsR.
    
    Module Operations := AbstractOperations (NumberR).
    Export Operations.
    
    (* --------------------------------------------------------------------- *)
    (** *** test *)
    Section test.
      
      Let w0 := l2b [0;0].
      Let w1 := l2b [2;1].
      Compute magnitude w0 w1.
    
    End test.
  
  End OperationsR.
  

End LinearAlgebraOperations.

Export LinearAlgebraOperations.
        

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
  Module Def_1_1 (N : AbstractNumber).
  
  Definition A := N.A.
  
  End Def_1_1.
  
  Print Def_1_1.
  
  Module AA : Def_1_1.
    Module N := NumberQ.
  
  End AA.
  
   (N : AbstractNumber).
    
    (** Definitions *)
    Section Defs.

      Variable n : nat.
      
      Definition point := @Block N.A n.
      
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
      Definition vraw_mag : forall (v : vector_raw), A.
      
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


