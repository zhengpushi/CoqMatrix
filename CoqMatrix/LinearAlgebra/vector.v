(*
  Copyright 2023 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Chapter 1, Introduction to Vectors
  author    : ZhengPu Shi
  date      : 2023.03
  
  remark    :
  1. reference: Introduction to Linear Algebra, by Gilbert Strang
 *)


(** There is no implementation of sqrt, thus vlen cannot be defined. *)
(* Require Import VectorQ. *)

Require Import VectorR.


(** Set initial scope *)
Open Scope nat_scope.
(* Open Scope Q_scope. *)
Open Scope R_scope.
Open Scope mat_scope.
Open Scope vec_scope.

(** ** 1.1 Vectors and Linear Combination  *)
Section sec_1_1.

  (** Linear Combination of: c * v + d * w *)
  Definition lc {n : nat} (v w : vec n) (c d : A) := c c* v + d c* w.

  (* Example  *)
  Let v := mk_vec2 1 1.
  Let w := mk_vec2 2 3.
  
  Goal lc v w 1 1 == mk_vec2 3 4.
  Proof. lma. Qed.
  
  Goal lc v w 2 1 == mk_vec2 4 5.
  Proof. lma. Qed.

  Goal lc v w 3 5 == mk_vec2 13 18.
  Proof. lma. Qed.

  (** Verify these special linear combinations: *)
  Section special_linear_combinations.

    (* 1v + 1w = v + w *)
    Lemma lc_eq_add : forall {n} (v w : vec n), lc v w 1 1 == v + w.
    Proof. lma. Qed.
    
    (* 1v - 1w = v - w *)
    Lemma lc_eq_sub : forall {n} (v w : vec n), lc v w 1 (-1) == v - w.
    Proof. lma. Qed.
    
    (* 0v + 0w = 0 *)
    Lemma lc_eq_zero : forall {n} (v w : vec n), lc v w 0 0 == vec0.
    Proof. lma. Qed.
    
    (* cv + 0w = c.v *)
    Lemma lc_eq_scal : forall {n} (v w : vec n) (c : A), lc v w c 0 == c c* v.
    Proof. lma. Qed.

  End special_linear_combinations.

  (** Example for 3D vector *)
  Goal let v := mk_vec3 1 1 (-1) in
       let w := mk_vec3 2 3 4 in
       lc v w 1 1 == mk_vec3 3 4 3.
  Proof. lma. Qed.

  (** Linear combination of several vectors (more than 2) *)
  Reset lc.

  Definition lc {n : nat} (l : list (A * (vec n))%type) :=
    let l' := map (fun x : A * vec n => let (c,v) := x in c c* v) l in
    fold_left vadd l' vec0.

  (** Example in page 5 *)
  Goal let u := mk_vec3 1 0 3 in
       let v := mk_vec3 1 2 1 in
       let w := mk_vec3 2 3 (-1) in
       lc [(1,u);(4,v);(-2,w)] == mk_vec3 1 2 9.
  Proof. lma. Qed.
  
End sec_1_1.


(** ** 1.2 Lengths and Dot Products *)
Section sec_1_2.

  Infix "⋅" := vdot : vec_scope.
  Notation "v| v |" := (vlen v) : vec_scope.

  (** A vector is a unit vector *)
  Section vunit.

    (** unit vector in xy plane *)
    Let i := mk_vec2 1 0.
    Let j := mk_vec2 0 1.

    (** make an angle "theta" with the x axis *)
    Let u θ := mk_vec2 (cos θ) (sin θ).
    
    (** if theta = 0, then u is i *)
    Goal u 0 == i.
    Proof. lma; cbv; ra. Qed.
    
    (** if theta = 90 degree (π/2), then u is j *)
    Goal u (PI/2) == j.
    Proof. lma; cbv; ra. Qed.

    (** at any angle, u is a unit vector *)
    Goal forall θ, vunit (u θ).
    Proof. intros. cbv. autorewrite with R. auto. Qed.

  End vunit.

  (** Convert any non-zero vector to a unit vector *)
  Section vnormalize.

    Let u := mk_vec3 2 2 1.

    (** length of us is 3 *)
    Let len_of_u : v| u | = 3.
    Proof. cbv. solve_sqrt_eq. Qed.

    (** normalize u to unit vector *)
    Goal vnormalize u == mk_vec3 (2/3) (2/3) (1/3).
    Proof. lma. all: rewrite len_of_u; cbv; ra. Qed.

  End vnormalize.

  
  (** The angle between two vectors *)
  Section angle.

    (** Angle of two vectors *)
    Parameter angle_of_vec : forall {n} (u v : vec n), R.
    Infix "∠" := angle_of_vec (at level 70) : vec_scope.

    (** Two vectors are perpendicular *)
    Section perp.
      
      (** Two vectors u and w are perpendicular *)
      Definition perpendicular {n} (u v : vec n) : Prop := u ∠ v = PI/2.
      Infix "⟂" := perpendicular (at level 70) : vec_scope.

      (** Pythagoras Law. *)
      Axiom PythagorasLaw2D : forall (a b : vec 2),
          let c := a - b in
          a ⟂ b <-> (Rsqr (v|a|) + Rsqr (v|b|))%A = Rsqr (v|c|).

      (** v ⟂ w, iff v ⋅ w = 0 *)
      Lemma perpendicular_iff_dot0_2D : forall (u v : vec 2), u ⟂ v <-> u ⋅ v = 0.
      Proof.
        intros. split; intros H.
        - apply PythagorasLaw2D in H.
          destruct u as [u], v as [v]. cbv in *.
          ring_simplify in H. autorewrite with R in *.
          rewrite ?Rsqr_sqrt in H; ra.
        - apply PythagorasLaw2D.
          destruct u as [u], v as [v]. cbv in *.
          ring_simplify. autorewrite with R in *.
          rewrite ?Rsqr_sqrt; ra.
      Qed.
    End perp.

    (** The angle of two unit vectors *)
    Section angle_vunit.
      
      (** the cosine of angle of two unit vectors *)
      Axiom cosine_angle_of_vuint : forall {n} (u v : vec n),
          vunit u -> vunit v -> cos (u ∠ v) = u ⋅ v.

      (** if u = (cos θ, sin θ), i = (1,0), then u⋅i=cos θ.
        That is the cosine of the angle between them. *)

      (** after rotation through any angle α, their angle still is θ *)

    End angle_vunit.

    (** The angle of two vectors (needn't be unit vector) *)
    Section angle.

      (** the cosine of angle of two vectors *)
      Axiom cosine_angle_of_vec : forall {n} (u v : vec n),
          vnonzero u -> vnonzero v ->
          cos (u ∠ v) = (vnormalize u) ⋅ (vnormalize v).

      (** “Schwarz inequality” for dot products.
          more correctly, Cauchy-Schwarz-Buniakowsky inequality *)
      Lemma schwarz_ineq_vdot : forall {n} (v w : vec n), Rabs (v⋅w) <= v|v | * v|w|.
      Proof.
        intros.
        destruct (decidable v vec0), (decidable w vec0).
        - (* v = 0, w = 0 *)
          assert (v ⋅ w == 0)%A.
          { rewrite v0. rewrite vdot_0_l. easy. }
          rewrite H. autorewrite with R.
          ?
          hnf. ra.
            rewrite v1.
            rewrite v0.
          Set Printing All.
          
          rewrite v0.
          
          
        - (* v = 0, w <> 0 *)
        - (* v = 0, w <> 0 *)
        - (* v = 0, w <> 0 *)
          
        pose proof (cosine_angle_of_vec v w).
        assert (vnormalize v ⋅ vnormalize w
        unfold vnormalize in H.
        assert 
        s hnf in *.
        
      Admitted.

      (** Triangle inequality *)
      Lemma triangle_ineq : forall {n} (v w : vec n), v|v + w| <= v|v | + v|w|.
      Admitted.

      
    End angle.

    (** 

  End angle.

  

  

End sec_1_2.

