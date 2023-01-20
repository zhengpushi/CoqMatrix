(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : AST for R.
  author    : ZhengPu Shi
  date      : 2022.08
  
  remark    :
  1. Why this module?
     In the inversion of symbol matrix, there are many redundant expressions such
     as "0 + 1 * a + b * 1 + 0", and it should be simplified to friendly "a + b".
     Althouth the former expression is equal to later, we still want to get the later.
     One way to do this job is using Abstract Syntax Tree (AST).
  2. motivation
     To simplify the expressions of symbol matrix with real number, we use AST to
     manipulate the expressions.
  3. How to do it?
     A simple encapsulate of usual operations of R.
     This is a light-weight AST for R, and the main type is named to "T"
  4. Thanks to...
     it is inspired by Marisa Kirisame<lolisa@marisa.moe>.
*)


Require Export BasicConfig.

Require Export RExt.
Require Import String.


(* ######################################################################### *)
(** * AST for R *)

(** Syntax of the AST *)
Inductive A :=
| A0 | A1
| ALit (r : R)
| Aadd (r1 r2 : A) | Aopp (r : A)
| Amul (r1 r2 : A) | Ainv (r : A)
| Afunc (f : string) (args : list A).

(** Simplify expression with R type *)
Global Hint Rewrite
  Rplus_0_l  (* 0 + r = r *)
  Rplus_0_r  (* r + 0 = r *)
  Rmult_0_l  (* 0 * r = 0 *)
  Rmult_0_r  (* r * 0 = 0 *)
  Rmult_1_l  (* 1 * r = r *)
  Rmult_1_r  (* r * 1 = r *)
.

(** New scope *)
Declare Scope A_scope.
Delimit Scope A_scope with A.
Open Scope A_scope.

Bind Scope A_scope with A.

(** Subtraction *)
Definition Asub a b := Aadd a (Aopp b).

(** Division *)
Definition Adiv a b := Amul a (Ainv b).

Notation "0" := A0 : A_scope.
Notation "1" := A1 : A_scope.
Infix "+" := Aadd : A_scope.
Infix "-" := Asub : A_scope.
Infix "*" := Amul : A_scope.
Infix "/" := Adiv : A_scope.
Notation "- a" := (Aopp a) : A_scope.
Notation "/ a" := (Ainv a) : A_scope.

(* Assumped rules for operations of A *)
Axiom Aadd_0_l : forall x, 0 + x = x.
Axiom Aadd_comm : forall x y, x + y = y + x.
Axiom Aadd_assoc : forall x y z, x + (y + z) = (x + y) + z.
Axiom Amul_1_l : forall x, 1 * x = x.
Axiom Amul_comm : forall x y, x * y = y * x.
Axiom Amul_assoc : forall x y z, x * (y * z) = (x * y) * z.
Axiom Adistr_l : forall x y z, (x + y) * z = x * z + y * z.
Axiom Aopp_def : forall x, x + (- x) = 0.
Axiom Ainv_l : forall x, x <> 0 -> (/ x) * x = 1.

(** We get a ring structure *)
Definition A_ring : ring_theory A0 A1 Aadd Amul Asub Aopp eq.
  constructor; auto.
  apply Aadd_0_l. apply Aadd_comm. apply Aadd_assoc.
  apply Amul_1_l. apply Amul_comm. apply Amul_assoc.
  apply Adistr_l. apply Aopp_def.
Defined.

Add Ring Ring_thy_inst : A_ring.

(** We get a field structure *)
Definition A_field : field_theory A0 A1 Aadd Amul Asub Aopp Adiv Ainv eq.
  constructor; auto.
  apply A_ring. intro. easy.
  apply Ainv_l.
Defined.

Add Field Field_thy_inst : A_field.

(** Semantic of the AST *)
Fixpoint A2R (t : A) : R :=
  match t with
  | 0 => R0 | 1 => R1 | ALit r => r
  | t1 + t2 => Rplus (A2R t1) (A2R t2) | Aopp t => Ropp (A2R t)
  | t1 * t2 => Rmult (A2R t1) (A2R t2) | Ainv t => Rinv (A2R t)
  | Afunc f args => match f with
    | _ => R0
    end
  end.

(** Simplify an expression *)
Fixpoint simp (t : A) : A :=
  match t with
  | 0 + x => x 
  | x + 0 => x
  | a + (b + c) => a + b + c
  | a + b => (simp a) + (simp b)
  | - 0 => 0
  | - - a => a
  | - (a + b) => - a + - b
  | - (a * b) => (-a) * b
  | - x => - (simp x)
  | 0 * _ => 0
  | _ * 0 => 0
  | 1 * x => x
  | x * 1 => x
  | (- (1)) * x => (-x)
  | x * (- (1)) => (-x)
  | a * (b + c) => (a * b) + (a * c)
  | (a + b) * c => (a * c) + (b * c)
  | a * (b * c) => a * b * c
  | a * b => (simp a) * (simp b)
  | / 1 => 1
  | / (a * b) => /a * /b
  | / x => / (simp x)
  | 0 => 0
  | 1 => 1
  | ALit _ => t
  | Afunc _ _ => t
  (* | _ => t *)
  end.

(** Multi-step simplification *)
Fixpoint nsimp (t : A) (n : nat) : A :=
  match n with
  | O => t
  | S n' => nsimp (simp t) n'
  end.


Section test.

  (* test of simp *)
  Let ex1 := 1 * 1 * (0 + 0).
  (* Compute simp ex1. *)
  (* Compute nsimp ex1 3. *)

  Let ex2 := 1 * 1 + 1 + (0 + 0 + 0).
  (* Compute simp ex2. *)
  (* Compute nsimp ex2 6. *)
  
  (* test of A2R *)
  Let f (t : A) : A := 1 * 1 * (t + 0 + 0).
  (* Compute f A0. *)
  (* Compute A2R (f A0). *)
  (* Compute A2R (nsimp (f A0) 5). *)

  (* test for simp + A2R *)
  Variable r11 r12 r13 r21 r22 r23 r31 r32 r33 : R.
  Let a11 := ALit r11. Let a12 := ALit r12. Let a13 := ALit r13.
  Let a21 := ALit r21. Let a22 := ALit r22. Let a23 := ALit r23.
  Let a31 := ALit r31. Let a32 := ALit r32. Let a33 := ALit r33.
  
  Let t1 := / (a11 * a12 + - a12 * a21) * -(1) * a12.
  (* Eval cbv in (A2R (nsimp t1 0)). *)
  (* Eval cbv in (A2R (nsimp t1 1)). *)
  (* Eval cbv in (A2R (nsimp t1 2)). *)
  
End test.

(** Aeq is decidable *)
Theorem Aeqdec : forall t1 t2 : A, {t1 = t2} + {t1 <> t2}.
Proof.
  induction t1; induction t2; auto;
  try (left; easy); try (right; easy).
  - destruct (Req_EM_T r r0); subst; auto. right. intro. inversion H. auto.
  - destruct (IHt1_1 t2_1),(IHt1_2 t2_2); subst; auto.
    + right. intro. inversion H. easy.
    + right. intro. inversion H. easy.
    + right. intro. inversion H. easy.
  - destruct (IHt1 t2); subst; auto. right. intro H; inversion H. easy.
  - destruct (IHt1_1 t2_1),(IHt1_2 t2_2); subst; auto.
    + right. intro. inversion H. easy.
    + right. intro. inversion H. easy.
    + right. intro. inversion H. easy.
  - destruct (IHt1 t2); subst; auto. right. intro H; inversion H. easy.
  - destruct (string_dec f f0); subst; auto.
    2:{ right. intro. inversion H. easy. }
    { assert ({args = args0} + {args <> args0}).
      2:{ destruct H; subst; auto. right. intro H; inversion H; auto. }
      apply List.list_eq_dec.
      (* Why lost this assupmption ? *)
Admitted.

Open Scope R.

(** simp keep the symantic *)
Theorem simp_ok : forall (t : A), A2R (simp t) = A2R t.
Proof.
(*   induction t; auto.
  - simpl. destruct (Aeqdec t1 0), (Aeqdec t2 0).
    + subst. simpl. ring.
    + subst. simpl. ring.
    + subst.
      replace (match t1 with 0 => 0 | _ => t1 end)%A with t1.
      * simpl. ring.
      * destruct t1; auto.
    + replace (match t2 with 0 => t1 | b + c => t1 + b + c | 
        _ => simp t1 + simp t2 end)%A
      with (match t2 with b + c => t1 + b + c | 
        _ => simp t1 + simp t2 end)%A.
      * replace (match t1 with 0 => t2 | _ => simp t1 + simp t2 end)%A
        with (simp t1 + simp t2)%A.
        { simpl. rewrite IHt1, IHt2. auto. }
        { destruct t1; auto. easy. }
      * destruct t2; auto. easy.
  - simpl. destruct (Aeqdec t 0); subst; simpl; try ring.
    replace (match t with 0 => 0 | _ => - simp t end)%A with (- simp t)%A.
    + simpl. rewrite IHt. auto.
    + destruct t; auto. easy.
  - simpl. destruct (Aeqdec t1 0), (Aeqdec t2 0).
    + subst. simpl. ring.
    + subst. simpl. ring.
    + subst. destruct t1; simpl; try ring.
    + destruct (Aeqdec t1 1); subst; auto.
      * replace (match t2 with 0 => 0 | _ => t2 end)%A with t2.
        simpl; try ring. destruct t2; auto.
      * destruct (Aeqdec t2 1); subst.
        { replace (match t1 with 0 => 0 | 1 => 1 | _ => t1 end)%A with t1.
          simpl; ring. destruct t1; auto. }
        { replace (match t2 with 0 => 0 | _ => t2 end)%A with t2.
          { replace (match t2 with 0=>0 | 1=>t1 | _=> simp t1 * simp t2
            end)%A with (simp t1 * simp t2)%A.
            { replace (match t1 with 0=>0 | 1=>t2 | _=> simp t1 * simp t2
              end)%A with (simp t1 * simp t2)%A.
              { simpl; rewrite IHt1,IHt2. auto. }
              { destruct t1; auto; try easy. } }
            { destruct t2; auto; try easy. } }
          { destruct t2; auto. }}
  - simpl. destruct (Aeqdec t 0); subst; simpl; try ring.
    destruct (Aeqdec t 1); subst. simpl. field.
    replace (match t with 1 => 1 | _ => / simp t end)%A with (/ simp t)%A.
    + simpl. rewrite IHt. auto.
    + destruct t; auto. easy.
Qed. *)
Admitted.


(** nsimp keep the symantic *)
Theorem nsimp_ok : forall (n : nat) (t : A), A2R (nsimp t n) = A2R t.
Proof.
  induction n; auto. simpl. intros. rewrite IHn. apply simp_ok.
Qed.

(** Boolean equality can be derived from T2R and Req_dec *)
Definition Aeqb (t1 t2 : A) : bool :=
  let r1 := A2R t1 in
  let r2 := A2R t2 in
    if Req_EM_T r1 r2 then true else false.

Infix     "=?"          := Aeqb           : A_scope.

