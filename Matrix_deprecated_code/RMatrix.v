(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix on Real numbers.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export Matrix RExt.

Open Scope R_scope.
Open Scope mat_scope.

(* ################################################################# *)
(** ** 由矩阵理论直接得到的 实数矩阵理论 *)

Definition mat r c := mat (A:=R) r c.

Definition mk_mat {r c} f : mat r c := mk_mat (A:=R) r c f.

Definition m2f {r c} (m : mat r c) := m2f m.

Definition f2m {r c} f : mat r c := f2m f.

Definition meq {r c} (m1 m2 : mat r c) := meq m1 m2.

Lemma meq_refl : forall {r c} (m : mat r c), m == m.
Proof. intros. apply meq_refl. Qed.

Lemma meq_sym : forall {r c} (m1 m2 : mat r c), m1 == m2 -> m2 == m1.
Proof. intros. apply meq_sym; auto. Qed.

Lemma meq_trans : forall {r c} (m1 m2 m3 : mat r c),
    m1 == m2 -> m2 == m3 -> m1 == m3.
Proof. intros. apply meq_trans with m2; auto. Qed.

Lemma meq_iff : forall {r c} (m1 m2 : mat r c),
  m1 == m2 <-> forall i j, (i < r)%nat -> (j < c)%nat -> m2f m1 i j = m2f m2 i j.
Proof. intros. apply meq_iff. Qed.

Lemma meq_dec : forall {r c} (m1 m2 : mat r c), {m1 == m2} + {~(m1 == m2)}.
Proof. intros. apply meq_dec. Qed.

Definition mnth {r c} (m : mat r c) i j := mnth m i j.

Definition mrow {r c} (m : mat r c) i := mrow i m.

Lemma mrow_length : forall {r c} (m : mat r c) i, length (mrow m i) = c.
Proof. intros. apply mrow_length. Qed.

Lemma mrow_nth : forall {r c} (m : mat r c) i j,
    (i < r)%nat -> (j < c)%nat -> nth j (mrow m i) 0 = m2f m i j.
Proof. intros. apply mrow_nth; auto. Qed.

Definition mcol {r c} (m : mat r c) j := mcol j m.

Lemma mcol_length : forall {r c} (m : mat r c) j, length (mcol m j) = r.
Proof. intros. apply mcol_length. Qed.

Lemma mcol_nth : forall {r c} (m : mat r c) i j,
    (i < r)%nat -> (j < c)%nat -> nth i (mcol m j) 0 = m2f m i j.
Proof. intros. apply mcol_nth; auto. Qed.

Definition l2m {r c} l : mat r c := l2m l (r:=r) (c:=c) (A0:=0).

Definition m2l {r c} (m : mat r c) := m2l m.

Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
Proof. intros. apply m2l_length. Qed.

Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
Proof. intros. apply m2l_width. Qed.

Lemma l2m_m2l_id : forall {r c} (m : mat r c), l2m (m2l m) == m.
Proof. intros. apply l2m_m2l_id. Qed.

Lemma m2l_l2m_id : forall {r c} l,
    length l = r -> width l c -> m2l (l2m l (r:=r) (c:=c)) = l.
Proof. intros. apply m2l_l2m_id; auto. Qed. 

Lemma l2m_inj : forall {r c} l1 l2,
    length l1 = r -> width l1 c -> length l2 = r -> width l2 c ->
    l1 <> l2 -> ~(l2m l1 (r:=r) (c:=c) == l2m l2).
Proof. intros. apply l2m_inj; auto. Qed.

Lemma m2l_inj : forall {r c} (m1 m2 : mat r c),
    ~(m1 == m2) -> m2l m1 <> m2l m2.
Proof. intros. apply m2l_inj; auto. Qed.

Definition mshiftc {r c} (m : mat r c) k : mat r c := mshiftc m k.

Lemma mshiftc_neq : exists r c (m1 m2 : mat r c) k,
    (m1 == m2) /\ (~(mshiftc m1 k == mshiftc m2 k)).
Proof. apply (mshiftc_neq (A1_neq_A0:=R1_neq_R0)). Qed.

Definition mk_mat_0_c c : mat 0 c := mk_mat_0_c c (A0:=0).

Definition mk_mat_1_1 a11 : mat 1 1 := mk_mat_1_1 (A0:=0) a11.

Definition mk_mat_1_2 a11 a12 : mat 1 2 :=
  mk_mat_1_2 (A0:=0) a11 a12.

Definition mk_mat_1_3 a11 a12 a13 : mat 1 3 :=
  mk_mat_1_3 (A0:=0) a11 a12 a13.

Definition mk_mat_1_4 a11 a12 a13 a14 : mat 1 4 :=
  mk_mat_1_4 (A0:=0) a11 a12 a13 a14.

Definition mk_mat_1_c c l : mat 1 c := mk_mat_1_c c l (A0:=0).

Definition mk_mat_2_1 a11 a21 : mat 2 1 :=
  mk_mat_2_1 (A0:=0) a11 a21.

Definition mk_mat_2_2 a11 a12 a21 a22 : mat 2 2 :=
  mk_mat_2_2 (A0:=0) a11 a12 a21 a22.

Definition mk_mat_3_1 a11 a21 a31 : mat 3 1 :=
  mk_mat_3_1 (A0:=0) a11 a21 a31.

Definition mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 : mat 3 3 :=
  mk_mat_3_3 (A0:=0) a11 a12 a13 a21 a22 a23 a31 a32 a33.

Definition mk_mat_4_1 a11 a21 a31 a41 : mat 4 1 :=
  mk_mat_4_1 (A0:=0) a11 a21 a31 a41.

Definition mk_mat_4_4 a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34
  a41 a42 a43 a44 : mat 4 4 :=
  mk_mat_4_4 (A0:=0) a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34
    a41 a42 a43 a44.

Definition mk_mat_r_0 r : mat r 0 := mk_mat_r_0 (A0:=0) r.

Definition mk_mat_r_1 r l : mat r 1 := mk_mat_r_1 (A0:=0) r l.

Definition mmap {r c} f (m : mat r c) : mat r c := mmap f m.

Definition mmap2 {r c} f (m1 m2 : mat r c) : mat r c := mmap2 f m1 m2.

Lemma mmap2_comm : forall {r c} (m1 m2 : mat r c) f,
    (forall a b, f a b = f b a) ->
    mmap2 f m1 m2 == mmap2 f m2 m1.
Proof. intros. apply mmap2_comm; auto. Qed.

Lemma mmap2_assoc : forall {r c} (m1 m2 m3 : mat r c) f,
    (forall a b c, f (f a b) c = f a (f b c)) ->
    mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
Proof. intros. apply mmap2_assoc; auto. Qed.

Definition mat0 r c : mat r c := mat0 r c (A0:=0).

Definition mat1 n : mat n n := mat1 n (A0:=0) (A1:=1).

Definition mdiag n l : mat n n := mdiag n l (A0:=0).

Definition madd {r c} (m1 m2 : mat r c) : mat r c := madd m1 m2 (op:=Rplus).
Global Infix "+" := madd : mat_scope.

Lemma madd_comm : forall {r c} (m1 m2 : mat r c), m1 + m2 == m2 + m1.
Proof. intros. apply madd_comm. Qed.

Lemma madd_assoc : forall {r c} (m1 m2 m3 : mat r c),
    (m1 + m2) + m3 == m1 + (m2 + m3).
Proof. intros. apply madd_assoc. Qed.

Lemma madd_0_l : forall {r c} (m : mat r c), (mat0 r c) + m == m.
Proof. intros. apply madd_0_l. Qed.

Lemma madd_0_r : forall {r c} (m : mat r c), m + (mat0 r c) == m.
Proof. intros. apply madd_0_r. Qed.

Lemma madd_nth : forall {r c} (m1 m2 : mat r c) i j,
    mnth (m1 + m2) i j = (mnth m1 i j + mnth m2 i j)%R.
Proof. intros. apply madd_nth. Qed.

Definition mopp {r c} (m : mat r c) : mat r c := mopp m (inv:=Ropp).
Global Notation "- m" := (mopp m) : mat_scope.

Definition msub {r c} (m1 m2 : mat r c) : mat r c :=
  msub m1 m2 (op:=Rplus) (inv:=Ropp).
Global Infix "-" := msub : mat_scope.

Lemma mopp_opp : forall {r c} (m : mat r c), --m == m.
Proof. intros. apply mopp_opp. Qed.

Lemma msub_comm : forall {r c} (m1 m2 : mat r c), m1 - m2 == - (m2 - m1).
Proof. intros. apply msub_comm. Qed. 

Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c),
    (m1 - m2) - m3 == m1 - (m2 + m3).
Proof. intros. apply msub_assoc. Qed.

Lemma msub_0_l : forall {r c} (m : mat r c), (mat0 r c) - m == - m.
Proof. intros. apply msub_0_l. Qed.

Lemma msub_0_r : forall {r c} (m : mat r c), m - (mat0 r c) == m.
Proof. intros. apply msub_0_r. Qed.

Lemma madd_opp : forall {r c} (m : mat r c), m + (-m) == mat0 r c.
Proof. intros. apply madd_opp. Qed.

Lemma msub_self : forall {r c} (m : mat r c), m - m == mat0 r c.
Proof. intros. apply msub_self. Qed. 

Definition mcmul {r c} a (m : mat r c) : mat r c := mcmul a m (mul0:=Rmult).
Global Infix "c*" := mcmul : mat_scope.

Definition mmulc {r c} (m : mat r c) a : mat r c := mmulc m a (mul0:=Rmult).
Global Infix "*c" := mmulc : mat_scope.

Lemma mmulc_eq_mcmul : forall {r c} a (m : mat r c), m *c a == a c* m.
Proof. intros. apply mmulc_eq_mcmul. Qed.

Lemma mcmul_0_l : forall {r c} (m : mat r c), 0 c* m == mat0 r c.
Proof. intros. apply mcmul_0_l. Qed.

Lemma mcmul_0_r : forall {r c} a, a c* (mat0 r c) == mat0 r c.
Proof. intros. apply mcmul_0_r. Qed.

Lemma mcmul_1_l : forall {r c} (m : mat r c), 1 c* m == m.
Proof. intros. apply mcmul_1_l. Qed.

Lemma mcmul_1_r : forall {n} a,
    a c* (mat1 n) == f2m (fun i j => if (i =? j)%nat then a else 0).
Proof. intros. apply mcmul_1_r. Qed.

Lemma mcmul_assoc : forall {r c} a b (m : mat r c),
    a c* (b c* m) == (a * b)%R c* m.
Proof. intros. apply mcmul_assoc. Qed.

Lemma mcmul_perm : forall {r c} a b (m : mat r c),
    a c* (b c* m) == b c* (a c* m).
Proof. intros. apply mcmul_perm. Qed.

Lemma mcmul_add_distr_l : forall {r c} a (m1 m2 : mat r c),
    a c* (m1 + m2) == a c* m1 + a c* m2.
Proof. intros. apply mcmul_add_distr_l. Qed.

Lemma mcmul_add_distr_r : forall {r c} a b (m : mat r c),
    (a + b)%R c* m == a c* m + b c* m.
Proof. intros. apply mcmul_add_distr_r. Qed.

Definition mtrans {r c} (m : mat r c) : mat c r := mtrans m.
Global Notation "m '''" := (mtrans m) (at level 30) : mat_scope.

Lemma mtrans_trans : forall {r c} (m : mat r c), m '' == m.
Proof. intros. apply mtrans_trans. Qed.

Lemma mat1_trans_eq : forall {n}, (mat1 n) ' == mat1 n.
Proof. intros. apply mat1_trans_eq. Qed.

Lemma mat0_trans_eq : forall {r c}, (mat0 r c) ' == mat0 c r.
Proof. intros. apply mat0_trans_eq. Qed.

Definition mmul {r c s} (m1 : mat r c) (m2 : mat c s) : mat r s :=
  mmul m1 m2 (add0:=Rplus) (zero0:=0) (mul0:=Rmult).
Global Infix "*" := mmul : mat_scope.

Lemma mmul_assoc : forall {r c s t} (m1 : mat r c) (m2 : mat c s) (m3 : mat s t),
    (m1 * m2) * m3 == m1 * (m2 * m3).
Proof. intros. apply mmul_assoc. Qed.

Lemma mmul_add_distr_l : forall {r c s} (m1 : mat r c) (m2 m3 : mat c s),
    m1 * (m2 + m3) == m1 * m2 + m1 * m3.
Proof. intros. apply mmul_add_distr_l. Qed.

Lemma mmul_add_distr_r : forall {r c s} (m1 m2 : mat r c) (m3 : mat c s),
    (m1 + m2) * m3 == m1 * m3 + m2 * m3.
Proof. intros. apply mmul_add_distr_r. Qed.

Lemma mmul_0_l : forall {r c s} (m : mat c s), (mat0 r c) * m == mat0 r s.
Proof. intros. apply mmul_0_l. Qed.

Lemma mmul_0_r : forall {r c s} (m : mat r c), m * (mat0 c s) == mat0 r s.
Proof. intros. apply mmul_0_r. Qed.

Lemma mmul_1_l : forall {r c} (m : mat r c), (mat1 r) * m == m.
Proof. intros. apply mmul_1_l. Qed.

Lemma mmul_1_r : forall {r c} (m : mat r c), m * (mat1 c) == m.
Proof. intros. apply mmul_1_r. Qed.

Lemma mcmul_mul : forall {r c s} a (m1 : mat r c) (m2 : mat c s),
    (a c* m1) * m2 == a c* (m1 * m2).
Proof. intros. apply mcmul_mul. Qed.

Lemma mmul_mcmul : forall {r c s} a (m1 : mat r c) (m2 : mat c s),
    m1 * (a c* m2) == a c* (m1 * m2).
Proof. intros. apply mmul_mcmul. Qed.

Definition Square n := mat n n.

Definition trace {n} (m : Square n) := trace m (add:=Rplus) (zero:=0).

Definition t2m_1x1 a11 : mat 1 1 := t2m_1x1 (A0:=0) a11.

Definition m2t_1x1 (m : mat 1 1) := m2t_1x1 m.

Definition t2m_2x2 (t : T_2x2) : mat 2 2 := t2m_2x2 (A0:=0) t.

Definition m2t_2x2 (m : mat 2 2) := m2t_2x2 m.

Definition t2m_3x3 (t : T_3x3) : mat 3 3 := t2m_3x3 (A0:=0) t.

Definition m2t_3x3 (m : mat 3 3) := m2t_3x3 m.


(* ################################################################# *)
(** ** 新增的 实数矩阵理论 *)

(** 3阶方阵的行列式 *)
Definition det3 (m : mat 3 3) :=
  let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) :=
    m2t_3x3 m in
  (let b1 := (a11 * a22 * a33) in
  let b2 := (a12 * a23 * a31) in
  let b3 := (a13 * a21 * a32) in
  let c1 := (a11 * a23 * a32) in
  let c2 := (a12 * a21 * a33) in
  let c3 := (a13 * a22 * a31) in
  let b := (b1 + b2 + b3) in
  let c := (c1 + c2 + c3) in
  (b - c))%R.
