# CoqMatrix

## 1. Introduction
* This is a formal matrix library in Coq, and integrated with multiple different implementations.
* Our goal is to provide a unified framework for different implementations of formalized matrix libraries, so as to decouple the differences between underlying technologies and upper-level applications.
* There are several design ideas in this:
  * we mainly use equivalence relations on setoid instead of Leibniz equal.
  * organize an operation and its related properties with typeclasses instead of unorganized scattered assumptions, to simplify the proof and improve the readibility.
  * organize the mathematical hierarchy of element or matrix with module type.
  * mainly use functor to maintain the polymorphism of the design, the concrete theory could be batch exported.

* What we have done?
  * First, developped several useful extensions for Coq Standard Library, such as:
	NatExt.v ZExt.v QExt.v QcExt.v RExt.v SetoidListExt.v SetoidListListExt.v HierarchySetoid.v
  * Second, seperately reimplement formal matrix library of several known matrix model.
  * Third, design mathematical hierarchy of matrix element and matrix interface.
  * Forth, package different implementations according the matrix interface.
  * Fifth, create conversion between different models, and proof lots of them are homomorphism/isomomorphism.

* What we got?
  * An available formal matrix library with unified interface under several different low-level implementations.
  * A fundamental technical comparison of these different models, about maturity, simplicity, technical difficulty etc.

* History of this project?
  * It is a submodule of project [VFCS](https://github.com/zhengpushi/VFCS)
  * A stage version is published in SETTA 2022, and located in [coq-matrix](https://github.com/zhengpushi/coq-matrix).

* How to contact us?
  * We are a team focusing on formal engineering mathematics study, and located in Nanjing University of  Aeronautics and Astronautics, in China.
  * Author: ZhengPu Shi (zhengpushi@nuaa.edu.cn) 

## 2. A comparison result
  | Models                                  | DepList | DepPair | DepRec | NatFun | FinFun | SafeNatFun |
  | --------------------------------------- | ------- | ------- | ------ | ------ | ------ | ---------- |
  | Maturity                                | *       | *       | **     | **     | ***    | **         |
  | Conciseness of the definitions          | *       | *       | *      | ***    | ***    | ***        |
  | Conciseness of the proofs               | *       | *       | **     | ***    | ***    | ***        |
  | Conciseness of the extracted OCaml code | *       | *       | ***    | **     | **     | **         |
  | Simplicity of the syntax or skill       | **      | **      | ***    | **     | *      | *          |

## 3. Dependent or related projects
* Dependent projects
  * [CoqExt](https://github.com/zhengpushi/CoqExt): Extension of Coq Standard Libray.

* Related projects
  * [VFCS](https://github.com/zhengpushi/VFCS): Verified flight control system.


## 4. Reference resources
* [DepRec](https://gitee.com/yingyingma/Matrix): Matrix by NUAA
* [DepList](https://coq.inria.fr/distrib/current/stdlib/Coq.Vectors.Vector.html): Coq.Vectors.Vector
* [DepPair](http://coquelicot.saclay.inria.fr/html/Coquelicot.Hierarchy.html#matrix): Matrix in Coquelicot
* [NatFun](https://www.cs.umd.edu/~rrand/vqc/index.html): Verified Quantum Computing, Software Foundations Inspired, Volume Q.
* [FinFun](https://math-comp.github.io/): Mathematical Component
* [SafeNatFun]: by myself, look at the source code.

## 5. Usage demo.
* Basic usage

  ```coq
  From CoqMatrix Import MatrixNat. (* use "MatrixZ, MatrixQ, MatrixQc, MatrixR" as you need *)
  
  (** Then, all functions, theorems, notations are available *)
  Example dl := [[1;2;3];[4;5;6]].
  Example m1 : mat 2 3 := @l2m 2 3 dl.
  Compute (m2l m1). (* = [[1; 2; 3]; [4; 5; 6]] : list (list A) *)
  Compute (mnth m1 0 1). (* = 2 : A *)
  Compute (m2l (m1\T)). (* = [[1; 4]; [2; 5]; [3; 6]] : list (list A) *)
  Goal mmap S m1 == l2m [[2;3;4];[5;6;7]].
  Proof. 
    (** Proof with tactic "lma" (linear matrix arithmetic), availabe for all models *)
    lma.
  Qed.
  
  (** Check that if A is nat really *)
  Print A. (* A = nat : Type *)
  
  (** You can mixed use all models *)
  Import MatrixAllNat. (* all models *)
  Compute @DL.l2m 2 3 dl.
  Compute @DP.l2m 2 3 dl.
  Compute @DR.l2m 2 3 dl.
  Compute @NF.l2m 2 3 dl.
  ```

* Support Q type (rational number) and Qc type (canonical rational number), hence the low-level equality is Setoid Equality instead of Leibniz Equality.

  ```coq
  Import MatrixQ.
  (* automatic maintain the Scope and Notations. for exmaple, here, Q_scope is opened. *)
  
  Example m1 : mat 2 3 := l2m [[6/4;10/4;7/2];[4;5;6]].
  Example m2 : mat 2 3 := l2m [[1.5;2.5;3.5];[4;5;6]].
  
  Example eq1: m1 == m2. Proof. lma. Qed.
  
  (** Proof by ltac or by using properties *)
  Goal m1 * (mat1 _) == m2. Proof. lma. Qed.
  Goal m1 * (mat1 _) == m2. Proof. rewrite mmul_1_r. apply eq1. Qed.
  ```

* Conversion between models, and all these conversion functions are bijective.

  ```coq
  (* opem matrix theory on Z with default model *)
  Import MatrixZ.
  (* open matrix theory on Z with all models (optional) *)
  Import MatrixAllZ.
  
  (** convert from one model to other models *)
  Example m : NF.mat 2 2 := NF.mk_mat_2_2 1 2 3 4.
  Compute nf2dl m. (* = [[1; 2]; [3; 4]]%vector : DL.mat 2 2 *)
  Compute nf2dp m. (* = (1, (2, tt), (3, (4, tt), tt)) : DP.mat 2 2 *)
  Compute nf2dr m. (* = {| mdata := [[1;2];[3;4]]; .. |} : DR.mat 2 2 *)
  
  (** prove that {SF -> DL -> DP -> DR -> NF -> DL -> SF} return back *)
  Goal forall r c (m0 : SF.mat r c),
    let m1 : DL.mat r c := sf2dl m0 in
    let m2 : DP.mat r c := dl2dp m1 in
    let m3 : DR.mat r c := dp2dr m2 in
    let m4 : NF.mat r c := dr2nf m3 in
    let m5 : DL.mat r c := nf2dl m4 in
    let m6 : SF.mat r c := dl2sf m5 in
    m6 == m0.
  Proof.
    intros. unfold m6,m5,m4,m3,m2,m1,dl2dp,dp2dr,dr2nf,nf2dl,dl2sf,sf2dl.
    rewrite DR.m2l_l2m_id; auto with mat.
    rewrite NF.m2l_l2m_id; auto with mat.
    rewrite DP.m2l_l2m_id; auto with mat.
    rewrite DL.m2l_l2m_id; auto with mat.
    rewrite DL.m2l_l2m_id; auto with mat.
    rewrite SF.l2m_m2l_id; auto with mat.
    reflexivity.
  Qed.
  ```
