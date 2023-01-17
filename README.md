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
	NatExt.v ZExt.v QExt.v QcExt.v RExt.v SetoidListExt.v SetoidListListExt.v
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
  | Models                                  | DepList | DepPair | DepRec | NatFun | FinFun |
  | --------------------------------------- | ------- | ------- | ------ | ------ | ------ |
  | Maturity                                | *       | *       | **     | **     | ***    |
  | Conciseness of the definitions          | *       | *       | *      | ***    | ***    |
  | Conciseness of the proofs               | *       | *       | **     | ***    | ***    |
  | Conciseness of the extracted OCaml code | *       | *       | ***    | **     | **     |
  | Simplicity of the syntax or skill       | **      | **      | ***    | **     | *      |

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
