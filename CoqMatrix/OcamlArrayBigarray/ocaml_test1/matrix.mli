
module Nat :
 sig
 end

val seqsumAux : ('a1 -> 'a1 -> 'a1) -> int -> (int -> 'a1) -> 'a1 -> 'a1

val seqsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> (int -> 'a1) -> 'a1

module MatrixModel :
 sig
  type coq_A = float

  val coq_Azero : coq_A

  val coq_Aadd : coq_A -> coq_A -> coq_A

  val coq_Amul : coq_A -> coq_A -> coq_A

  type mat = (float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array2.t

  val mrows : mat -> int

  val mcols : mat -> int

  val mget : mat -> int -> int -> coq_A

  val mcreate : int -> int -> mat

  val minit : int -> int -> (int -> int -> coq_A) -> mat
 end

module MatrixTheory :
 sig
  val mnull : MatrixModel.mat

  val mtrans : MatrixModel.mat -> MatrixModel.mat

  val madd : MatrixModel.mat -> MatrixModel.mat -> MatrixModel.mat

  val mmul : MatrixModel.mat -> MatrixModel.mat -> MatrixModel.mat

  val mmul2 : MatrixModel.mat -> MatrixModel.mat -> MatrixModel.mat
 end
