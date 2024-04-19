
module Nat =
 struct
 end

(** val seqsumAux : ('a1 -> 'a1 -> 'a1) -> int -> (int -> 'a1) -> 'a1 -> 'a1 **)

let rec seqsumAux aadd n f acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun n' -> seqsumAux aadd n' f (aadd (f n') acc))
    n

(** val seqsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> (int -> 'a1) -> 'a1 **)

let seqsum aadd azero n f =
  seqsumAux aadd n f azero

module MatrixModel =
 struct
  type coq_A = float

  (** val coq_Azero : coq_A **)

  let coq_Azero = 0.0

  (** val coq_Aadd : coq_A -> coq_A -> coq_A **)

  let coq_Aadd = (+.)

  (** val coq_Amul : coq_A -> coq_A -> coq_A **)

  let coq_Amul = ( *.)

  type mat = (float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array2.t

  (** val mrows : mat -> int **)

  let mrows = Bigarray.Array2.dim1

  (** val mcols : mat -> int **)

  let mcols = Bigarray.Array2.dim2

  (** val mget : mat -> int -> int -> coq_A **)

  let mget = Bigarray.Array2.get

  (** val mcreate : int -> int -> mat **)

  let mcreate = Bigarray.Array2.create Float64 C_layout

  (** val minit : int -> int -> (int -> int -> coq_A) -> mat **)

  let minit = Bigarray.Array2.init Float64 C_layout
 end

module MatrixTheory =
 struct
  (** val mnull : MatrixModel.mat **)

  let mnull =
    MatrixModel.mcreate 0 0

  (** val mtrans : MatrixModel.mat -> MatrixModel.mat **)

  let mtrans m =
    let r = MatrixModel.mrows m in
    let c = MatrixModel.mcols m in MatrixModel.minit c r (fun i j -> MatrixModel.mget m j i)

  (** val madd : MatrixModel.mat -> MatrixModel.mat -> MatrixModel.mat **)

  let madd m1 m2 =
    let r = MatrixModel.mrows m1 in
    let c = MatrixModel.mcols m1 in
    let r' = MatrixModel.mrows m2 in
    let c' = MatrixModel.mcols m2 in
    if (&&) ((=) r r') ((=) c c')
    then MatrixModel.minit r c (fun i j ->
           MatrixModel.coq_Aadd (MatrixModel.mget m1 i j) (MatrixModel.mget m2 i j))
    else mnull

  (** val mmul : MatrixModel.mat -> MatrixModel.mat -> MatrixModel.mat **)

  let mmul m1 m2 =
    let r = MatrixModel.mrows m1 in
    let c = MatrixModel.mcols m1 in
    let c' = MatrixModel.mrows m2 in
    let s = MatrixModel.mcols m2 in
    if (=) c c'
    then MatrixModel.minit r s (fun i j ->
           seqsum MatrixModel.coq_Aadd MatrixModel.coq_Azero c (fun k ->
             MatrixModel.coq_Amul (MatrixModel.mget m1 i k) (MatrixModel.mget m2 k j)))
    else mnull

  (** val mmul2 : MatrixModel.mat -> MatrixModel.mat -> MatrixModel.mat **)

  let mmul2 m1 m2 =
    let r = MatrixModel.mrows m1 in
    let c = MatrixModel.mcols m1 in
    let c' = MatrixModel.mrows m2 in
    let s = MatrixModel.mcols m2 in
    if (=) c c'
    then MatrixModel.minit r s (fun i j ->
           MatrixModel.coq_Amul (MatrixModel.mget m1 i 0) (MatrixModel.mget m2 0 j))
    else mnull
 end
