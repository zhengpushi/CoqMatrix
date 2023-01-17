
type __ = Obj.t

val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2



val pred : int -> int

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

type reflect =
| ReflectT
| ReflectF

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val ltb : int -> int -> bool

  val pow : int -> int -> int
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val size_nat : positive -> int

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val ggcdn : int -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val of_nat : int -> positive

  val of_succ_nat : int -> positive
 end

val hd : 'a1 -> 'a1 list -> 'a1

val tl : 'a1 list -> 'a1 list

val nth : int -> 'a1 list -> 'a1 -> 'a1

val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val repeat : 'a1 -> int -> 'a1 list

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val sgn : z -> z

  val max : z -> z -> z

  val min : z -> z -> z

  val abs : z -> z

  val to_nat : z -> int

  val of_nat : int -> z

  val to_pos : z -> positive

  val ggcd : z -> z -> z * (z * z)
 end

type q = { qnum : z; qden : positive }

type t =
| F1 of int
| FS of int * t

val eqb : int -> int -> t -> t -> bool

val eq_dec : int -> t -> t -> bool

type 'a t0 =
| Nil
| Cons of 'a * int * 'a t0

val case0 : 'a2 -> 'a1 t0 -> 'a2

val caseS : ('a1 -> int -> 'a1 t0 -> 'a2) -> int -> 'a1 t0 -> 'a2

val caseS' : int -> 'a1 t0 -> ('a1 -> 'a1 t0 -> 'a2) -> 'a2

val rect2 :
  'a3 -> (int -> 'a1 t0 -> 'a2 t0 -> 'a3 -> 'a1 -> 'a2 -> 'a3) -> int -> 'a1 t0 -> 'a2 t0 -> 'a3

val hd0 : int -> 'a1 t0 -> 'a1

val const : 'a1 -> int -> 'a1 t0

val nth0 : int -> 'a1 t0 -> t -> 'a1

val tl0 : int -> 'a1 t0 -> 'a1 t0

val map2 : ('a1 -> 'a2 -> 'a3) -> int -> 'a1 t0 -> 'a2 t0 -> 'a3 t0

val fold_left : ('a2 -> 'a1 -> 'a2) -> 'a2 -> int -> 'a1 t0 -> 'a2

type cReal = { seq : (z -> q); scale : z }

type dReal = (q -> bool)

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl :
 RbaseSymbolsSig

val iPR_2 : positive -> RbaseSymbolsImpl.coq_R

val iPR : positive -> RbaseSymbolsImpl.coq_R

val iZR : z -> RbaseSymbolsImpl.coq_R

val total_order_T : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool option

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

val req_EM_T : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val reqb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

module type FieldSig =
 sig
  type coq_X

  val coq_X0 : coq_X

  val coq_X1 : coq_X

  val coq_Xadd : coq_X -> coq_X -> coq_X

  val coq_Xmul : coq_X -> coq_X -> coq_X

  val coq_Xopp : coq_X -> coq_X

  val coq_Xinv : coq_X -> coq_X

  val coq_Xeqb : coq_X -> coq_X -> bool

  val coq_Xeqdec : coq_X -> coq_X -> bool
 end

module FieldThy :
 functor (F:FieldSig) ->
 sig
 end

module FieldR :
 sig
  module FieldDefR :
   FieldSig with type coq_X = RbaseSymbolsImpl.coq_R
 end

type 'a t2 = 'a * 'a

type 'a t3 = 'a t2 * 'a

type 'a t_3x3 = ('a t3 * 'a t3) * 'a t3

val lzero : 'a1 -> int -> 'a1 list

val map0 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val ldot : 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 list -> 'a1 list -> 'a1

val dlist_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list list -> 'a1 list list -> bool

val dnil : int -> 'a1 list list

val cvt_row2col : 'a1 list -> 'a1 list list

val hdc : 'a1 -> 'a1 list list -> 'a1 list

val consc : 'a1 list -> 'a1 list list -> 'a1 list list

val dlzero : 'a1 -> int -> int -> 'a1 list list

val dlunit : 'a1 -> 'a1 -> int -> 'a1 list list

val dltrans : 'a1 list list -> int -> 'a1 list list

val dmap : ('a1 -> 'a2) -> 'a1 list list -> 'a2 list list

val dmap2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list list -> 'a2 list list -> 'a3 list list

val ldotdl : 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 list -> 'a1 list list -> 'a1 list

val dldotdl :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 list list -> 'a1 list list -> 'a1 list list

type 't vec = __

val vec_eq_dec : ('a1 -> 'a1 -> bool) -> int -> 'a1 vec -> 'a1 vec -> bool

val vrepeat : int -> 'a1 -> 'a1 vec

val vmake_aux : int -> int -> (int -> 'a1) -> 'a1 vec

val vmake : int -> (int -> 'a1) -> 'a1 vec

val vnth : 'a1 -> int -> int -> 'a1 vec -> 'a1

val vmap : ('a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec

val vmap2 : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1 vec

val vadd : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1 vec

val vopp : ('a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec

val vfoldl : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 vec -> 'a1

val vdot : 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1

val v2l : int -> 'a1 vec -> 'a1 list

val l2v : 'a1 -> 'a1 list -> int -> 'a1 vec

module Coq__2 : sig
 type 't mat = 't vec vec
end
include module type of struct include Coq__2 end

val mmake : int -> int -> (int -> int -> 'a1) -> 'a1 mat

val mnth : 'a1 -> int -> int -> 'a1 mat -> int -> int -> 'a1

val mat0 : 'a1 -> int -> int -> 'a1 mat

val mmap : ('a1 -> 'a1) -> int -> int -> 'a1 mat -> 'a1 mat

val mmap2 : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat -> 'a1 mat -> 'a1 mat

val mconsr : int -> int -> 'a1 vec -> 'a1 vec vec -> 'a1 vec vec

val mconsc : int -> int -> 'a1 vec -> 'a1 vec vec -> 'a1 vec vec

val mhdc : int -> int -> 'a1 mat -> 'a1 vec

val mtlc : int -> int -> 'a1 mat -> 'a1 mat

val mat1 : 'a1 -> 'a1 -> int -> 'a1 mat

val madd : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat -> 'a1 mat -> 'a1 mat

val mopp : ('a1 -> 'a1) -> int -> int -> 'a1 mat -> 'a1 mat

val msub : ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat -> 'a1 mat -> 'a1 mat

val mcmul : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 mat -> 'a1 mat

val mmulc : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat -> 'a1 -> 'a1 mat

val mtrans : int -> int -> 'a1 mat -> 'a1 mat

val vdotm :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 vec -> 'a1 mat -> 'a1 vec

val mdot :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> int -> 'a1 mat -> 'a1 mat -> 'a1
  mat

val mmul :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> int -> 'a1 mat -> 'a1 mat -> 'a1
  mat

val m2l : int -> int -> 'a1 mat -> 'a1 list list

val l2m : 'a1 -> 'a1 list list -> int -> int -> 'a1 mat

module MatrixThy :
 functor (F:FieldSig) ->
 sig
  type 'x mat = 'x Coq__2.mat

  val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X

  val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool

  val mk_mat_1_1 : F.coq_X -> F.coq_X mat

  val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

  val mk_mat_3_3 :
    F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X ->
    F.coq_X mat

  val mat0 : int -> int -> F.coq_X mat

  val mat1 : int -> F.coq_X mat

  val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat

  val mmap2 :
    int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  val madd : int -> int -> F.coq_X Coq__2.mat -> F.coq_X Coq__2.mat -> F.coq_X Coq__2.mat

  val mopp : int -> int -> F.coq_X mat -> F.coq_X mat

  val msub : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat

  val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat

  val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat

  val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  val l2m_old : int -> int -> F.coq_X list list -> F.coq_X mat

  val l2m : int -> int -> F.coq_X list list -> F.coq_X mat

  val m2l : int -> int -> F.coq_X mat -> F.coq_X list list

  val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat

  val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3

  val scalar_of_mat : F.coq_X mat -> F.coq_X
 end

val fin_gen : int -> int -> t option

val vec_S : int -> 'a1 t0 -> ('a1, 'a1 t0) sigT

val veq_dec : ('a1 -> 'a1 -> bool) -> int -> 'a1 t0 -> 'a1 t0 -> bool

val vmake0 : int -> (t -> 'a1) -> 'a1 t0

val vget : 'a1 -> int -> 'a1 t0 -> int -> 'a1

val vset : int -> 'a1 t0 -> int -> 'a1 -> 'a1 t0

type 'a mat2 = 'a t0 t0

val meq_dec0 : ('a1 -> 'a1 -> bool) -> int -> int -> 'a1 mat2 -> 'a1 mat2 -> bool

val mcoli : int -> int -> 'a1 mat2 -> t -> 'a1 t0

val mnth0 : int -> int -> 'a1 mat2 -> t -> t -> 'a1

val mget : 'a1 -> int -> int -> 'a1 mat2 -> int -> int -> 'a1

val mset : 'a1 -> int -> int -> 'a1 mat2 -> int -> int -> 'a1 -> 'a1 mat2

val mat3 : 'a1 -> int -> int -> 'a1 mat2

val mat4 : 'a1 -> 'a1 -> int -> 'a1 mat2

val mtrans0 : int -> int -> 'a1 mat2 -> 'a1 mat2

val vdot0 : 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 t0 -> 'a1 t0 -> 'a1

val mmap0 : ('a1 -> 'a1) -> int -> int -> 'a1 mat2 -> 'a1 mat2

val mmap1 : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat2 -> 'a1 mat2 -> 'a1 mat2

val mopp0 : ('a1 -> 'a1) -> int -> int -> 'a1 mat2 -> 'a1 mat2

val madd0 : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat2 -> 'a1 mat2 -> 'a1 mat2

val msub0 : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat2 -> 'a1 mat2 -> 'a1 mat2

val mcmul0 : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 mat2 -> 'a1 mat2

val mmulc0 : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat2 -> 'a1 -> 'a1 mat2

val mmul0 :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> int -> 'a1 mat2 -> 'a1 mat2 ->
  'a1 mat2

val v2l0 : int -> 'a1 t0 -> 'a1 list

val l2v0 : 'a1 -> 'a1 list -> int -> 'a1 t0

val m2l0 : int -> int -> 'a1 mat2 -> 'a1 list list

val l2m0 : 'a1 -> 'a1 list list -> int -> int -> 'a1 mat2

module Coq_MatrixThy :
 functor (F:FieldSig) ->
 sig
  type 'x mat = 'x mat2

  val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool

  val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X

  val mk_mat_1_1 : F.coq_X -> F.coq_X mat

  val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

  val mk_mat_3_3 :
    F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X ->
    F.coq_X mat

  val mat0 : int -> int -> F.coq_X mat

  val mat1 : int -> F.coq_X mat

  val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat

  val mmap2 :
    int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  val madd : int -> int -> F.coq_X mat2 -> F.coq_X mat2 -> F.coq_X mat2

  val mopp : int -> int -> F.coq_X mat -> F.coq_X mat

  val msub : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat

  val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat

  val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat

  val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  val l2m : int -> int -> F.coq_X list list -> F.coq_X mat

  val m2l : int -> int -> F.coq_X mat -> F.coq_X list list

  val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat

  val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3

  val scalar_of_mat : F.coq_X mat -> F.coq_X

  val mget : F.coq_X -> int -> int -> F.coq_X mat2 -> int -> int -> F.coq_X

  val mset : F.coq_X -> int -> int -> F.coq_X mat2 -> int -> int -> F.coq_X -> F.coq_X mat2
 end

type 'a mat5 = 'a list list
  (* singleton inductive, whose constructor was mk_mat *)

val mat_data : int -> int -> 'a1 mat5 -> 'a1 list list

val mk_mat_1_0 : 'a1 -> 'a1 mat5

val mk_mat_r_1 : 'a1 list -> int -> 'a1 mat5

val mk_mat_3_0 : 'a1 -> 'a1 -> 'a1 -> 'a1 mat5

val mk_mat_2_2 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 mat5

val mk_mat_3_2 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 mat5

val mat_nth : 'a1 -> int -> int -> 'a1 mat5 -> int -> int -> 'a1

val matmapdl : ('a1 -> 'a2) -> int -> int -> 'a1 mat5 -> 'a2 list list

val matmap2dl : ('a1 -> 'a2 -> 'a3) -> int -> int -> 'a1 mat5 -> 'a2 mat5 -> 'a3 list list

val matmap : ('a1 -> 'a2) -> int -> int -> 'a1 mat5 -> 'a2 mat5

val matmap2 : ('a1 -> 'a2 -> 'a3) -> int -> int -> 'a1 mat5 -> 'a2 mat5 -> 'a3 mat5

val matzero : 'a1 -> int -> int -> 'a1 mat5

val matunit : 'a1 -> 'a1 -> int -> 'a1 mat5

val mat_trans : int -> int -> 'a1 mat5 -> 'a1 mat5

val matadd : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat5 -> 'a1 mat5 -> 'a1 mat5

val matopp : ('a1 -> 'a1) -> int -> int -> 'a1 mat5 -> 'a1 mat5

val matsub : ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat5 -> 'a1 mat5 -> 'a1 mat5

val matmul :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> int -> 'a1 mat5 -> 'a1 mat5 ->
  'a1 mat5

val matcmul : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 mat5 -> 'a1 mat5

val matmulc : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat5 -> 'a1 -> 'a1 mat5

val l2v_aux : 'a1 -> 'a1 list -> int -> 'a1 list

val l2m_aux : 'a1 -> 'a1 list list -> int -> int -> 'a1 list list

val l2m1 : 'a1 -> 'a1 list list -> int -> int -> 'a1 mat5

module Coq0_MatrixThy :
 functor (F:FieldSig) ->
 sig
  module FieldThyInst :
   sig
   end

  type 'x mat = 'x mat5

  val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool

  val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X

  val mk_mat_1_1 : F.coq_X -> F.coq_X mat

  val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

  val mk_mat_3_3 :
    F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X ->
    F.coq_X mat

  val mk_mat_2_2 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

  val mat0 : int -> int -> F.coq_X mat

  val mat1 : int -> F.coq_X mat

  val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat

  val mmap2 :
    int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  val madd : int -> int -> F.coq_X mat5 -> F.coq_X mat5 -> F.coq_X mat5

  val mopp : int -> int -> F.coq_X mat -> F.coq_X mat

  val msub : int -> int -> F.coq_X mat5 -> F.coq_X mat5 -> F.coq_X mat5

  val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat

  val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat

  val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat

  val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  type vecr = F.coq_X mat

  type vecc = F.coq_X mat

  val mconsr : int -> int -> vecr -> F.coq_X mat -> F.coq_X mat

  val mconsc : int -> int -> vecc -> F.coq_X mat -> F.coq_X mat

  val l2m_old : int -> int -> F.coq_X list list -> F.coq_X mat

  val l2m : int -> int -> F.coq_X list list -> F.coq_X mat

  val m2l : int -> int -> F.coq_X mat -> F.coq_X list list

  val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat

  val m2t_3x3' : F.coq_X mat -> F.coq_X t_3x3

  val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3

  val scalar_of_mat : F.coq_X mat -> F.coq_X

  val det_of_mat_3_3 : F.coq_X mat -> F.coq_X
 end

module Sequence :
 functor (F:FieldSig) ->
 sig
  module FieldThyInst :
   sig
   end

  val seqeqb : int -> (int -> F.coq_X) -> (int -> F.coq_X) -> bool

  val seqeq_dec : int -> (int -> F.coq_X) -> (int -> F.coq_X) -> bool

  val seq2eqb : int -> int -> (int -> int -> F.coq_X) -> (int -> int -> F.coq_X) -> bool

  val seq2eq_dec : int -> int -> (int -> int -> F.coq_X) -> (int -> int -> F.coq_X) -> bool

  val seqsum : (int -> F.coq_X) -> int -> F.coq_X
 end

module Coq1_MatrixThy :
 functor (F:FieldSig) ->
 sig
  module FieldThyInst :
   sig
   end

  module SequenceInst :
   sig
    module FieldThyInst :
     sig
     end

    val seqeqb : int -> (int -> F.coq_X) -> (int -> F.coq_X) -> bool

    val seqeq_dec : int -> (int -> F.coq_X) -> (int -> F.coq_X) -> bool

    val seq2eqb : int -> int -> (int -> int -> F.coq_X) -> (int -> int -> F.coq_X) -> bool

    val seq2eq_dec : int -> int -> (int -> int -> F.coq_X) -> (int -> int -> F.coq_X) -> bool

    val seqsum : (int -> F.coq_X) -> int -> F.coq_X
   end

  type 'x coq_MATData = int -> int -> 'x

  type 'x mat' = 'x coq_MATData
    (* singleton inductive, whose constructor was mk_mat *)

  val mdata : int -> int -> 'a1 mat' -> 'a1 coq_MATData

  type 'x mat'' = 'x coq_MATData
    (* singleton inductive, whose constructor was mk_mat'' *)

  val mat''_rect : int -> int -> ('a1 coq_MATData -> 'a2) -> 'a1 mat'' -> 'a2

  val mat''_rec : int -> int -> ('a1 coq_MATData -> 'a2) -> 'a1 mat'' -> 'a2

  type 'x mat = 'x mat'

  val meq_dec_equiv : int -> int -> F.coq_X mat -> F.coq_X mat -> bool

  val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool

  val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X

  val mrow_aux : int -> int -> int -> int -> F.coq_X mat -> F.coq_X list

  val mrow : int -> int -> int -> F.coq_X mat -> F.coq_X list

  val l2m : int -> int -> F.coq_X list list -> F.coq_X mat

  val l2m' : F.coq_X list list -> F.coq_X mat

  val m2l_aux : int -> int -> int -> F.coq_X mat -> F.coq_X list list

  val m2l : int -> int -> F.coq_X mat -> F.coq_X list list

  val coq_MCol_aux : int -> int -> int -> int -> F.coq_X mat -> F.coq_X list

  val coq_MCol : int -> int -> int -> F.coq_X mat -> F.coq_X list

  val mshiftc : int -> int -> F.coq_X mat -> int -> F.coq_X mat

  val mk_mat_0_c : int -> F.coq_X mat

  val mk_mat_1_1 : F.coq_X -> F.coq_X mat

  val mk_mat_1_2 : F.coq_X -> F.coq_X -> F.coq_X mat

  val mk_mat_1_3 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

  val mk_mat_1_4 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

  val mk_mat_1_c : int -> F.coq_X list -> F.coq_X mat

  val mk_mat_r_0 : int -> F.coq_X mat

  val mk_mat_2_1 : F.coq_X -> F.coq_X -> F.coq_X mat

  val mk_mat_2_2 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

  val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

  val mk_mat_3_3 :
    F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X ->
    F.coq_X mat

  val mk_mat_4_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

  val mk_mat_4_4 :
    F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X ->
    F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

  val mk_mat_r_1 : int -> F.coq_X list -> F.coq_X mat

  val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat

  val mmap2 :
    int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  val mat0 : int -> int -> F.coq_X mat

  val mat1 : int -> F.coq_X mat

  val madd : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  val mopp : int -> int -> F.coq_X mat -> F.coq_X mat

  val msub : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat

  val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat

  val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat

  val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat

  val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3

  val scalar_of_mat : F.coq_X mat -> F.coq_X

  val trace : int -> F.coq_X mat -> F.coq_X
 end

val locked_with : unit -> 'a1 -> 'a1

module Option :
 sig
  val apply : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

  val default : 'a1 -> 'a1 option -> 'a1

  val bind : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option

  val map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option
 end

type ('aT, 'rT) simpl_fun = 'aT -> 'rT
  (* singleton inductive, whose constructor was SimplFun *)

val fun_of_simpl : ('a1, 'a2) simpl_fun -> 'a1 -> 'a2

val comp : ('a2 -> 'a1) -> ('a3 -> 'a2) -> 'a3 -> 'a1

val pcomp : ('a2 -> 'a1 option) -> ('a3 -> 'a2 option) -> 'a3 -> 'a1 option

val tag : ('a1, 'a2) sigT -> 'a1

val tagged : ('a1, 'a2) sigT -> 'a2

val tagged0 : 'a1 -> 'a2 -> ('a1, 'a2) sigT

val isSome : 'a1 option -> bool

type decidable = bool

val iffP : bool -> reflect -> reflect

val decP : bool -> reflect -> decidable

val idP : bool -> reflect

val andP : bool -> bool -> reflect

type 't pred0 = 't -> bool

type 't predType = __ -> 't pred0
  (* singleton inductive, whose constructor was PredType *)

type 't pred_sort = __

val predPredType : 'a1 predType

type 't simpl_pred = ('t, bool) simpl_fun

val simplPred : 'a1 pred0 -> 'a1 simpl_pred

val predT : 'a1 simpl_pred

module PredOfSimpl :
 sig
  val coerce : 'a1 simpl_pred -> 'a1 pred0
 end

val pred_of_argType : 'a1 simpl_pred

type 't rel = 't -> 't pred0

type 't mem_pred = 't pred0
  (* singleton inductive, whose constructor was Mem *)

val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort

val in_mem : 'a1 -> 'a1 mem_pred -> bool

val simpl_of_mem : 'a1 mem_pred -> 'a1 simpl_pred

val mem : 'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred

module Equality :
 sig
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  val op : 'a1 mixin_of -> 'a1 rel

  type coq_type = __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort mixin_of
 end

val eq_op : Equality.coq_type -> Equality.sort rel

val eqP : Equality.coq_type -> Equality.sort Equality.axiom

val pred1 : Equality.coq_type -> Equality.sort -> Equality.sort simpl_pred

type 't comparable = 't -> 't -> decidable

val eq_comparable : Equality.coq_type -> Equality.sort comparable

type 't subType = { val0 : (__ -> 't); sub0 : ('t -> __ -> __);
                    subType__2 : (__ -> ('t -> __ -> __) -> __ -> __) }

type 't sub_sort = __

val sub0 : 'a1 pred0 -> 'a1 subType -> 'a1 -> 'a1 sub_sort

val insub : 'a1 pred0 -> 'a1 subType -> 'a1 -> 'a1 sub_sort option

val insubd : 'a1 pred0 -> 'a1 subType -> 'a1 sub_sort -> 'a1 -> 'a1 sub_sort

val inj_eqAxiom : Equality.coq_type -> ('a1 -> Equality.sort) -> 'a1 Equality.axiom

val injEqMixin : Equality.coq_type -> ('a1 -> Equality.sort) -> 'a1 Equality.mixin_of

val pcanEqMixin :
  Equality.coq_type -> ('a1 -> Equality.sort) -> (Equality.sort -> 'a1 option) -> 'a1 Equality.mixin_of

val val_eqP :
  Equality.coq_type -> Equality.sort pred0 -> Equality.sort subType -> Equality.sort sub_sort
  Equality.axiom

val pair_eq : Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort) rel

val pair_eqP : Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort) Equality.axiom

val prod_eqMixin :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort) Equality.mixin_of

val prod_eqType : Equality.coq_type -> Equality.coq_type -> Equality.coq_type

val tagged_as : Equality.coq_type -> (Equality.sort, 'a1) sigT -> (Equality.sort, 'a1) sigT -> 'a1

val tag_eq :
  Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> (Equality.sort, Equality.sort) sigT ->
  (Equality.sort, Equality.sort) sigT -> bool

val tag_eqP :
  Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> (Equality.sort, Equality.sort) sigT
  Equality.axiom

val tag_eqMixin :
  Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> (Equality.sort, Equality.sort) sigT
  Equality.mixin_of

val tag_eqType : Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> Equality.coq_type

val eqn : int -> int -> bool

val eqnP : int Equality.axiom

val nat_eqMixin : int Equality.mixin_of

val nat_eqType : Equality.coq_type

val subn_rec : int -> int -> int

val subn : int -> int -> int

val leq : int -> int -> bool

val iteri : int -> (int -> 'a1 -> 'a1) -> 'a1 -> 'a1

val iterop : int -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

val muln_rec : int -> int -> int

val muln : int -> int -> int

val expn_rec : int -> int -> int

val expn : int -> int -> int

val double_rec : int -> int

val double0 : int -> int

val size : 'a1 list -> int

val cat : 'a1 list -> 'a1 list -> 'a1 list

val nth1 : 'a1 -> 'a1 list -> int -> 'a1

val find : 'a1 pred0 -> 'a1 list -> int

val filter : 'a1 pred0 -> 'a1 list -> 'a1 list

val eqseq : Equality.coq_type -> Equality.sort list -> Equality.sort list -> bool

val eqseqP : Equality.coq_type -> Equality.sort list Equality.axiom

val seq_eqMixin : Equality.coq_type -> Equality.sort list Equality.mixin_of

val seq_eqType : Equality.coq_type -> Equality.coq_type

val index : Equality.coq_type -> Equality.sort -> Equality.sort list -> int

val map1 : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val pmap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list

val iota : int -> int -> int list

val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val flatten : 'a1 list list -> 'a1 list

module CodeSeq :
 sig
  val code : int list -> int

  val decode_rec : int -> int -> int -> int list

  val decode : int -> int list
 end

val tag_of_pair : ('a1 * 'a2) -> ('a1, 'a2) sigT

val pair_of_tag : ('a1, 'a2) sigT -> 'a1 * 'a2

module Choice :
 sig
  type 't mixin_of = 't pred0 -> int -> 't option
    (* singleton inductive, whose constructor was Mixin *)

  val find : 'a1 mixin_of -> 'a1 pred0 -> int -> 'a1 option

  type 't class_of = { base : 't Equality.mixin_of; mixin : 't mixin_of }

  val base : 'a1 class_of -> 'a1 Equality.mixin_of

  val mixin : 'a1 class_of -> 'a1 mixin_of

  type coq_type = __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort class_of

  val pack : 'a1 mixin_of -> 'a1 Equality.mixin_of -> Equality.coq_type -> coq_type

  val eqType : coq_type -> Equality.coq_type

  module InternalTheory :
   sig
    val find : coq_type -> sort pred0 -> int -> sort option
   end
 end

val pcanChoiceMixin :
  Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1 option) -> 'a1 Choice.mixin_of

val canChoiceMixin :
  Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1) -> 'a1 Choice.mixin_of

val sub_choiceMixin :
  Choice.coq_type -> Choice.sort pred0 -> Choice.sort subType -> Choice.sort sub_sort Choice.mixin_of

val tagged_choiceMixin :
  Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> (Choice.sort, Choice.sort) sigT
  Choice.mixin_of

val tagged_choiceType : Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> Choice.coq_type

val nat_choiceMixin : int Choice.mixin_of

val nat_choiceType : Choice.coq_type

val prod_choiceMixin :
  Choice.coq_type -> Choice.coq_type -> (Choice.sort * Choice.sort) Choice.mixin_of

val prod_choiceType : Choice.coq_type -> Choice.coq_type -> Choice.coq_type

module Countable :
 sig
  type 't mixin_of = { pickle : ('t -> int); unpickle : (int -> 't option) }

  val pickle : 'a1 mixin_of -> 'a1 -> int

  val unpickle : 'a1 mixin_of -> int -> 'a1 option

  val coq_ChoiceMixin : 'a1 mixin_of -> 'a1 Choice.mixin_of

  type 't class_of = { base : 't Choice.class_of; mixin : 't mixin_of }

  val base : 'a1 class_of -> 'a1 Choice.class_of

  val mixin : 'a1 class_of -> 'a1 mixin_of

  type coq_type = __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort class_of

  val choiceType : coq_type -> Choice.coq_type
 end

val unpickle0 : Countable.coq_type -> int -> Countable.sort option

val pickle0 : Countable.coq_type -> Countable.sort -> int

val pcanCountMixin :
  Countable.coq_type -> ('a1 -> Countable.sort) -> (Countable.sort -> 'a1 option) -> 'a1
  Countable.mixin_of

val canCountMixin :
  Countable.coq_type -> ('a1 -> Countable.sort) -> (Countable.sort -> 'a1) -> 'a1 Countable.mixin_of

val sub_countMixin :
  Countable.coq_type -> Countable.sort pred0 -> Countable.sort subType -> Countable.sort sub_sort
  Countable.mixin_of

val pickle_tagged :
  Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> (Countable.sort, Countable.sort)
  sigT -> int

val unpickle_tagged :
  Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> int -> (Countable.sort,
  Countable.sort) sigT option

val tag_countMixin :
  Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> (Countable.sort, Countable.sort)
  sigT Countable.mixin_of

val tag_countType : Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> Countable.coq_type

val nat_countMixin : int Countable.mixin_of

val nat_countType : Countable.coq_type

val prod_countMixin :
  Countable.coq_type -> Countable.coq_type -> (Countable.sort * Countable.sort) Countable.mixin_of

module Finite :
 sig
  type mixin_of = { mixin_base : Equality.sort Countable.mixin_of; mixin_enum : Equality.sort list }

  val mixin_base : Equality.coq_type -> mixin_of -> Equality.sort Countable.mixin_of

  val mixin_enum : Equality.coq_type -> mixin_of -> Equality.sort list

  type 't class_of = { base : 't Choice.class_of; mixin : mixin_of }

  val base : 'a1 class_of -> 'a1 Choice.class_of

  val mixin : 'a1 class_of -> mixin_of

  val base2 : 'a1 class_of -> 'a1 Countable.class_of

  type coq_type = __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort class_of

  val eqType : coq_type -> Equality.coq_type

  val choiceType : coq_type -> Choice.coq_type

  val countType : coq_type -> Countable.coq_type

  module type EnumSig =
   sig
    val enum : coq_type -> sort list
   end

  module EnumDef :
   EnumSig
 end

val enum_mem : Finite.coq_type -> Finite.sort mem_pred -> Finite.sort list

module type CardDefSig =
 sig
  val card : Finite.coq_type -> Finite.sort mem_pred -> int
 end

module CardDef :
 CardDefSig

val pred0b : Finite.coq_type -> Finite.sort pred0 -> bool

module FiniteQuant :
 sig
  type quantified = bool
    (* singleton inductive, whose constructor was Quantified *)

  val all : Finite.coq_type -> quantified -> Finite.sort -> Finite.sort -> quantified
 end

val pred0P : Finite.coq_type -> Finite.sort pred0 -> reflect

val forallPP : Finite.coq_type -> Finite.sort pred0 -> (Finite.sort -> reflect) -> reflect

val eqfunP :
  Finite.coq_type -> (Finite.sort -> Equality.coq_type) -> (Finite.sort -> Equality.sort) ->
  (Finite.sort -> Equality.sort) -> reflect

val image_mem : Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort mem_pred -> 'a1 list

val codom : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 list

type ordinal = int
  (* singleton inductive, whose constructor was Ordinal *)

val nat_of_ord : int -> ordinal -> int

val ordinal_subType : int -> int subType

val ordinal_eqMixin : int -> ordinal Equality.mixin_of

val ordinal_eqType : int -> Equality.coq_type

val ordinal_choiceMixin : int -> ordinal Choice.mixin_of

val ordinal_choiceType : int -> Choice.coq_type

val ordinal_countMixin : int -> ordinal Countable.mixin_of

val ord_enum : int -> ordinal list

val ordinal_finMixin : int -> Finite.mixin_of

val ordinal_finType : int -> Finite.coq_type

val enum_rank_in :
  Finite.coq_type -> Finite.sort -> Finite.sort pred_sort -> Equality.sort -> int sub_sort

val enum_rank : Finite.coq_type -> Finite.sort -> int sub_sort

val prod_enum : Finite.coq_type -> Finite.coq_type -> (Finite.sort * Finite.sort) list

val prod_finMixin : Finite.coq_type -> Finite.coq_type -> Finite.mixin_of

val prod_finType : Finite.coq_type -> Finite.coq_type -> Finite.coq_type

type 't tuple_of = 't list
  (* singleton inductive, whose constructor was Tuple *)

val tval : int -> 'a1 tuple_of -> 'a1 list

val tuple_subType : int -> 'a1 list subType

val tnth_default : int -> 'a1 tuple_of -> ordinal -> 'a1

val tnth : int -> 'a1 tuple_of -> ordinal -> 'a1

val tuple : int -> 'a1 tuple_of -> (__ -> 'a1 tuple_of) -> 'a1 tuple_of

val map_tuple : int -> ('a1 -> 'a2) -> 'a1 tuple_of -> 'a2 tuple_of

val tuple_eqMixin : int -> Equality.coq_type -> Equality.sort tuple_of Equality.mixin_of

val tuple_eqType : int -> Equality.coq_type -> Equality.coq_type

val enum_tuple : Finite.coq_type -> Finite.sort pred_sort -> Finite.sort tuple_of

val codom_tuple : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 tuple_of

type 'rT finfun_on =
| Finfun_nil
| Finfun_cons of Finite.sort * Finite.sort list * 'rT * 'rT finfun_on

val finfun_rec : Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort list -> 'a1 finfun_on

val fun_of_fin_rec : Finite.coq_type -> Equality.sort -> Finite.sort list -> 'a1 finfun_on -> 'a1

type 'rT finfun_of = 'rT finfun_on
  (* singleton inductive, whose constructor was FinfunOf *)

type 'rT dfinfun_of = 'rT finfun_of

val fun_of_fin : Finite.coq_type -> 'a1 finfun_of -> Equality.sort -> 'a1

module type FinfunDefSig =
 sig
  val finfun : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 finfun_of
 end

module FinfunDef :
 FinfunDefSig

val total_fun : Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort -> (Finite.sort, 'a1) sigT

val tfgraph : Finite.coq_type -> 'a1 finfun_of -> (Finite.sort, 'a1) sigT tuple_of

val tfgraph_inv : Finite.coq_type -> (Finite.sort, 'a1) sigT tuple_of -> 'a1 finfun_of option

val eqMixin :
  Finite.coq_type -> (Finite.sort -> Equality.coq_type) -> Equality.sort dfinfun_of Equality.mixin_of

val finfun_eqType : Finite.coq_type -> Equality.coq_type -> Equality.coq_type

type ('r, 'i) bigbody =
| BigBody of 'i * ('r -> 'r -> 'r) * bool * 'r

val applybig : ('a1, 'a2) bigbody -> 'a1 -> 'a1

val reducebig : 'a1 -> 'a2 list -> ('a2 -> ('a1, 'a2) bigbody) -> 'a1

module type BigOpSig =
 sig
  val bigop : 'a1 -> 'a2 list -> ('a2 -> ('a1, 'a2) bigbody) -> 'a1
 end

module BigOp :
 BigOpSig

val index_enum_key : unit

val index_enum : Finite.coq_type -> Finite.sort list

module GRing :
 sig
  module Zmodule :
   sig
    type 'v mixin_of = { zero : 'v; opp : ('v -> 'v); add : ('v -> 'v -> 'v) }

    val zero : 'a1 mixin_of -> 'a1

    val add : 'a1 mixin_of -> 'a1 -> 'a1 -> 'a1

    type 't class_of = { base : 't Choice.class_of; mixin : 't mixin_of }

    val mixin : 'a1 class_of -> 'a1 mixin_of

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    val coq_class : coq_type -> sort class_of
   end

  val zero : Zmodule.coq_type -> Zmodule.sort

  val add : Zmodule.coq_type -> Zmodule.sort -> Zmodule.sort -> Zmodule.sort

  module Ring :
   sig
    type mixin_of = { one : Zmodule.sort; mul : (Zmodule.sort -> Zmodule.sort -> Zmodule.sort) }

    val mul : Zmodule.coq_type -> mixin_of -> Zmodule.sort -> Zmodule.sort -> Zmodule.sort

    type 'r class_of = { base : 'r Zmodule.class_of; mixin : mixin_of }

    val base : 'a1 class_of -> 'a1 Zmodule.class_of

    val mixin : 'a1 class_of -> mixin_of

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    val coq_class : coq_type -> sort class_of

    val zmodType : coq_type -> Zmodule.coq_type
   end

  val mul : Ring.coq_type -> Ring.sort -> Ring.sort -> Ring.sort
 end

type 'r matrix = 'r finfun_of
  (* singleton inductive, whose constructor was Matrix *)

val mx_val : int -> int -> 'a1 matrix -> 'a1 finfun_of

val matrix_subType : int -> int -> 'a1 finfun_of subType

val matrix_of_fun_def : int -> int -> (Finite.sort -> Finite.sort -> 'a1) -> 'a1 matrix

val matrix_of_fun : int -> int -> unit -> (Finite.sort -> Finite.sort -> 'a1) -> 'a1 matrix

val fun_of_matrix : int -> int -> 'a1 matrix -> ordinal -> ordinal -> 'a1

val matrix_eqMixin : Equality.coq_type -> int -> int -> Equality.sort matrix Equality.mixin_of

val matrix_eqType : Equality.coq_type -> int -> int -> Equality.coq_type

val mulmx_key : unit

val mulmx :
  GRing.Ring.coq_type -> int -> int -> int -> GRing.Ring.sort matrix -> GRing.Ring.sort matrix ->
  GRing.Ring.sort matrix

module Coq2_MatrixThy :
 functor (F:FieldSig) ->
 sig
  module FieldThyInst :
   sig
   end

  module X_carrier_of_matrix :
   sig
    val coq_X_eqType : Equality.coq_type

    val pickle : F.coq_X -> int

    val unpickle : int -> F.coq_X option

    val coq_X_choiceType_mixin_of : F.coq_X Countable.mixin_of

    val coq_X_choiceType : Choice.coq_type

    val coq_X_zmodType : GRing.Zmodule.coq_type

    val coq_X_ringType : GRing.Ring.coq_type
   end

  type 'x mat = 'x matrix

  val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool

  val mnth' : int -> int -> F.coq_X mat -> int -> int -> F.coq_X

  val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X

  val mk_mat_1_1 : F.coq_X -> F.coq_X mat

  val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

  val mk_mat_3_3 :
    F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X ->
    F.coq_X mat

  val mk_mat_2_2 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

  val mat0 : int -> int -> F.coq_X mat

  val mat1 : int -> F.coq_X mat

  val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat

  val mmap2 :
    int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  val madd : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X matrix

  val mopp : int -> int -> F.coq_X mat -> F.coq_X mat

  val msub : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X matrix

  val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat

  val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat

  val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat

  val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

  val l2m : int -> int -> F.coq_X list list -> F.coq_X mat

  val finfun_on_to_dlist : int -> int -> F.coq_X finfun_on -> F.coq_X list list

  val m2l : int -> int -> F.coq_X mat -> F.coq_X list list

  val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat

  val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3

  val scalar_of_mat : F.coq_X mat -> F.coq_X

  val det_of_mat_3_3 : F.coq_X mat -> F.coq_X
 end

module MatrixAll :
 functor (F:FieldSig) ->
 sig
  module DP :
   sig
    type 'x mat = 'x Coq__2.mat

    val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X

    val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool

    val mk_mat_1_1 : F.coq_X -> F.coq_X mat

    val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

    val mk_mat_3_3 :
      F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X
      -> F.coq_X mat

    val mat0 : int -> int -> F.coq_X mat

    val mat1 : int -> F.coq_X mat

    val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat

    val mmap2 :
      int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    val madd : int -> int -> F.coq_X Coq__2.mat -> F.coq_X Coq__2.mat -> F.coq_X Coq__2.mat

    val mopp : int -> int -> F.coq_X mat -> F.coq_X mat

    val msub : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat

    val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat

    val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat

    val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    val l2m_old : int -> int -> F.coq_X list list -> F.coq_X mat

    val l2m : int -> int -> F.coq_X list list -> F.coq_X mat

    val m2l : int -> int -> F.coq_X mat -> F.coq_X list list

    val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat

    val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3

    val scalar_of_mat : F.coq_X mat -> F.coq_X
   end

  module DL :
   sig
    type 'x mat = 'x mat2

    val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool

    val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X

    val mk_mat_1_1 : F.coq_X -> F.coq_X mat

    val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

    val mk_mat_3_3 :
      F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X
      -> F.coq_X mat

    val mat0 : int -> int -> F.coq_X mat

    val mat1 : int -> F.coq_X mat

    val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat

    val mmap2 :
      int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    val madd : int -> int -> F.coq_X mat2 -> F.coq_X mat2 -> F.coq_X mat2

    val mopp : int -> int -> F.coq_X mat -> F.coq_X mat

    val msub : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat

    val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat

    val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat

    val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    val l2m : int -> int -> F.coq_X list list -> F.coq_X mat

    val m2l : int -> int -> F.coq_X mat -> F.coq_X list list

    val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat

    val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3

    val scalar_of_mat : F.coq_X mat -> F.coq_X

    val mget : F.coq_X -> int -> int -> F.coq_X mat2 -> int -> int -> F.coq_X

    val mset : F.coq_X -> int -> int -> F.coq_X mat2 -> int -> int -> F.coq_X -> F.coq_X mat2
   end

  module DR :
   sig
    module FieldThyInst :
     sig
     end

    type 'x mat = 'x mat5

    val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool

    val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X

    val mk_mat_1_1 : F.coq_X -> F.coq_X mat

    val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

    val mk_mat_3_3 :
      F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X
      -> F.coq_X mat

    val mk_mat_2_2 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

    val mat0 : int -> int -> F.coq_X mat

    val mat1 : int -> F.coq_X mat

    val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat

    val mmap2 :
      int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    val madd : int -> int -> F.coq_X mat5 -> F.coq_X mat5 -> F.coq_X mat5

    val mopp : int -> int -> F.coq_X mat -> F.coq_X mat

    val msub : int -> int -> F.coq_X mat5 -> F.coq_X mat5 -> F.coq_X mat5

    val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat

    val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat

    val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat

    val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    type vecr = F.coq_X mat

    type vecc = F.coq_X mat

    val mconsr : int -> int -> vecr -> F.coq_X mat -> F.coq_X mat

    val mconsc : int -> int -> vecc -> F.coq_X mat -> F.coq_X mat

    val l2m_old : int -> int -> F.coq_X list list -> F.coq_X mat

    val l2m : int -> int -> F.coq_X list list -> F.coq_X mat

    val m2l : int -> int -> F.coq_X mat -> F.coq_X list list

    val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat

    val m2t_3x3' : F.coq_X mat -> F.coq_X t_3x3

    val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3

    val scalar_of_mat : F.coq_X mat -> F.coq_X

    val det_of_mat_3_3 : F.coq_X mat -> F.coq_X
   end

  module NF :
   sig
    module FieldThyInst :
     sig
     end

    module SequenceInst :
     sig
      module FieldThyInst :
       sig
       end

      val seqeqb : int -> (int -> F.coq_X) -> (int -> F.coq_X) -> bool

      val seqeq_dec : int -> (int -> F.coq_X) -> (int -> F.coq_X) -> bool

      val seq2eqb : int -> int -> (int -> int -> F.coq_X) -> (int -> int -> F.coq_X) -> bool

      val seq2eq_dec : int -> int -> (int -> int -> F.coq_X) -> (int -> int -> F.coq_X) -> bool

      val seqsum : (int -> F.coq_X) -> int -> F.coq_X
     end

    type 'x coq_MATData = int -> int -> 'x

    type 'x mat' = 'x coq_MATData
      (* singleton inductive, whose constructor was mk_mat *)

    val mdata : int -> int -> 'a1 mat' -> 'a1 coq_MATData

    type 'x mat'' = 'x coq_MATData
      (* singleton inductive, whose constructor was mk_mat'' *)

    val mat''_rect : int -> int -> ('a1 coq_MATData -> 'a2) -> 'a1 mat'' -> 'a2

    val mat''_rec : int -> int -> ('a1 coq_MATData -> 'a2) -> 'a1 mat'' -> 'a2

    type 'x mat = 'x mat'

    val meq_dec_equiv : int -> int -> F.coq_X mat -> F.coq_X mat -> bool

    val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool

    val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X

    val mrow_aux : int -> int -> int -> int -> F.coq_X mat -> F.coq_X list

    val mrow : int -> int -> int -> F.coq_X mat -> F.coq_X list

    val l2m : int -> int -> F.coq_X list list -> F.coq_X mat

    val l2m' : F.coq_X list list -> F.coq_X mat

    val m2l_aux : int -> int -> int -> F.coq_X mat -> F.coq_X list list

    val m2l : int -> int -> F.coq_X mat -> F.coq_X list list

    val coq_MCol_aux : int -> int -> int -> int -> F.coq_X mat -> F.coq_X list

    val coq_MCol : int -> int -> int -> F.coq_X mat -> F.coq_X list

    val mshiftc : int -> int -> F.coq_X mat -> int -> F.coq_X mat

    val mk_mat_0_c : int -> F.coq_X mat

    val mk_mat_1_1 : F.coq_X -> F.coq_X mat

    val mk_mat_1_2 : F.coq_X -> F.coq_X -> F.coq_X mat

    val mk_mat_1_3 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

    val mk_mat_1_4 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

    val mk_mat_1_c : int -> F.coq_X list -> F.coq_X mat

    val mk_mat_r_0 : int -> F.coq_X mat

    val mk_mat_2_1 : F.coq_X -> F.coq_X -> F.coq_X mat

    val mk_mat_2_2 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

    val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

    val mk_mat_3_3 :
      F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X
      -> F.coq_X mat

    val mk_mat_4_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

    val mk_mat_4_4 :
      F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X
      -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

    val mk_mat_r_1 : int -> F.coq_X list -> F.coq_X mat

    val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat

    val mmap2 :
      int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    val mat0 : int -> int -> F.coq_X mat

    val mat1 : int -> F.coq_X mat

    val madd : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    val mopp : int -> int -> F.coq_X mat -> F.coq_X mat

    val msub : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat

    val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat

    val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat

    val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat

    val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3

    val scalar_of_mat : F.coq_X mat -> F.coq_X

    val trace : int -> F.coq_X mat -> F.coq_X
   end

  module FF :
   sig
    module FieldThyInst :
     sig
     end

    module X_carrier_of_matrix :
     sig
      val coq_X_eqType : Equality.coq_type

      val pickle : F.coq_X -> int

      val unpickle : int -> F.coq_X option

      val coq_X_choiceType_mixin_of : F.coq_X Countable.mixin_of

      val coq_X_choiceType : Choice.coq_type

      val coq_X_zmodType : GRing.Zmodule.coq_type

      val coq_X_ringType : GRing.Ring.coq_type
     end

    type 'x mat = 'x matrix

    val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool

    val mnth' : int -> int -> F.coq_X mat -> int -> int -> F.coq_X

    val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X

    val mk_mat_1_1 : F.coq_X -> F.coq_X mat

    val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

    val mk_mat_3_3 :
      F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X
      -> F.coq_X mat

    val mk_mat_2_2 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat

    val mat0 : int -> int -> F.coq_X mat

    val mat1 : int -> F.coq_X mat

    val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat

    val mmap2 :
      int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    val madd : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X matrix

    val mopp : int -> int -> F.coq_X mat -> F.coq_X mat

    val msub : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X matrix

    val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat

    val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat

    val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat

    val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat

    val l2m : int -> int -> F.coq_X list list -> F.coq_X mat

    val finfun_on_to_dlist : int -> int -> F.coq_X finfun_on -> F.coq_X list list

    val m2l : int -> int -> F.coq_X mat -> F.coq_X list list

    val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat

    val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3

    val scalar_of_mat : F.coq_X mat -> F.coq_X

    val det_of_mat_3_3 : F.coq_X mat -> F.coq_X
   end

  val dr2nf : int -> int -> F.coq_X DR.mat -> F.coq_X NF.mat

  val nf2dr : int -> int -> F.coq_X NF.mat -> F.coq_X DR.mat

  val dr2ff : int -> int -> F.coq_X DR.mat -> F.coq_X FF.mat

  val ff2dr : int -> int -> F.coq_X FF.mat -> F.coq_X DR.mat

  val dr2dp : int -> int -> F.coq_X DR.mat -> F.coq_X DP.mat

  val dp2dr : int -> int -> F.coq_X DP.mat -> F.coq_X DR.mat

  val dr2dl : int -> int -> F.coq_X DR.mat -> F.coq_X DL.mat

  val dl2dr : int -> int -> F.coq_X DL.mat -> F.coq_X DR.mat

  val nf2ff : int -> int -> F.coq_X NF.mat -> F.coq_X FF.mat

  val ff2nf : int -> int -> F.coq_X FF.mat -> F.coq_X NF.mat

  val nf2dp : int -> int -> F.coq_X NF.mat -> F.coq_X DP.mat

  val dp2nf : int -> int -> F.coq_X DP.mat -> F.coq_X NF.mat

  val nf2dl : int -> int -> F.coq_X NF.mat -> F.coq_X DL.mat

  val dl2nf : int -> int -> F.coq_X DL.mat -> F.coq_X NF.mat

  val ff2dp : int -> int -> F.coq_X FF.mat -> F.coq_X DP.mat

  val dp2ff : int -> int -> F.coq_X DP.mat -> F.coq_X FF.mat

  val ff2dl : int -> int -> F.coq_X FF.mat -> F.coq_X DL.mat

  val dl2ff : int -> int -> F.coq_X DL.mat -> F.coq_X FF.mat

  val dp2dl : int -> int -> F.coq_X DP.mat -> F.coq_X DL.mat

  val dl2dp : int -> int -> F.coq_X DL.mat -> F.coq_X DP.mat
 end

module MatrixAllR :
 sig
  module DP :
   sig
    type 'x mat = 'x Coq__2.mat

    val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

    val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

    val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mk_mat_3_1 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X mat

    val mk_mat_3_3 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X mat

    val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

    val mat1 : int -> FieldR.FieldDefR.coq_X mat

    val mmap :
      int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat
      -> FieldR.FieldDefR.coq_X mat

    val mmap2 :
      int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
      FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val madd :
      int -> int -> FieldR.FieldDefR.coq_X Coq__2.mat -> FieldR.FieldDefR.coq_X Coq__2.mat ->
      FieldR.FieldDefR.coq_X Coq__2.mat

    val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val msub :
      int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
      mat

    val mcmul :
      int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val mmulc :
      int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val mmul :
      int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
      FieldR.FieldDefR.coq_X mat

    val l2m_old : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

    val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

    val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

    val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

    val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

    val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
   end

  module DL :
   sig
    type 'x mat = 'x mat2

    val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

    val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

    val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mk_mat_3_1 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X mat

    val mk_mat_3_3 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X mat

    val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

    val mat1 : int -> FieldR.FieldDefR.coq_X mat

    val mmap :
      int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat
      -> FieldR.FieldDefR.coq_X mat

    val mmap2 :
      int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
      FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val madd :
      int -> int -> FieldR.FieldDefR.coq_X mat2 -> FieldR.FieldDefR.coq_X mat2 ->
      FieldR.FieldDefR.coq_X mat2

    val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val msub :
      int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
      mat

    val mcmul :
      int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val mmulc :
      int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val mmul :
      int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
      FieldR.FieldDefR.coq_X mat

    val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

    val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

    val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

    val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

    val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X

    val mget :
      FieldR.FieldDefR.coq_X -> int -> int -> FieldR.FieldDefR.coq_X mat2 -> int -> int ->
      FieldR.FieldDefR.coq_X

    val mset :
      FieldR.FieldDefR.coq_X -> int -> int -> FieldR.FieldDefR.coq_X mat2 -> int -> int ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat2
   end

  module DR :
   sig
    module FieldThyInst :
     sig
     end

    type 'x mat = 'x mat5

    val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

    val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

    val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mk_mat_3_1 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X mat

    val mk_mat_3_3 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X mat

    val mk_mat_2_2 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

    val mat1 : int -> FieldR.FieldDefR.coq_X mat

    val mmap :
      int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat
      -> FieldR.FieldDefR.coq_X mat

    val mmap2 :
      int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
      FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val madd :
      int -> int -> FieldR.FieldDefR.coq_X mat5 -> FieldR.FieldDefR.coq_X mat5 ->
      FieldR.FieldDefR.coq_X mat5

    val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val msub :
      int -> int -> FieldR.FieldDefR.coq_X mat5 -> FieldR.FieldDefR.coq_X mat5 ->
      FieldR.FieldDefR.coq_X mat5

    val mcmul :
      int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val mmulc :
      int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val mmul :
      int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
      FieldR.FieldDefR.coq_X mat

    type vecr = FieldR.FieldDefR.coq_X mat

    type vecc = FieldR.FieldDefR.coq_X mat

    val mconsr : int -> int -> vecr -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val mconsc : int -> int -> vecc -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val l2m_old : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

    val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

    val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

    val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

    val m2t_3x3' : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

    val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

    val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X

    val det_of_mat_3_3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
   end

  module NF :
   sig
    module FieldThyInst :
     sig
     end

    module SequenceInst :
     sig
      module FieldThyInst :
       sig
       end

      val seqeqb : int -> (int -> FieldR.FieldDefR.coq_X) -> (int -> FieldR.FieldDefR.coq_X) -> bool

      val seqeq_dec : int -> (int -> FieldR.FieldDefR.coq_X) -> (int -> FieldR.FieldDefR.coq_X) -> bool

      val seq2eqb :
        int -> int -> (int -> int -> FieldR.FieldDefR.coq_X) -> (int -> int -> FieldR.FieldDefR.coq_X)
        -> bool

      val seq2eq_dec :
        int -> int -> (int -> int -> FieldR.FieldDefR.coq_X) -> (int -> int -> FieldR.FieldDefR.coq_X)
        -> bool

      val seqsum : (int -> FieldR.FieldDefR.coq_X) -> int -> FieldR.FieldDefR.coq_X
     end

    type 'x coq_MATData = int -> int -> 'x

    type 'x mat' = 'x coq_MATData
      (* singleton inductive, whose constructor was mk_mat *)

    val mdata : int -> int -> 'a1 mat' -> 'a1 coq_MATData

    type 'x mat'' = 'x coq_MATData
      (* singleton inductive, whose constructor was mk_mat'' *)

    val mat''_rect : int -> int -> ('a1 coq_MATData -> 'a2) -> 'a1 mat'' -> 'a2

    val mat''_rec : int -> int -> ('a1 coq_MATData -> 'a2) -> 'a1 mat'' -> 'a2

    type 'x mat = 'x mat'

    val meq_dec_equiv : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

    val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

    val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

    val mrow_aux :
      int -> int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list

    val mrow : int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list

    val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

    val l2m' : FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

    val m2l_aux : int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

    val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

    val coq_MCol_aux :
      int -> int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list

    val coq_MCol : int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list

    val mshiftc : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> FieldR.FieldDefR.coq_X mat

    val mk_mat_0_c : int -> FieldR.FieldDefR.coq_X mat

    val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mk_mat_1_2 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mk_mat_1_3 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X mat

    val mk_mat_1_4 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mk_mat_1_c : int -> FieldR.FieldDefR.coq_X list -> FieldR.FieldDefR.coq_X mat

    val mk_mat_r_0 : int -> FieldR.FieldDefR.coq_X mat

    val mk_mat_2_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mk_mat_2_2 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mk_mat_3_1 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X mat

    val mk_mat_3_3 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X mat

    val mk_mat_4_1 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mk_mat_4_4 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mk_mat_r_1 : int -> FieldR.FieldDefR.coq_X list -> FieldR.FieldDefR.coq_X mat

    val mmap :
      int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat
      -> FieldR.FieldDefR.coq_X mat

    val mmap2 :
      int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
      FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

    val mat1 : int -> FieldR.FieldDefR.coq_X mat

    val madd :
      int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
      mat

    val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val msub :
      int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
      mat

    val mcmul :
      int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val mmulc :
      int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val mmul :
      int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
      FieldR.FieldDefR.coq_X mat

    val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

    val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

    val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X

    val trace : int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
   end

  module FF :
   sig
    module FieldThyInst :
     sig
     end

    module X_carrier_of_matrix :
     sig
      val coq_X_eqType : Equality.coq_type

      val pickle : FieldR.FieldDefR.coq_X -> int

      val unpickle : int -> FieldR.FieldDefR.coq_X option

      val coq_X_choiceType_mixin_of : FieldR.FieldDefR.coq_X Countable.mixin_of

      val coq_X_choiceType : Choice.coq_type

      val coq_X_zmodType : GRing.Zmodule.coq_type

      val coq_X_ringType : GRing.Ring.coq_type
     end

    type 'x mat = 'x matrix

    val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

    val mnth' : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

    val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

    val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mk_mat_3_1 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X mat

    val mk_mat_3_3 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X mat

    val mk_mat_2_2 :
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
      FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

    val mat1 : int -> FieldR.FieldDefR.coq_X mat

    val mmap :
      int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat
      -> FieldR.FieldDefR.coq_X mat

    val mmap2 :
      int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
      FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val madd :
      int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
      matrix

    val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val msub :
      int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
      matrix

    val mcmul :
      int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val mmulc :
      int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

    val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

    val mmul :
      int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
      FieldR.FieldDefR.coq_X mat

    val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

    val finfun_on_to_dlist :
      int -> int -> FieldR.FieldDefR.coq_X finfun_on -> FieldR.FieldDefR.coq_X list list

    val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

    val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

    val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

    val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X

    val det_of_mat_3_3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
   end

  val dr2nf : int -> int -> FieldR.FieldDefR.coq_X DR.mat -> FieldR.FieldDefR.coq_X NF.mat

  val nf2dr : int -> int -> FieldR.FieldDefR.coq_X NF.mat -> FieldR.FieldDefR.coq_X DR.mat

  val dr2ff : int -> int -> FieldR.FieldDefR.coq_X DR.mat -> FieldR.FieldDefR.coq_X FF.mat

  val ff2dr : int -> int -> FieldR.FieldDefR.coq_X FF.mat -> FieldR.FieldDefR.coq_X DR.mat

  val dr2dp : int -> int -> FieldR.FieldDefR.coq_X DR.mat -> FieldR.FieldDefR.coq_X DP.mat

  val dp2dr : int -> int -> FieldR.FieldDefR.coq_X DP.mat -> FieldR.FieldDefR.coq_X DR.mat

  val dr2dl : int -> int -> FieldR.FieldDefR.coq_X DR.mat -> FieldR.FieldDefR.coq_X DL.mat

  val dl2dr : int -> int -> FieldR.FieldDefR.coq_X DL.mat -> FieldR.FieldDefR.coq_X DR.mat

  val nf2ff : int -> int -> FieldR.FieldDefR.coq_X NF.mat -> FieldR.FieldDefR.coq_X FF.mat

  val ff2nf : int -> int -> FieldR.FieldDefR.coq_X FF.mat -> FieldR.FieldDefR.coq_X NF.mat

  val nf2dp : int -> int -> FieldR.FieldDefR.coq_X NF.mat -> FieldR.FieldDefR.coq_X DP.mat

  val dp2nf : int -> int -> FieldR.FieldDefR.coq_X DP.mat -> FieldR.FieldDefR.coq_X NF.mat

  val nf2dl : int -> int -> FieldR.FieldDefR.coq_X NF.mat -> FieldR.FieldDefR.coq_X DL.mat

  val dl2nf : int -> int -> FieldR.FieldDefR.coq_X DL.mat -> FieldR.FieldDefR.coq_X NF.mat

  val ff2dp : int -> int -> FieldR.FieldDefR.coq_X FF.mat -> FieldR.FieldDefR.coq_X DP.mat

  val dp2ff : int -> int -> FieldR.FieldDefR.coq_X DP.mat -> FieldR.FieldDefR.coq_X FF.mat

  val ff2dl : int -> int -> FieldR.FieldDefR.coq_X FF.mat -> FieldR.FieldDefR.coq_X DL.mat

  val dl2ff : int -> int -> FieldR.FieldDefR.coq_X DL.mat -> FieldR.FieldDefR.coq_X FF.mat

  val dp2dl : int -> int -> FieldR.FieldDefR.coq_X DP.mat -> FieldR.FieldDefR.coq_X DL.mat

  val dl2dp : int -> int -> FieldR.FieldDefR.coq_X DL.mat -> FieldR.FieldDefR.coq_X DP.mat
 end

module MatrixR_DR :
 sig
  module FieldThyInst :
   sig
   end

  type 'x mat = 'x mat5

  val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

  val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

  val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_3_1 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_3_3 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_2_2 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

  val mat1 : int -> FieldR.FieldDefR.coq_X mat

  val mmap :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val mmap2 :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
    FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val madd :
    int -> int -> FieldR.FieldDefR.coq_X mat5 -> FieldR.FieldDefR.coq_X mat5 -> FieldR.FieldDefR.coq_X
    mat5

  val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val msub :
    int -> int -> FieldR.FieldDefR.coq_X mat5 -> FieldR.FieldDefR.coq_X mat5 -> FieldR.FieldDefR.coq_X
    mat5

  val mcmul :
    int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmulc :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmul :
    int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  type vecr = FieldR.FieldDefR.coq_X mat

  type vecc = FieldR.FieldDefR.coq_X mat

  val mconsr : int -> int -> vecr -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mconsc : int -> int -> vecc -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val l2m_old : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

  val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

  val m2t_3x3' : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

  val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

  val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X

  val det_of_mat_3_3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
 end

module MatrixR_DP :
 sig
  type 'x mat = 'x Coq__2.mat

  val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

  val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

  val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_3_1 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_3_3 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

  val mat1 : int -> FieldR.FieldDefR.coq_X mat

  val mmap :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val mmap2 :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
    FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val madd :
    int -> int -> FieldR.FieldDefR.coq_X Coq__2.mat -> FieldR.FieldDefR.coq_X Coq__2.mat ->
    FieldR.FieldDefR.coq_X Coq__2.mat

  val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val msub :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
    mat

  val mcmul :
    int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmulc :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmul :
    int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val l2m_old : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

  val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

  val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

  val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
 end

module MatrixR_DL :
 sig
  type 'x mat = 'x mat2

  val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

  val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

  val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_3_1 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_3_3 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

  val mat1 : int -> FieldR.FieldDefR.coq_X mat

  val mmap :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val mmap2 :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
    FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val madd :
    int -> int -> FieldR.FieldDefR.coq_X mat2 -> FieldR.FieldDefR.coq_X mat2 -> FieldR.FieldDefR.coq_X
    mat2

  val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val msub :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
    mat

  val mcmul :
    int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmulc :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmul :
    int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

  val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

  val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

  val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X

  val mget :
    FieldR.FieldDefR.coq_X -> int -> int -> FieldR.FieldDefR.coq_X mat2 -> int -> int ->
    FieldR.FieldDefR.coq_X

  val mset :
    FieldR.FieldDefR.coq_X -> int -> int -> FieldR.FieldDefR.coq_X mat2 -> int -> int ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat2
 end

module MatrixR_NF :
 sig
  module FieldThyInst :
   sig
   end

  module SequenceInst :
   sig
    module FieldThyInst :
     sig
     end

    val seqeqb : int -> (int -> FieldR.FieldDefR.coq_X) -> (int -> FieldR.FieldDefR.coq_X) -> bool

    val seqeq_dec : int -> (int -> FieldR.FieldDefR.coq_X) -> (int -> FieldR.FieldDefR.coq_X) -> bool

    val seq2eqb :
      int -> int -> (int -> int -> FieldR.FieldDefR.coq_X) -> (int -> int -> FieldR.FieldDefR.coq_X)
      -> bool

    val seq2eq_dec :
      int -> int -> (int -> int -> FieldR.FieldDefR.coq_X) -> (int -> int -> FieldR.FieldDefR.coq_X)
      -> bool

    val seqsum : (int -> FieldR.FieldDefR.coq_X) -> int -> FieldR.FieldDefR.coq_X
   end

  type 'x coq_MATData = int -> int -> 'x

  type 'x mat' = 'x coq_MATData
    (* singleton inductive, whose constructor was mk_mat *)

  val mdata : int -> int -> 'a1 mat' -> 'a1 coq_MATData

  type 'x mat'' = 'x coq_MATData
    (* singleton inductive, whose constructor was mk_mat'' *)

  val mat''_rect : int -> int -> ('a1 coq_MATData -> 'a2) -> 'a1 mat'' -> 'a2

  val mat''_rec : int -> int -> ('a1 coq_MATData -> 'a2) -> 'a1 mat'' -> 'a2

  type 'x mat = 'x mat'

  val meq_dec_equiv : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

  val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

  val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

  val mrow_aux : int -> int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list

  val mrow : int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list

  val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val l2m' : FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val m2l_aux : int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

  val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

  val coq_MCol_aux :
    int -> int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list

  val coq_MCol : int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list

  val mshiftc : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> FieldR.FieldDefR.coq_X mat

  val mk_mat_0_c : int -> FieldR.FieldDefR.coq_X mat

  val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_1_2 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_1_3 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_1_4 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_1_c : int -> FieldR.FieldDefR.coq_X list -> FieldR.FieldDefR.coq_X mat

  val mk_mat_r_0 : int -> FieldR.FieldDefR.coq_X mat

  val mk_mat_2_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_2_2 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_3_1 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_3_3 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_4_1 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_4_4 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_r_1 : int -> FieldR.FieldDefR.coq_X list -> FieldR.FieldDefR.coq_X mat

  val mmap :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val mmap2 :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
    FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

  val mat1 : int -> FieldR.FieldDefR.coq_X mat

  val madd :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
    mat

  val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val msub :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
    mat

  val mcmul :
    int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmulc :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmul :
    int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

  val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

  val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X

  val trace : int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
 end

module MatrixR_FF :
 sig
  module FieldThyInst :
   sig
   end

  module X_carrier_of_matrix :
   sig
    val coq_X_eqType : Equality.coq_type

    val pickle : FieldR.FieldDefR.coq_X -> int

    val unpickle : int -> FieldR.FieldDefR.coq_X option

    val coq_X_choiceType_mixin_of : FieldR.FieldDefR.coq_X Countable.mixin_of

    val coq_X_choiceType : Choice.coq_type

    val coq_X_zmodType : GRing.Zmodule.coq_type

    val coq_X_ringType : GRing.Ring.coq_type
   end

  type 'x mat = 'x matrix

  val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

  val mnth' : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

  val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

  val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_3_1 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_3_3 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_2_2 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

  val mat1 : int -> FieldR.FieldDefR.coq_X mat

  val mmap :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val mmap2 :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
    FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val madd :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
    matrix

  val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val msub :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
    matrix

  val mcmul :
    int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmulc :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmul :
    int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val finfun_on_to_dlist :
    int -> int -> FieldR.FieldDefR.coq_X finfun_on -> FieldR.FieldDefR.coq_X list list

  val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

  val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

  val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

  val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X

  val det_of_mat_3_3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
 end

module DL :
 sig
  type 'x mat = 'x mat2

  val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

  val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

  val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_3_1 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_3_3 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

  val mat1 : int -> FieldR.FieldDefR.coq_X mat

  val mmap :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val mmap2 :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
    FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val madd :
    int -> int -> FieldR.FieldDefR.coq_X mat2 -> FieldR.FieldDefR.coq_X mat2 -> FieldR.FieldDefR.coq_X
    mat2

  val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val msub :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
    mat

  val mcmul :
    int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmulc :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmul :
    int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

  val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

  val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

  val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X

  val mget :
    FieldR.FieldDefR.coq_X -> int -> int -> FieldR.FieldDefR.coq_X mat2 -> int -> int ->
    FieldR.FieldDefR.coq_X

  val mset :
    FieldR.FieldDefR.coq_X -> int -> int -> FieldR.FieldDefR.coq_X mat2 -> int -> int ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat2
 end

module DP :
 sig
  type 'x mat = 'x Coq__2.mat

  val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

  val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

  val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_3_1 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_3_3 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

  val mat1 : int -> FieldR.FieldDefR.coq_X mat

  val mmap :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val mmap2 :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
    FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val madd :
    int -> int -> FieldR.FieldDefR.coq_X Coq__2.mat -> FieldR.FieldDefR.coq_X Coq__2.mat ->
    FieldR.FieldDefR.coq_X Coq__2.mat

  val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val msub :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
    mat

  val mcmul :
    int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmulc :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmul :
    int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val l2m_old : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

  val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

  val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

  val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
 end

module DR :
 sig
  module FieldThyInst :
   sig
   end

  type 'x mat = 'x mat5

  val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

  val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

  val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_3_1 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_3_3 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_2_2 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

  val mat1 : int -> FieldR.FieldDefR.coq_X mat

  val mmap :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val mmap2 :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
    FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val madd :
    int -> int -> FieldR.FieldDefR.coq_X mat5 -> FieldR.FieldDefR.coq_X mat5 -> FieldR.FieldDefR.coq_X
    mat5

  val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val msub :
    int -> int -> FieldR.FieldDefR.coq_X mat5 -> FieldR.FieldDefR.coq_X mat5 -> FieldR.FieldDefR.coq_X
    mat5

  val mcmul :
    int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmulc :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmul :
    int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  type vecr = FieldR.FieldDefR.coq_X mat

  type vecc = FieldR.FieldDefR.coq_X mat

  val mconsr : int -> int -> vecr -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mconsc : int -> int -> vecc -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val l2m_old : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

  val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

  val m2t_3x3' : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

  val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

  val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X

  val det_of_mat_3_3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
 end

module NF :
 sig
  module FieldThyInst :
   sig
   end

  module SequenceInst :
   sig
    module FieldThyInst :
     sig
     end

    val seqeqb : int -> (int -> FieldR.FieldDefR.coq_X) -> (int -> FieldR.FieldDefR.coq_X) -> bool

    val seqeq_dec : int -> (int -> FieldR.FieldDefR.coq_X) -> (int -> FieldR.FieldDefR.coq_X) -> bool

    val seq2eqb :
      int -> int -> (int -> int -> FieldR.FieldDefR.coq_X) -> (int -> int -> FieldR.FieldDefR.coq_X)
      -> bool

    val seq2eq_dec :
      int -> int -> (int -> int -> FieldR.FieldDefR.coq_X) -> (int -> int -> FieldR.FieldDefR.coq_X)
      -> bool

    val seqsum : (int -> FieldR.FieldDefR.coq_X) -> int -> FieldR.FieldDefR.coq_X
   end

  type 'x coq_MATData = int -> int -> 'x

  type 'x mat' = 'x coq_MATData
    (* singleton inductive, whose constructor was mk_mat *)

  val mdata : int -> int -> 'a1 mat' -> 'a1 coq_MATData

  type 'x mat'' = 'x coq_MATData
    (* singleton inductive, whose constructor was mk_mat'' *)

  val mat''_rect : int -> int -> ('a1 coq_MATData -> 'a2) -> 'a1 mat'' -> 'a2

  val mat''_rec : int -> int -> ('a1 coq_MATData -> 'a2) -> 'a1 mat'' -> 'a2

  type 'x mat = 'x mat'

  val meq_dec_equiv : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

  val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

  val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

  val mrow_aux : int -> int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list

  val mrow : int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list

  val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val l2m' : FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val m2l_aux : int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

  val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

  val coq_MCol_aux :
    int -> int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list

  val coq_MCol : int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list

  val mshiftc : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> FieldR.FieldDefR.coq_X mat

  val mk_mat_0_c : int -> FieldR.FieldDefR.coq_X mat

  val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_1_2 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_1_3 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_1_4 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_1_c : int -> FieldR.FieldDefR.coq_X list -> FieldR.FieldDefR.coq_X mat

  val mk_mat_r_0 : int -> FieldR.FieldDefR.coq_X mat

  val mk_mat_2_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_2_2 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_3_1 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_3_3 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_4_1 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_4_4 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_r_1 : int -> FieldR.FieldDefR.coq_X list -> FieldR.FieldDefR.coq_X mat

  val mmap :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val mmap2 :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
    FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

  val mat1 : int -> FieldR.FieldDefR.coq_X mat

  val madd :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
    mat

  val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val msub :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
    mat

  val mcmul :
    int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmulc :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmul :
    int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

  val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

  val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X

  val trace : int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
 end

module FF :
 sig
  module FieldThyInst :
   sig
   end

  module X_carrier_of_matrix :
   sig
    val coq_X_eqType : Equality.coq_type

    val pickle : FieldR.FieldDefR.coq_X -> int

    val unpickle : int -> FieldR.FieldDefR.coq_X option

    val coq_X_choiceType_mixin_of : FieldR.FieldDefR.coq_X Countable.mixin_of

    val coq_X_choiceType : Choice.coq_type

    val coq_X_zmodType : GRing.Zmodule.coq_type

    val coq_X_ringType : GRing.Ring.coq_type
   end

  type 'x mat = 'x matrix

  val meq_dec : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> bool

  val mnth' : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

  val mnth : int -> int -> FieldR.FieldDefR.coq_X mat -> int -> int -> FieldR.FieldDefR.coq_X

  val mk_mat_1_1 : FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mk_mat_3_1 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_3_3 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X mat

  val mk_mat_2_2 :
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X ->
    FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mat0 : int -> int -> FieldR.FieldDefR.coq_X mat

  val mat1 : int -> FieldR.FieldDefR.coq_X mat

  val mmap :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val mmap2 :
    int -> int -> (FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X) ->
    FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val madd :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
    matrix

  val mopp : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val msub :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
    matrix

  val mcmul :
    int -> int -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmulc :
    int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X -> FieldR.FieldDefR.coq_X mat

  val mtrans : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat

  val mmul :
    int -> int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X mat ->
    FieldR.FieldDefR.coq_X mat

  val l2m : int -> int -> FieldR.FieldDefR.coq_X list list -> FieldR.FieldDefR.coq_X mat

  val finfun_on_to_dlist :
    int -> int -> FieldR.FieldDefR.coq_X finfun_on -> FieldR.FieldDefR.coq_X list list

  val m2l : int -> int -> FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X list list

  val t2m_3x3 : FieldR.FieldDefR.coq_X t_3x3 -> FieldR.FieldDefR.coq_X mat

  val m2t_3x3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X t_3x3

  val scalar_of_mat : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X

  val det_of_mat_3_3 : FieldR.FieldDefR.coq_X mat -> FieldR.FieldDefR.coq_X
 end
