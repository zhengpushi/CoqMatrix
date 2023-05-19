
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

module Coq__1 = struct
 (** val add : int -> int -> int **)let rec add = (+)
end
include Coq__1

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m0 -> mul n (pow n m0))
      m
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val size_nat : positive -> int **)

  let rec size_nat = function
  | XI p0 -> Stdlib.Int.succ (size_nat p0)
  | XO p0 -> Stdlib.Int.succ (size_nat p0)
  | XH -> Stdlib.Int.succ 0

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val ggcdn :
      int -> positive -> positive -> positive * (positive * positive) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (XH, (a, b)))
      (fun n0 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> (a, (XH, XH))
            | Lt ->
              let (g, p) = ggcdn n0 (sub b' a') a in
              let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
            | Gt ->
              let (g, p) = ggcdn n0 (sub a' b') b in
              let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
         | XO b0 ->
           let (g, p) = ggcdn n0 a b0 in let (aa, bb) = p in (g, (aa, (XO bb)))
         | XH -> (XH, (a, XH)))
      | XO a0 ->
        (match b with
         | XI _ ->
           let (g, p) = ggcdn n0 a0 b in let (aa, bb) = p in (g, ((XO aa), bb))
         | XO b0 -> let (g, p) = ggcdn n0 a0 b0 in ((XO g), p)
         | XH -> (XH, (a, XH)))
      | XH -> (XH, (XH, b)))
      n

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.Int.succ 0)

  (** val of_nat : int -> positive **)

  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> XH)
        (fun _ -> succ (of_nat x))
        x)
      n

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Coq_Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val to_nat : z -> int **)

  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> 0

  (** val of_nat : int -> z **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Z0)
      (fun n0 -> Zpos (Coq_Pos.of_succ_nat n0))
      n

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val ggcd : z -> z -> z * (z * z) **)

  let ggcd a b =
    match a with
    | Z0 -> ((abs b), (Z0, (sgn b)))
    | Zpos a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zneg bb))))
 end

type q = { qnum : z; qden : positive }

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

module RbaseSymbolsImpl =
 struct
  type coq_R = float

  (** val coq_Rabst : cReal -> dReal **)

  let coq_Rabst = __

  (** val coq_Rrepr : dReal -> cReal **)

  let coq_Rrepr = __

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 =
    __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 =
    __

  (** val coq_R0 : coq_R **)

  let coq_R0 = 0.0

  (** val coq_R1 : coq_R **)

  let coq_R1 = 1.0

  (** val coq_Rplus : coq_R -> coq_R -> coq_R **)

  let coq_Rplus = (+.)

  (** val coq_Rmult : coq_R -> coq_R -> coq_R **)

  let coq_Rmult = ( *. )

  (** val coq_Ropp : coq_R -> coq_R **)

  let coq_Ropp = fun a -> (0.0 -. a)

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def =
    __

  (** val coq_R1_def : __ **)

  let coq_R1_def =
    __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def =
    __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def =
    __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def =
    __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def =
    __
 end

(** val iPR_2 : positive -> RbaseSymbolsImpl.coq_R **)

let rec iPR_2 = function
| XI p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1)
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0))
| XO p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1)
    (iPR_2 p0)
| XH -> RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1

(** val iPR : positive -> RbaseSymbolsImpl.coq_R **)

let iPR = function
| XI p0 -> RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0)
| XO p0 -> iPR_2 p0
| XH -> RbaseSymbolsImpl.coq_R1

(** val iZR : z -> RbaseSymbolsImpl.coq_R **)

let iZR = function
| Z0 -> RbaseSymbolsImpl.coq_R0
| Zpos n -> iPR n
| Zneg n -> RbaseSymbolsImpl.coq_Ropp (iPR n)

(** val ex2 : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let ex2 x =
  RbaseSymbolsImpl.coq_Rplus x (iZR (Zpos (XO (XO XH))))

