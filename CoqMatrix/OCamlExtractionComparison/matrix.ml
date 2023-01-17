
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

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

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h



(** val pred : int -> int **)

let pred = fun n -> Stdlib.max 0 (n-1)

module Coq__1 = struct
 (** val add : int -> int -> int **)let rec add = (+)
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

type reflect =
| ReflectT
| ReflectF

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

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Stdlib.Int.succ n) m

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
    | XI p -> (match y with
               | XI q0 -> XO (add_carry p q0)
               | XO q0 -> XI (add p q0)
               | XH -> XO (succ p))
    | XO p -> (match y with
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
    | XO p -> (match y with
               | XI q0 -> XO (add_carry p q0)
               | XO q0 -> XI (add p q0)
               | XH -> XO (succ p))
    | XH -> (match y with
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
    | XI p -> (match y with
               | XI q0 -> compare_cont r p q0
               | XO q0 -> compare_cont Gt p q0
               | XH -> Gt)
    | XO p -> (match y with
               | XI q0 -> compare_cont Lt p q0
               | XO q0 -> compare_cont r p q0
               | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val ggcdn : int -> positive -> positive -> positive * (positive * positive) **)

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
              let (g, p) = ggcdn n0 (sub b' a') a in let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
            | Gt ->
              let (g, p) = ggcdn n0 (sub a' b') b in let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
         | XO b0 -> let (g, p) = ggcdn n0 a b0 in let (aa, bb) = p in (g, (aa, (XO bb)))
         | XH -> (XH, (a, XH)))
      | XO a0 ->
        (match b with
         | XI _ -> let (g, p) = ggcdn n0 a0 b in let (aa, bb) = p in (g, ((XO aa), bb))
         | XO b0 -> let (g, p) = ggcdn n0 a0 b0 in ((XO g), p)
         | XH -> (XH, (a, XH)))
      | XH -> (XH, (XH, b)))
      n

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op0 p a =
    match p with
    | XI p0 -> op0 a (iter_op op0 p0 (op0 a a))
    | XO p0 -> iter_op op0 p0 (op0 a a)
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

(** val hd : 'a1 -> 'a1 list -> 'a1 **)

let hd default0 = function
| [] -> default0
| x :: _ -> x

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| [] -> []
| _ :: m -> m

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> default0
              | x :: _ -> x)
    (fun m -> match l with
              | [] -> default0
              | _ :: t1 -> nth m t1 default0)
    n

(** val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec0 l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | y :: l0 ->
    (match l' with
     | [] -> false
     | a :: l1 -> if eq_dec0 y a then list_eq_dec eq_dec0 l0 l1 else false)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t1 -> (f a) :: (map f t1)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t1 -> f b (fold_right f a0 t1)

(** val repeat : 'a1 -> int -> 'a1 list **)

let rec repeat x n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun k -> x :: (repeat x k))
    n

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
    | XH -> (match y with
             | XI q0 -> Zneg (XO q0)
             | XO q0 -> Zneg (Coq_Pos.pred_double q0)
             | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' -> (match y with
                  | Z0 -> x
                  | Zpos y' -> Zpos (Coq_Pos.add x' y')
                  | Zneg y' -> pos_sub x' y')
    | Zneg x' -> (match y with
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
    | Zneg x' -> (match y with
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

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
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
         let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zneg bb))))
 end

type q = { qnum : z; qden : positive }

type t =
| F1 of int
| FS of int * t

(** val eqb : int -> int -> t -> t -> bool **)

let rec eqb _ _ p q0 =
  match p with
  | F1 m' -> (match q0 with
              | F1 n' -> (=) m' n'
              | FS (_, _) -> false)
  | FS (n0, p') -> (match q0 with
                    | F1 _ -> false
                    | FS (n1, q') -> eqb n0 n1 p' q')

(** val eq_dec : int -> t -> t -> bool **)

let eq_dec n x y =
  if eqb n n x y then true else false

type 'a t0 =
| Nil
| Cons of 'a * int * 'a t0

(** val case0 : 'a2 -> 'a1 t0 -> 'a2 **)

let case0 h = function
| Nil -> h
| Cons (x, x0, x1) -> Obj.magic __ x x0 x1

(** val caseS : ('a1 -> int -> 'a1 t0 -> 'a2) -> int -> 'a1 t0 -> 'a2 **)

let caseS h _ = function
| Nil -> Obj.magic __
| Cons (h0, n0, t1) -> h h0 n0 t1

(** val caseS' : int -> 'a1 t0 -> ('a1 -> 'a1 t0 -> 'a2) -> 'a2 **)

let caseS' _ v h =
  match v with
  | Nil -> Obj.magic __ __ h
  | Cons (h0, _, t1) -> h h0 t1

(** val rect2 :
    'a3 -> (int -> 'a1 t0 -> 'a2 t0 -> 'a3 -> 'a1 -> 'a2 -> 'a3) -> int -> 'a1 t0 -> 'a2 t0 -> 'a3 **)

let rec rect2 bas rect _ v1 v2 =
  match v1 with
  | Nil -> case0 bas v2
  | Cons (h1, n', t1) -> caseS' n' v2 (fun h2 t4 -> rect n' t1 t4 (rect2 bas rect n' t1 t4) h1 h2)

(** val hd0 : int -> 'a1 t0 -> 'a1 **)

let hd0 n =
  caseS (fun h _ _ -> h) n

(** val const : 'a1 -> int -> 'a1 t0 **)

let rec const a n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Nil)
    (fun n0 -> Cons (a, n0, (const a n0)))
    n

(** val nth0 : int -> 'a1 t0 -> t -> 'a1 **)

let rec nth0 _ v' = function
| F1 n -> caseS (fun h _ _ -> h) n v'
| FS (n, p') -> caseS (fun _ -> nth0) n v' p'

(** val tl0 : int -> 'a1 t0 -> 'a1 t0 **)

let tl0 n =
  caseS (fun _ _ t1 -> t1) n

(** val map2 : ('a1 -> 'a2 -> 'a3) -> int -> 'a1 t0 -> 'a2 t0 -> 'a3 t0 **)

let map2 g =
  rect2 Nil (fun n _ _ h a b -> Cons ((g a b), n, h))

(** val fold_left : ('a2 -> 'a1 -> 'a2) -> 'a2 -> int -> 'a1 t0 -> 'a2 **)

let rec fold_left f b _ = function
| Nil -> b
| Cons (a, n0, w) -> fold_left f (f b a) n0 w

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
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1) (iPR_2 p0)
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

(** val total_order_T : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool option **)

let total_order_T = fun r1 r2 ->   let c = Float.compare r1 r2 in   if c < 0 then Some true   else (if c = 0 then None else Some false)

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl =
 struct
  (** val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Rinv = fun a -> (1.0 /. a)

  (** val coq_Rinv_def : __ **)

  let coq_Rinv_def =
    __
 end

(** val req_EM_T : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let req_EM_T r1 r2 =
  let s = total_order_T r1 r2 in (match s with
                                  | Some a -> if a then false else true
                                  | None -> false)

(** val reqb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let reqb r1 r2 =
  if req_EM_T r1 r2 then true else false

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

module FieldThy =
 functor (F:FieldSig) ->
 struct
 end

module FieldR =
 struct
  module FieldDefR =
   struct
    type coq_X = RbaseSymbolsImpl.coq_R

    (** val coq_X0 : RbaseSymbolsImpl.coq_R **)

    let coq_X0 =
      iZR Z0

    (** val coq_X1 : RbaseSymbolsImpl.coq_R **)

    let coq_X1 =
      iZR (Zpos XH)

    (** val coq_Xadd : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

    let coq_Xadd =
      RbaseSymbolsImpl.coq_Rplus

    (** val coq_Xopp : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

    let coq_Xopp =
      RbaseSymbolsImpl.coq_Ropp

    (** val coq_Xmul : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

    let coq_Xmul =
      RbaseSymbolsImpl.coq_Rmult

    (** val coq_Xinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

    let coq_Xinv =
      RinvImpl.coq_Rinv

    (** val coq_Xeqb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

    let coq_Xeqb =
      reqb

    (** val coq_Xeqdec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

    let coq_Xeqdec =
      req_EM_T

    (** val coq_Xeqb_true_iff : __ **)

    let coq_Xeqb_true_iff =
      __

    (** val coq_Xeqb_false_iff : __ **)

    let coq_Xeqb_false_iff =
      __

    (** val coq_X1_neq_X0 : __ **)

    let coq_X1_neq_X0 =
      __

    (** val coq_Ring_thy : __ **)

    let coq_Ring_thy =
      __

    (** val coq_Ring_thy_inst_ring_lemma1 : __ **)

    let coq_Ring_thy_inst_ring_lemma1 =
      __

    (** val coq_Ring_thy_inst_ring_lemma2 : __ **)

    let coq_Ring_thy_inst_ring_lemma2 =
      __

    (** val coq_Field_thy : __ **)

    let coq_Field_thy =
      __

    (** val coq_Field_thy_inst_ring_lemma1 : __ **)

    let coq_Field_thy_inst_ring_lemma1 =
      __

    (** val coq_Field_thy_inst_ring_lemma2 : __ **)

    let coq_Field_thy_inst_ring_lemma2 =
      __

    (** val coq_Field_thy_inst_field_lemma1 : __ **)

    let coq_Field_thy_inst_field_lemma1 =
      __

    (** val coq_Field_thy_inst_field_lemma2 : __ **)

    let coq_Field_thy_inst_field_lemma2 =
      __

    (** val coq_Field_thy_inst_field_lemma3 : __ **)

    let coq_Field_thy_inst_field_lemma3 =
      __

    (** val coq_Field_thy_inst_field_lemma4 : __ **)

    let coq_Field_thy_inst_field_lemma4 =
      __

    (** val coq_Field_thy_inst_lemma5 : __ **)

    let coq_Field_thy_inst_lemma5 =
      __
   end
 end

type 'a t2 = 'a * 'a

type 'a t3 = 'a t2 * 'a

type 'a t_3x3 = ('a t3 * 'a t3) * 'a t3

(** val lzero : 'a1 -> int -> 'a1 list **)

let lzero =
  repeat

(** val map0 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec map0 f l1 l2 =
  match l1 with
  | [] -> []
  | x1 :: t1 -> (match l2 with
                 | [] -> []
                 | x2 :: t4 -> (f x1 x2) :: (map0 f t1 t4))

(** val ldot : 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 list -> 'a1 list -> 'a1 **)

let ldot a0 add0 mul0 l1 l2 =
  fold_right add0 a0 (map0 mul0 l1 l2)

(** val dlist_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list list -> 'a1 list list -> bool **)

let dlist_eq_dec aeq_dec =
  list_eq_dec (list_eq_dec aeq_dec)

(** val dnil : int -> 'a1 list list **)

let rec dnil n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' -> [] :: (dnil n'))
    n

(** val cvt_row2col : 'a1 list -> 'a1 list list **)

let rec cvt_row2col = function
| [] -> []
| x :: tl1 -> (x :: []) :: (cvt_row2col tl1)

(** val hdc : 'a1 -> 'a1 list list -> 'a1 list **)

let rec hdc a0 = function
| [] -> []
| l :: tl1 -> (hd a0 l) :: (hdc a0 tl1)

(** val consc : 'a1 list -> 'a1 list list -> 'a1 list list **)

let rec consc l dl =
  match l with
  | [] -> []
  | xl :: tl1 -> (match dl with
                  | [] -> []
                  | xdl :: tdl -> (xl :: xdl) :: (consc tl1 tdl))

(** val dlzero : 'a1 -> int -> int -> 'a1 list list **)

let dlzero a0 r c =
  repeat (lzero a0 c) r

(** val dlunit : 'a1 -> 'a1 -> int -> 'a1 list list **)

let rec dlunit a0 a1 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n0 -> (a1 :: (repeat a0 n0)) :: (consc (repeat a0 n0) (dlunit a0 a1 n0)))
    n

(** val dltrans : 'a1 list list -> int -> 'a1 list list **)

let rec dltrans dl c =
  match dl with
  | [] -> dnil c
  | l :: tl1 -> consc l (dltrans tl1 c)

(** val dmap : ('a1 -> 'a2) -> 'a1 list list -> 'a2 list list **)

let dmap f dl =
  map (map f) dl

(** val dmap2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list list -> 'a2 list list -> 'a3 list list **)

let dmap2 f dl1 dl2 =
  map0 (map0 f) dl1 dl2

(** val ldotdl :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 list -> 'a1 list list -> 'a1 list **)

let rec ldotdl a0 add0 mul0 l = function
| [] -> []
| h :: t1 -> (ldot a0 add0 mul0 l h) :: (ldotdl a0 add0 mul0 l t1)

(** val dldotdl :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 list list -> 'a1 list list -> 'a1 list
    list **)

let rec dldotdl a0 add0 mul0 dl1 dl2 =
  match dl1 with
  | [] -> []
  | h1 :: t1 -> (ldotdl a0 add0 mul0 h1 dl2) :: (dldotdl a0 add0 mul0 t1 dl2)

type 't vec = __

(** val vec_eq_dec : ('a1 -> 'a1 -> bool) -> int -> 'a1 vec -> 'a1 vec -> bool **)

let rec vec_eq_dec teq_dec n v1 v2 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n0 ->
    let (a, b) = Obj.magic v1 in
    let (a0, b0) = Obj.magic v2 in
    let s = vec_eq_dec teq_dec n0 b b0 in if s then teq_dec a a0 else false)
    n

(** val vrepeat : int -> 'a1 -> 'a1 vec **)

let rec vrepeat n val1 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun n' -> Obj.magic (val1, (vrepeat n' val1)))
    n

(** val vmake_aux : int -> int -> (int -> 'a1) -> 'a1 vec **)

let rec vmake_aux n i f =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun n' -> Obj.magic ((f i), (vmake_aux n' (Stdlib.Int.succ i) f)))
    n

(** val vmake : int -> (int -> 'a1) -> 'a1 vec **)

let vmake n f =
  vmake_aux n 0 f

(** val vnth : 'a1 -> int -> int -> 'a1 vec -> 'a1 **)

let rec vnth t1 n i x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> t1)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> fst (Obj.magic x))
      (fun i' -> vnth t1 n' i' (snd (Obj.magic x)))
      i)
    n

(** val vmap : ('a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec **)

let rec vmap f n v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun n' -> Obj.magic ((f (fst (Obj.magic v))), (vmap f n' (snd (Obj.magic v)))))
    n

(** val vmap2 : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1 vec **)

let rec vmap2 f n v1 v2 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun n' ->
    Obj.magic ((f (fst (Obj.magic v1)) (fst (Obj.magic v2))),
      (vmap2 f n' (snd (Obj.magic v1)) (snd (Obj.magic v2)))))
    n

(** val vadd : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1 vec **)

let vadd =
  vmap2

(** val vopp : ('a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec **)

let vopp =
  vmap

(** val vfoldl : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 vec -> 'a1 **)

let rec vfoldl fadd n init_val v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> init_val)
    (fun n' -> fadd (fst (Obj.magic v)) (vfoldl fadd n' init_val (snd (Obj.magic v))))
    n

(** val vdot :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1 **)

let vdot t1 fadd fmul n v1 v2 =
  vfoldl fadd n t1 (vmap2 fmul n v1 v2)

(** val v2l : int -> 'a1 vec -> 'a1 list **)

let rec v2l n v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' -> (fst (Obj.magic v)) :: (v2l n' (snd (Obj.magic v))))
    n

(** val l2v : 'a1 -> 'a1 list -> int -> 'a1 vec **)

let rec l2v a0 l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun n' -> Obj.magic ((hd a0 l), (l2v a0 (tl l) n')))
    n

module Coq__2 = struct
 type 't mat = 't vec vec
end
include Coq__2

(** val mmake : int -> int -> (int -> int -> 'a1) -> 'a1 mat **)

let mmake r c f =
  vmake r (fun ic -> vmake c (f ic))

(** val mnth : 'a1 -> int -> int -> 'a1 mat -> int -> int -> 'a1 **)

let mnth t1 r c m ir ic =
  vnth t1 c ic (vnth (vrepeat c t1) r ir m)

(** val mat0 : 'a1 -> int -> int -> 'a1 mat **)

let mat0 t1 r c =
  mmake r c (fun _ _ -> t1)

(** val mmap : ('a1 -> 'a1) -> int -> int -> 'a1 mat -> 'a1 mat **)

let rec mmap f r c m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun r' -> Obj.magic ((vmap f c (fst (Obj.magic m))), (mmap f r' c (snd (Obj.magic m)))))
    r

(** val mmap2 : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat -> 'a1 mat -> 'a1 mat **)

let rec mmap2 f r c m1 m2 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun r' ->
    Obj.magic ((vmap2 f c (fst (Obj.magic m1)) (fst (Obj.magic m2))),
      (mmap2 f r' c (snd (Obj.magic m1)) (snd (Obj.magic m2)))))
    r

(** val mconsr : int -> int -> 'a1 vec -> 'a1 vec vec -> 'a1 vec vec **)

let mconsr _ _ v m =
  Obj.magic (v, m)

(** val mconsc : int -> int -> 'a1 vec -> 'a1 vec vec -> 'a1 vec vec **)

let rec mconsc r c v m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun r' ->
    Obj.magic (((fst (Obj.magic v)), (fst (Obj.magic m))),
      (mconsc r' c (snd (Obj.magic v)) (snd (Obj.magic m)))))
    r

(** val mhdc : int -> int -> 'a1 mat -> 'a1 vec **)

let rec mhdc r c m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun r' -> Obj.magic ((fst (fst (Obj.magic m))), (mhdc r' c (snd (Obj.magic m)))))
    r

(** val mtlc : int -> int -> 'a1 mat -> 'a1 mat **)

let rec mtlc r c m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun r' -> Obj.magic ((snd (fst (Obj.magic m))), (mtlc r' c (snd (Obj.magic m)))))
    r

(** val mat1 : 'a1 -> 'a1 -> int -> 'a1 mat **)

let rec mat1 t1 t4 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> let mat'0 = () in Obj.magic mat'0)
    (fun n' ->
    let row' = (t4, (vrepeat n' t1)) in
    let mat'0 = mat1 t1 t4 n' in
    mconsr n' (Stdlib.Int.succ n') (Obj.magic row') (mconsc n' n' (vrepeat n' t1) mat'0))
    n

(** val madd : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat -> 'a1 mat -> 'a1 mat **)

let madd fadd r c m1 m2 =
  vmap2 (vadd fadd c) r m1 m2

(** val mopp : ('a1 -> 'a1) -> int -> int -> 'a1 mat -> 'a1 mat **)

let mopp fopp r c m =
  vmap (vopp fopp c) r m

(** val msub : ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat -> 'a1 mat -> 'a1 mat **)

let msub fopp fadd r c m1 m2 =
  madd fadd r c m1 (mopp fopp r c m2)

(** val mcmul : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 mat -> 'a1 mat **)

let mcmul fmul r c a m =
  mmap (fun x -> fmul a x) r c m

(** val mmulc : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat -> 'a1 -> 'a1 mat **)

let mmulc fmul r c m a =
  mmap (fun x -> fmul x a) r c m

(** val mtrans : int -> int -> 'a1 mat -> 'a1 mat **)

let rec mtrans r c m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun c' -> Obj.magic ((mhdc r c' m), (mtrans r c' (mtlc r c' m))))
    c

(** val vdotm :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 vec -> 'a1 mat -> 'a1 vec **)

let rec vdotm t1 fadd fmul r c v m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun r' ->
    Obj.magic ((vdot t1 fadd fmul c v (fst (Obj.magic m))),
      (vdotm t1 fadd fmul r' c v (snd (Obj.magic m)))))
    r

(** val mdot :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> int -> 'a1 mat -> 'a1 mat ->
    'a1 mat **)

let rec mdot t1 fadd fmul r c t4 m1 m2 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun r' ->
    Obj.magic ((vdotm t1 fadd fmul t4 c (fst (Obj.magic m1)) m2),
      (mdot t1 fadd fmul r' c t4 (snd (Obj.magic m1)) m2)))
    r

(** val mmul :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> int -> 'a1 mat -> 'a1 mat ->
    'a1 mat **)

let mmul t1 fadd fmul r c s m1 m2 =
  mdot t1 fadd fmul r c s m1 (mtrans c s m2)

(** val m2l : int -> int -> 'a1 mat -> 'a1 list list **)

let rec m2l r c m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun r' -> (v2l c (fst (Obj.magic m))) :: (m2l r' c (snd (Obj.magic m))))
    r

(** val l2m : 'a1 -> 'a1 list list -> int -> int -> 'a1 mat **)

let rec l2m a0 dl r c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun n' -> Obj.magic ((l2v a0 (hd [] dl) c), (l2m a0 (tl dl) n' c)))
    r

module MatrixThy =
 functor (F:FieldSig) ->
 struct
  type 'x mat = 'x Coq__2.mat

  (** val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X **)

  let mnth r c m ri ci =
    mnth F.coq_X0 r c m ri ci

  (** val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool **)

  let meq_dec r c m1 m2 =
    vec_eq_dec (vec_eq_dec F.coq_Xeqdec c) r m1 m2

  (** val mk_mat_1_1 : F.coq_X -> F.coq_X mat **)

  let mk_mat_1_1 a11 =
    Obj.magic ((a11, ()), ())

  (** val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_3_1 a1 a2 a3 =
    Obj.magic ((a1, ()), ((a2, ()), ((a3, ()), ())))

  (** val mk_mat_3_3 :
      F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X
      -> F.coq_X mat **)

  let mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 =
    Obj.magic ((a11, (a12, (a13, ()))), ((a21, (a22, (a23, ()))), ((a31, (a32, (a33, ()))), ())))

  (** val mat0 : int -> int -> F.coq_X mat **)

  let mat0 r c =
    mat0 F.coq_X0 r c

  (** val mat1 : int -> F.coq_X mat **)

  let mat1 n =
    mat1 F.coq_X0 F.coq_X1 n

  (** val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat **)

  let mmap r c f m =
    mmap f r c m

  (** val mmap2 :
      int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let mmap2 r c f m1 m2 =
    mmap2 f r c m1 m2

  (** val madd : int -> int -> F.coq_X Coq__2.mat -> F.coq_X Coq__2.mat -> F.coq_X Coq__2.mat **)

  let madd r c =
    madd F.coq_Xadd r c

  (** val mopp : int -> int -> F.coq_X mat -> F.coq_X mat **)

  let mopp r c m =
    mopp F.coq_Xopp r c m

  (** val msub : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let msub r c m1 m2 =
    msub F.coq_Xopp F.coq_Xadd r c m1 m2

  (** val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat **)

  let mcmul r c a m =
    mcmul F.coq_Xmul r c a m

  (** val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat **)

  let mmulc r c m a =
    mmulc F.coq_Xmul r c m a

  (** val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat **)

  let mtrans =
    mtrans

  (** val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let mmul r c s m1 m2 =
    mmul F.coq_X0 F.coq_Xadd F.coq_Xmul r c s m1 m2

  (** val l2m_old : int -> int -> F.coq_X list list -> F.coq_X mat **)

  let l2m_old r c dl =
    mmake r c (fun x y -> nth y (nth x dl []) F.coq_X0)

  (** val l2m : int -> int -> F.coq_X list list -> F.coq_X mat **)

  let l2m r c dl =
    l2m F.coq_X0 dl r c

  (** val m2l : int -> int -> F.coq_X mat -> F.coq_X list list **)

  let m2l =
    m2l

  (** val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat **)

  let t2m_3x3 = function
  | (a, b) ->
    let (a0, b0) = a in
    let (a1, b1) = a0 in
    let (a2, b2) = a1 in
    let (a3, b3) = b0 in
    let (a4, b4) = a3 in let (a5, b5) = b in let (a6, b6) = a5 in mk_mat_3_3 a2 b2 b1 a4 b4 b3 a6 b6 b5

  (** val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3 **)

  let m2t_3x3 m =
    let dl =
      m2l (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m
    in
    let l1 = hd [] dl in
    let l2 = hd [] (tl dl) in
    let l3 = hd [] (tl (tl dl)) in
    let t1 = (((hd F.coq_X0 l1), (hd F.coq_X0 (tl l1))), (hd F.coq_X0 (tl (tl l1)))) in
    let t4 = (((hd F.coq_X0 l2), (hd F.coq_X0 (tl l2))), (hd F.coq_X0 (tl (tl l2)))) in
    let t5 = (((hd F.coq_X0 l3), (hd F.coq_X0 (tl l3))), (hd F.coq_X0 (tl (tl l3)))) in ((t1, t4), t5)

  (** val scalar_of_mat : F.coq_X mat -> F.coq_X **)

  let scalar_of_mat m =
    mnth (Stdlib.Int.succ 0) (Stdlib.Int.succ 0) m 0 0
 end

(** val fin_gen : int -> int -> t option **)

let rec fin_gen n i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Some (F1 n'))
      (fun i' -> let a = fin_gen n' i' in (match a with
                                           | Some x -> Some (FS (n', x))
                                           | None -> None))
      i)
    n

(** val vec_S : int -> 'a1 t0 -> ('a1, 'a1 t0) sigT **)

let vec_S _ = function
| Nil -> Obj.magic __
| Cons (x, _, v') -> ExistT (x, v')

(** val veq_dec : ('a1 -> 'a1 -> bool) -> int -> 'a1 t0 -> 'a1 t0 -> bool **)

let rec veq_dec teq_dec n v1 v2 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n0 ->
    let x = vec_S n0 v1 in
    let ExistT (x0, p) = x in
    let x1 = vec_S n0 v2 in
    let ExistT (x2, p0) = x1 in let s = veq_dec teq_dec n0 p p0 in if s then teq_dec x0 x2 else false)
    n

(** val vmake0 : int -> (t -> 'a1) -> 'a1 t0 **)

let rec vmake0 n x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Nil)
    (fun n' -> Cons ((x (F1 n')), n', (vmake0 n' (fun fn' -> x (FS (n', fn'))))))
    n

(** val vget : 'a1 -> int -> 'a1 t0 -> int -> 'a1 **)

let rec vget a0 _ v i =
  match v with
  | Nil -> a0
  | Cons (a, n0, v') ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> a)
       (fun i' -> vget a0 n0 v' i')
       i)

(** val vset : int -> 'a1 t0 -> int -> 'a1 -> 'a1 t0 **)

let rec vset _ v i x =
  match v with
  | Nil -> Nil
  | Cons (a, n0, v') ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> Cons (x, n0, v'))
       (fun i' -> Cons (a, n0, (vset n0 v' i' x)))
       i)

type 'a mat2 = 'a t0 t0

(** val meq_dec0 : ('a1 -> 'a1 -> bool) -> int -> int -> 'a1 mat2 -> 'a1 mat2 -> bool **)

let rec meq_dec0 aeq_dec r c m1 m2 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n ->
    let x = vec_S n m1 in
    let ExistT (x0, p) = x in
    let x1 = vec_S n m2 in
    let ExistT (x2, p0) = x1 in
    let s = meq_dec0 aeq_dec n c p p0 in if s then veq_dec aeq_dec c x0 x2 else false)
    r

(** val mcoli : int -> int -> 'a1 mat2 -> t -> 'a1 t0 **)

let mcoli r c m fc =
  vmake0 r (fun fr -> nth0 c (nth0 r m fr) fc)

(** val mnth0 : int -> int -> 'a1 mat2 -> t -> t -> 'a1 **)

let mnth0 r c m fr fc =
  nth0 c (nth0 r m fr) fc

(** val mget : 'a1 -> int -> int -> 'a1 mat2 -> int -> int -> 'a1 **)

let mget a0 r c m i j =
  vget a0 c (vget (const a0 c) r m i) j

(** val mset : 'a1 -> int -> int -> 'a1 mat2 -> int -> int -> 'a1 -> 'a1 mat2 **)

let mset a0 r c m i j x =
  vset r m i (vset c (vget (const a0 c) r m i) j x)

(** val mat3 : 'a1 -> int -> int -> 'a1 mat2 **)

let mat3 a0 r c =
  vmake0 r (fun _ -> vmake0 c (fun _ -> a0))

(** val mat4 : 'a1 -> 'a1 -> int -> 'a1 mat2 **)

let mat4 a0 a1 n =
  vmake0 n (fun fr -> vmake0 n (fun fc -> if eq_dec n fr fc then a1 else a0))

(** val mtrans0 : int -> int -> 'a1 mat2 -> 'a1 mat2 **)

let mtrans0 r c m =
  vmake0 c (fun fc -> vmake0 r (fun fr -> nth0 c (nth0 r m fr) fc))

(** val vdot0 : 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 t0 -> 'a1 t0 -> 'a1 **)

let vdot0 a0 fadd fmul n v1 v2 =
  fold_left fadd a0 n (map2 fmul n v1 v2)

(** val mmap0 : ('a1 -> 'a1) -> int -> int -> 'a1 mat2 -> 'a1 mat2 **)

let mmap0 f r c m =
  vmake0 r (fun fr -> vmake0 c (fun fc -> f (mnth0 r c m fr fc)))

(** val mmap1 : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat2 -> 'a1 mat2 -> 'a1 mat2 **)

let mmap1 f r c m1 m2 =
  vmake0 r (fun fr -> vmake0 c (fun fc -> f (mnth0 r c m1 fr fc) (mnth0 r c m2 fr fc)))

(** val mopp0 : ('a1 -> 'a1) -> int -> int -> 'a1 mat2 -> 'a1 mat2 **)

let mopp0 fopp r c m =
  vmake0 r (fun fr -> vmake0 c (fun fc -> fopp (mnth0 r c m fr fc)))

(** val madd0 : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat2 -> 'a1 mat2 -> 'a1 mat2 **)

let madd0 fadd r c m1 m2 =
  vmake0 r (fun fr -> vmake0 c (fun fc -> fadd (mnth0 r c m1 fr fc) (mnth0 r c m2 fr fc)))

(** val msub0 : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat2 -> 'a1 mat2 -> 'a1 mat2 **)

let msub0 fsub r c m1 m2 =
  vmake0 r (fun fr -> vmake0 c (fun fc -> fsub (mnth0 r c m1 fr fc) (mnth0 r c m2 fr fc)))

(** val mcmul0 : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 mat2 -> 'a1 mat2 **)

let mcmul0 fmul r c a m =
  vmake0 r (fun fr -> vmake0 c (fun fc -> fmul a (mnth0 r c m fr fc)))

(** val mmulc0 : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat2 -> 'a1 -> 'a1 mat2 **)

let mmulc0 fmul r c m a =
  vmake0 r (fun fr -> vmake0 c (fun fc -> fmul (mnth0 r c m fr fc) a))

(** val mmul0 :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> int -> 'a1 mat2 -> 'a1 mat2 ->
    'a1 mat2 **)

let mmul0 a0 fadd fmul r s c m1 m2 =
  vmake0 r (fun fr -> vmake0 c (fun fc -> vdot0 a0 fadd fmul s (nth0 r m1 fr) (mcoli s c m2 fc)))

(** val v2l0 : int -> 'a1 t0 -> 'a1 list **)

let rec v2l0 _ = function
| Nil -> []
| Cons (x, n0, v') -> x :: (v2l0 n0 v')

(** val l2v0 : 'a1 -> 'a1 list -> int -> 'a1 t0 **)

let rec l2v0 a0 l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Nil)
    (fun n' -> Cons ((hd a0 l), n', (l2v0 a0 (tl l) n')))
    n

(** val m2l0 : int -> int -> 'a1 mat2 -> 'a1 list list **)

let rec m2l0 _ c = function
| Nil -> []
| Cons (x, n, v') -> (v2l0 c x) :: (m2l0 n c v')

(** val l2m0 : 'a1 -> 'a1 list list -> int -> int -> 'a1 mat2 **)

let rec l2m0 a0 dl r c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Nil)
    (fun n' -> Cons ((l2v0 a0 (hd [] dl) c), n', (l2m0 a0 (tl dl) n' c)))
    r

module Coq_MatrixThy =
 functor (F:FieldSig) ->
 struct
  type 'x mat = 'x mat2

  (** val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool **)

  let meq_dec =
    meq_dec0 F.coq_Xeqdec

  (** val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X **)

  let mnth r c m ri ci =
    let fri = fin_gen r ri in
    let fci = fin_gen c ci in
    (match fri with
     | Some fri' -> (match fci with
                     | Some fci' -> mnth0 r c m fri' fci'
                     | None -> F.coq_X0)
     | None -> F.coq_X0)

  (** val mk_mat_1_1 : F.coq_X -> F.coq_X mat **)

  let mk_mat_1_1 a11 =
    Cons ((Cons (a11, 0, Nil)), 0, Nil)

  (** val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_3_1 a1 a2 a3 =
    Cons ((Cons (a1, 0, Nil)), (Stdlib.Int.succ (Stdlib.Int.succ 0)), (Cons ((Cons (a2, 0, Nil)),
      (Stdlib.Int.succ 0), (Cons ((Cons (a3, 0, Nil)), 0, Nil)))))

  (** val mk_mat_3_3 :
      F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X
      -> F.coq_X mat **)

  let mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 =
    Cons ((Cons (a11, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (Cons (a12, (Stdlib.Int.succ 0), (Cons
      (a13, 0, Nil)))))), (Stdlib.Int.succ (Stdlib.Int.succ 0)), (Cons ((Cons (a21, (Stdlib.Int.succ
      (Stdlib.Int.succ 0)), (Cons (a22, (Stdlib.Int.succ 0), (Cons (a23, 0, Nil)))))),
      (Stdlib.Int.succ 0), (Cons ((Cons (a31, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (Cons (a32,
      (Stdlib.Int.succ 0), (Cons (a33, 0, Nil)))))), 0, Nil)))))

  (** val mat0 : int -> int -> F.coq_X mat **)

  let mat0 r c =
    mat3 F.coq_X0 r c

  (** val mat1 : int -> F.coq_X mat **)

  let mat1 n =
    mat4 F.coq_X0 F.coq_X1 n

  (** val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat **)

  let mmap r c f m =
    mmap0 f r c m

  (** val mmap2 :
      int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let mmap2 r c f m1 m2 =
    mmap1 f r c m1 m2

  (** val madd : int -> int -> F.coq_X mat2 -> F.coq_X mat2 -> F.coq_X mat2 **)

  let madd r c =
    madd0 F.coq_Xadd r c

  (** val mopp : int -> int -> F.coq_X mat -> F.coq_X mat **)

  let mopp r c m =
    mopp0 F.coq_Xopp r c m

  (** val msub : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let msub r c m1 m2 =
    msub0 (fun x y -> F.coq_Xadd x (F.coq_Xopp y)) r c m1 m2

  (** val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat **)

  let mcmul r c a m =
    mcmul0 F.coq_Xmul r c a m

  (** val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat **)

  let mmulc r c m a =
    mmulc0 F.coq_Xmul r c m a

  (** val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat **)

  let mtrans =
    mtrans0

  (** val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let mmul r c s m1 m2 =
    mmul0 F.coq_X0 F.coq_Xadd F.coq_Xmul r c s m1 m2

  (** val l2m : int -> int -> F.coq_X list list -> F.coq_X mat **)

  let l2m r c dl =
    l2m0 F.coq_X0 dl r c

  (** val m2l : int -> int -> F.coq_X mat -> F.coq_X list list **)

  let m2l =
    m2l0

  (** val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat **)

  let t2m_3x3 = function
  | (a, b) ->
    let (a0, b0) = a in
    let (a1, b1) = a0 in
    let (a2, b2) = a1 in
    let (a3, b3) = b0 in
    let (a4, b4) = a3 in let (a5, b5) = b in let (a6, b6) = a5 in mk_mat_3_3 a2 b2 b1 a4 b4 b3 a6 b6 b5

  (** val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3 **)

  let m2t_3x3 m =
    let l1 = hd0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) m in
    let l2 = hd0 (Stdlib.Int.succ 0) (tl0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) m) in
    let l3 = hd0 0 (tl0 (Stdlib.Int.succ 0) (tl0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) m)) in
    let t1 = (((hd0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) l1),
      (hd0 (Stdlib.Int.succ 0) (tl0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) l1))),
      (hd0 0 (tl0 (Stdlib.Int.succ 0) (tl0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) l1))))
    in
    let t4 = (((hd0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) l2),
      (hd0 (Stdlib.Int.succ 0) (tl0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) l2))),
      (hd0 0 (tl0 (Stdlib.Int.succ 0) (tl0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) l2))))
    in
    let t5 = (((hd0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) l3),
      (hd0 (Stdlib.Int.succ 0) (tl0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) l3))),
      (hd0 0 (tl0 (Stdlib.Int.succ 0) (tl0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) l3))))
    in
    ((t1, t4), t5)

  (** val scalar_of_mat : F.coq_X mat -> F.coq_X **)

  let scalar_of_mat m =
    mnth (Stdlib.Int.succ 0) (Stdlib.Int.succ 0) m 0 0

  (** val mget : F.coq_X -> int -> int -> F.coq_X mat2 -> int -> int -> F.coq_X **)

  let mget =
    mget

  (** val mset : F.coq_X -> int -> int -> F.coq_X mat2 -> int -> int -> F.coq_X -> F.coq_X mat2 **)

  let mset =
    mset
 end

type 'a mat5 = 'a list list
  (* singleton inductive, whose constructor was mk_mat *)

(** val mat_data : int -> int -> 'a1 mat5 -> 'a1 list list **)

let mat_data _ _ m =
  m

(** val mk_mat_1_0 : 'a1 -> 'a1 mat5 **)

let mk_mat_1_0 a =
  (a :: []) :: []

(** val mk_mat_r_1 : 'a1 list -> int -> 'a1 mat5 **)

let mk_mat_r_1 l _ =
  cvt_row2col l

(** val mk_mat_3_0 : 'a1 -> 'a1 -> 'a1 -> 'a1 mat5 **)

let mk_mat_3_0 a1 a2 a3 =
  mk_mat_r_1 (a1 :: (a2 :: (a3 :: []))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))

(** val mk_mat_2_2 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 mat5 **)

let mk_mat_2_2 a11 a12 a21 a22 =
  (a11 :: (a12 :: [])) :: ((a21 :: (a22 :: [])) :: [])

(** val mk_mat_3_2 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 mat5 **)

let mk_mat_3_2 a11 a12 a13 a21 a22 a23 a31 a32 a33 =
  (a11 :: (a12 :: (a13 :: []))) :: ((a21 :: (a22 :: (a23 :: []))) :: ((a31 :: (a32 :: (a33 :: []))) :: []))

(** val mat_nth : 'a1 -> int -> int -> 'a1 mat5 -> int -> int -> 'a1 **)

let mat_nth a0 r c m ri ci =
  nth ci (nth ri (mat_data r c m) []) a0

(** val matmapdl : ('a1 -> 'a2) -> int -> int -> 'a1 mat5 -> 'a2 list list **)

let matmapdl f r c m =
  dmap f (mat_data r c m)

(** val matmap2dl : ('a1 -> 'a2 -> 'a3) -> int -> int -> 'a1 mat5 -> 'a2 mat5 -> 'a3 list list **)

let matmap2dl f r c m1 m2 =
  dmap2 f (mat_data r c m1) (mat_data r c m2)

(** val matmap : ('a1 -> 'a2) -> int -> int -> 'a1 mat5 -> 'a2 mat5 **)

let matmap =
  matmapdl

(** val matmap2 : ('a1 -> 'a2 -> 'a3) -> int -> int -> 'a1 mat5 -> 'a2 mat5 -> 'a3 mat5 **)

let matmap2 =
  matmap2dl

(** val matzero : 'a1 -> int -> int -> 'a1 mat5 **)

let matzero =
  dlzero

(** val matunit : 'a1 -> 'a1 -> int -> 'a1 mat5 **)

let matunit =
  dlunit

(** val mat_trans : int -> int -> 'a1 mat5 -> 'a1 mat5 **)

let mat_trans r c m =
  let dl = mat_data r c m in dltrans dl c

(** val matadd : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat5 -> 'a1 mat5 -> 'a1 mat5 **)

let matadd =
  matmap2

(** val matopp : ('a1 -> 'a1) -> int -> int -> 'a1 mat5 -> 'a1 mat5 **)

let matopp =
  matmap

(** val matsub :
    ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat5 -> 'a1 mat5 -> 'a1 mat5 **)

let matsub opp0 add0 r c m1 m2 =
  matmap2 (fun x y -> add0 x (opp0 y)) r c m1 m2

(** val matmul :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> int -> 'a1 mat5 -> 'a1 mat5 ->
    'a1 mat5 **)

let matmul a0 add0 mul0 r c t1 m1 m2 =
  dldotdl a0 add0 mul0 (mat_data r c m1) (mat_data t1 c (mat_trans c t1 m2))

(** val matcmul : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 mat5 -> 'a1 mat5 **)

let matcmul mul0 r c a m =
  dmap (fun x -> mul0 a x) (mat_data r c m)

(** val matmulc : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 mat5 -> 'a1 -> 'a1 mat5 **)

let matmulc mul0 r c m a =
  dmap (fun x -> mul0 x a) (mat_data r c m)

(** val l2v_aux : 'a1 -> 'a1 list -> int -> 'a1 list **)

let rec l2v_aux a0 l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' -> (hd a0 l) :: (l2v_aux a0 (tl l) n'))
    n

(** val l2m_aux : 'a1 -> 'a1 list list -> int -> int -> 'a1 list list **)

let rec l2m_aux a0 dl r c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' -> (l2v_aux a0 (hd [] dl) c) :: (l2m_aux a0 (tl dl) n' c))
    r

(** val l2m1 : 'a1 -> 'a1 list list -> int -> int -> 'a1 mat5 **)

let l2m1 =
  l2m_aux

module Coq0_MatrixThy =
 functor (F:FieldSig) ->
 struct
  module FieldThyInst = FieldThy(F)

  type 'x mat = 'x mat5

  (** val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool **)

  let meq_dec =
    let internal_eq_rew_dep = fun _ f _ -> f in
    (fun r _ m1 m2 ->
    let h = dlist_eq_dec F.coq_Xeqdec m1 m2 in
    if h then internal_eq_rew_dep (length m1) (fun _ -> true) r __ else false)

  (** val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X **)

  let mnth r c m ri ci =
    mat_nth F.coq_X0 r c m ri ci

  (** val mk_mat_1_1 : F.coq_X -> F.coq_X mat **)

  let mk_mat_1_1 =
    mk_mat_1_0

  (** val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_3_1 =
    mk_mat_3_0

  (** val mk_mat_3_3 :
      F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X
      -> F.coq_X mat **)

  let mk_mat_3_3 =
    mk_mat_3_2

  (** val mk_mat_2_2 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_2_2 =
    mk_mat_2_2

  (** val mat0 : int -> int -> F.coq_X mat **)

  let mat0 r c =
    matzero F.coq_X0 r c

  (** val mat1 : int -> F.coq_X mat **)

  let mat1 n =
    matunit F.coq_X0 F.coq_X1 n

  (** val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat **)

  let mmap r c f m =
    matmap f r c m

  (** val mmap2 :
      int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let mmap2 r c f m1 m2 =
    matmap2 f r c m1 m2

  (** val madd : int -> int -> F.coq_X mat5 -> F.coq_X mat5 -> F.coq_X mat5 **)

  let madd r c =
    matadd F.coq_Xadd r c

  (** val mopp : int -> int -> F.coq_X mat -> F.coq_X mat **)

  let mopp r c m =
    matopp F.coq_Xopp r c m

  (** val msub : int -> int -> F.coq_X mat5 -> F.coq_X mat5 -> F.coq_X mat5 **)

  let msub r c =
    matsub F.coq_Xopp F.coq_Xadd r c

  (** val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat **)

  let mcmul r c a m =
    matcmul F.coq_Xmul r c a m

  (** val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat **)

  let mmulc r c m a =
    matmulc F.coq_Xmul r c m a

  (** val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat **)

  let mtrans =
    mat_trans

  (** val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let mmul r c s m1 m2 =
    matmul F.coq_X0 F.coq_Xadd F.coq_Xmul r c s m1 m2

  type vecr = F.coq_X mat

  type vecc = F.coq_X mat

  (** val mconsr : int -> int -> vecr -> F.coq_X mat -> F.coq_X mat **)

  let mconsr _ _ v m =
    (hd [] v) :: m

  (** val mconsc : int -> int -> vecc -> F.coq_X mat -> F.coq_X mat **)

  let mconsc _ _ v m =
    consc (hdc F.coq_X0 v) m

  (** val l2m_old : int -> int -> F.coq_X list list -> F.coq_X mat **)

  let l2m_old _ _ dl =
    dl

  (** val l2m : int -> int -> F.coq_X list list -> F.coq_X mat **)

  let l2m r c dl =
    l2m1 F.coq_X0 dl r c

  (** val m2l : int -> int -> F.coq_X mat -> F.coq_X list list **)

  let m2l =
    mat_data

  (** val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat **)

  let t2m_3x3 = function
  | (a, b) ->
    let (a0, b0) = a in
    let (a1, b1) = a0 in
    let (a2, b2) = a1 in
    let (a3, b3) = b0 in
    let (a4, b4) = a3 in let (a5, b5) = b in let (a6, b6) = a5 in mk_mat_3_3 a2 b2 b1 a4 b4 b3 a6 b6 b5

  (** val m2t_3x3' : F.coq_X mat -> F.coq_X t_3x3 **)

  let m2t_3x3' m =
    (((((mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ 0))) m 0 0),
      (mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m 0 (Stdlib.Int.succ 0))),
      (mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m 0 (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
      (((mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ 0))) m (Stdlib.Int.succ 0) 0),
      (mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m (Stdlib.Int.succ 0) (Stdlib.Int.succ 0))),
      (mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m (Stdlib.Int.succ 0) (Stdlib.Int.succ (Stdlib.Int.succ 0))))),
      (((mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ 0))) m (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0),
      (mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))),
      (mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))

  (** val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3 **)

  let m2t_3x3 m =
    let l1 = hd [] m in
    let l2 = hd [] (tl m) in
    let l3 = hd [] (tl (tl m)) in
    let t1 = (((hd F.coq_X0 l1), (hd F.coq_X0 (tl l1))), (hd F.coq_X0 (tl (tl l1)))) in
    let t4 = (((hd F.coq_X0 l2), (hd F.coq_X0 (tl l2))), (hd F.coq_X0 (tl (tl l2)))) in
    let t5 = (((hd F.coq_X0 l3), (hd F.coq_X0 (tl l3))), (hd F.coq_X0 (tl (tl l3)))) in ((t1, t4), t5)

  (** val scalar_of_mat : F.coq_X mat -> F.coq_X **)

  let scalar_of_mat m =
    mnth (Stdlib.Int.succ 0) (Stdlib.Int.succ 0) m 0 0

  (** val det_of_mat_3_3 : F.coq_X mat -> F.coq_X **)

  let det_of_mat_3_3 m =
    let (p, t1) = m2t_3x3 m in
    let (t4, t5) = p in
    let (t6, a13) = t4 in
    let (a11, a12) = t6 in
    let (t7, a23) = t5 in
    let (a21, a22) = t7 in
    let (t8, a33) = t1 in
    let (a31, a32) = t8 in
    let b1 = F.coq_Xmul (F.coq_Xmul a11 a22) a33 in
    let b2 = F.coq_Xmul (F.coq_Xmul a12 a23) a31 in
    let b3 = F.coq_Xmul (F.coq_Xmul a13 a21) a32 in
    let c1 = F.coq_Xmul (F.coq_Xmul a11 a23) a32 in
    let c2 = F.coq_Xmul (F.coq_Xmul a12 a21) a33 in
    let c3 = F.coq_Xmul (F.coq_Xmul a13 a22) a31 in
    let b = F.coq_Xadd (F.coq_Xadd b1 b2) b3 in
    let c = F.coq_Xadd (F.coq_Xadd c1 c2) c3 in F.coq_Xadd b (F.coq_Xopp c)
 end

module Sequence =
 functor (F:FieldSig) ->
 struct
  module FieldThyInst = FieldThy(F)

  (** val seqeqb : int -> (int -> F.coq_X) -> (int -> F.coq_X) -> bool **)

  let rec seqeqb n f g =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> F.coq_Xeqb (f 0) (g 0))
        (fun _ -> (&&) (seqeqb n' f g) (F.coq_Xeqb (f n') (g n')))
        n')
      n

  (** val seqeq_dec : int -> (int -> F.coq_X) -> (int -> F.coq_X) -> bool **)

  let seqeq_dec n f g =
    let b = seqeqb n f g in if b then true else false

  (** val seq2eqb : int -> int -> (int -> int -> F.coq_X) -> (int -> int -> F.coq_X) -> bool **)

  let rec seq2eqb r c f g =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun r' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> seqeqb c (f 0) (g 0))
        (fun _ -> (&&) (seq2eqb r' c f g) (seqeqb c (f r') (g r')))
        r')
      r

  (** val seq2eq_dec : int -> int -> (int -> int -> F.coq_X) -> (int -> int -> F.coq_X) -> bool **)

  let seq2eq_dec r c f g =
    let b = seq2eqb r c f g in if b then true else false

  (** val seqsum : (int -> F.coq_X) -> int -> F.coq_X **)

  let rec seqsum f n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> F.coq_X0)
      (fun n' -> F.coq_Xadd (seqsum f n') (f n'))
      n
 end

module Coq1_MatrixThy =
 functor (F:FieldSig) ->
 struct
  module FieldThyInst = FieldThy(F)

  module SequenceInst = Sequence(F)

  type 'x coq_MATData = int -> int -> 'x

  type 'x mat' = 'x coq_MATData
    (* singleton inductive, whose constructor was mk_mat *)

  (** val mdata : int -> int -> 'a1 mat' -> 'a1 coq_MATData **)

  let mdata _ _ m =
    m

  type 'x mat'' = 'x coq_MATData
    (* singleton inductive, whose constructor was mk_mat'' *)

  (** val mat''_rect : int -> int -> ('a1 coq_MATData -> 'a2) -> 'a1 mat'' -> 'a2 **)

  let mat''_rect _ _ f =
    f

  (** val mat''_rec : int -> int -> ('a1 coq_MATData -> 'a2) -> 'a1 mat'' -> 'a2 **)

  let mat''_rec _ _ f =
    f

  type 'x mat = 'x mat'

  (** val meq_dec_equiv : int -> int -> F.coq_X mat -> F.coq_X mat -> bool **)

  let meq_dec_equiv r c m1 m2 =
    SequenceInst.seq2eq_dec r c (mdata r c m1) (mdata r c m2)

  (** val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool **)

  let meq_dec =
    meq_dec_equiv

  (** val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X **)

  let mnth =
    mdata

  (** val mrow_aux : int -> int -> int -> int -> F.coq_X mat -> F.coq_X list **)

  let rec mrow_aux r c ri cnt m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> [])
      (fun c' -> let g = mdata r c m in (g ri cnt) :: (mrow_aux r c' ri (Stdlib.Int.succ cnt) g))
      c

  (** val mrow : int -> int -> int -> F.coq_X mat -> F.coq_X list **)

  let mrow r c ri m =
    mrow_aux r c ri 0 m

  (** val l2m : int -> int -> F.coq_X list list -> F.coq_X mat **)

  let l2m _ _ dl x y =
    nth y (nth x dl []) F.coq_X0

  (** val l2m' : F.coq_X list list -> F.coq_X mat **)

  let l2m' dl x y =
    nth y (nth x dl []) F.coq_X0

  (** val m2l_aux : int -> int -> int -> F.coq_X mat -> F.coq_X list list **)

  let rec m2l_aux r c cnt m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> [])
      (fun r' -> let g = mdata r c m in (mrow r c cnt m) :: (m2l_aux r' c (Stdlib.Int.succ cnt) g))
      r

  (** val m2l : int -> int -> F.coq_X mat -> F.coq_X list list **)

  let m2l r c m =
    m2l_aux r c 0 m

  (** val coq_MCol_aux : int -> int -> int -> int -> F.coq_X mat -> F.coq_X list **)

  let rec coq_MCol_aux r c ci cnt m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> [])
      (fun r' -> let g = mdata r c m in (g cnt ci) :: (coq_MCol_aux r' c ci (Stdlib.Int.succ cnt) g))
      r

  (** val coq_MCol : int -> int -> int -> F.coq_X mat -> F.coq_X list **)

  let coq_MCol r c ci m =
    coq_MCol_aux r c ci 0 m

  (** val mshiftc : int -> int -> F.coq_X mat -> int -> F.coq_X mat **)

  let mshiftc r c m k =
    let g = mdata r c m in (fun i j -> g i (add j k))

  (** val mk_mat_0_c : int -> F.coq_X mat **)

  let mk_mat_0_c c =
    l2m 0 c []

  (** val mk_mat_1_1 : F.coq_X -> F.coq_X mat **)

  let mk_mat_1_1 a11 =
    l2m (Stdlib.Int.succ 0) (Stdlib.Int.succ 0) ((a11 :: []) :: [])

  (** val mk_mat_1_2 : F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_1_2 a11 a12 =
    l2m (Stdlib.Int.succ 0) (Stdlib.Int.succ (Stdlib.Int.succ 0)) ((a11 :: (a12 :: [])) :: [])

  (** val mk_mat_1_3 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_1_3 a11 a12 a13 =
    l2m (Stdlib.Int.succ 0) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      ((a11 :: (a12 :: (a13 :: []))) :: [])

  (** val mk_mat_1_4 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_1_4 a11 a12 a13 a14 =
    l2m (Stdlib.Int.succ 0) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
      ((a11 :: (a12 :: (a13 :: (a14 :: [])))) :: [])

  (** val mk_mat_1_c : int -> F.coq_X list -> F.coq_X mat **)

  let mk_mat_1_c c l =
    l2m (Stdlib.Int.succ 0) c (l :: [])

  (** val mk_mat_r_0 : int -> F.coq_X mat **)

  let mk_mat_r_0 r =
    l2m r 0 []

  (** val mk_mat_2_1 : F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_2_1 a11 a21 =
    l2m (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0) ((a11 :: []) :: ((a21 :: []) :: []))

  (** val mk_mat_2_2 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_2_2 a11 a12 a21 a22 =
    l2m (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ (Stdlib.Int.succ 0))
      ((a11 :: (a12 :: [])) :: ((a21 :: (a22 :: [])) :: []))

  (** val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_3_1 a11 a21 a31 =
    l2m (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)
      ((a11 :: []) :: ((a21 :: []) :: ((a31 :: []) :: [])))

  (** val mk_mat_3_3 :
      F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X
      -> F.coq_X mat **)

  let mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 =
    l2m (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0)))
      ((a11 :: (a12 :: (a13 :: []))) :: ((a21 :: (a22 :: (a23 :: []))) :: ((a31 :: (a32 :: (a33 :: []))) :: [])))

  (** val mk_mat_4_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_4_1 a11 a21 a31 a41 =
    l2m (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))) (Stdlib.Int.succ 0)
      ((a11 :: []) :: ((a21 :: []) :: ((a31 :: []) :: ((a41 :: []) :: []))))

  (** val mk_mat_4_4 :
      F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X
      -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_4_4 a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 =
    l2m (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))) (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
      ((a11 :: (a12 :: (a13 :: (a14 :: [])))) :: ((a21 :: (a22 :: (a23 :: (a24 :: [])))) :: ((a31 :: (a32 :: (a33 :: (a34 :: [])))) :: ((a41 :: (a42 :: (a43 :: (a44 :: [])))) :: []))))

  (** val mk_mat_r_1 : int -> F.coq_X list -> F.coq_X mat **)

  let mk_mat_r_1 _ l ri ci =
    if (=) ci 0 then nth ri l F.coq_X0 else F.coq_X0

  (** val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat **)

  let mmap r c f m =
    let g = mdata r c m in (fun i j -> f (g i j))

  (** val mmap2 :
      int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let mmap2 r c f m1 m2 =
    let g1 = mdata r c m1 in let g2 = mdata r c m2 in (fun i j -> f (g1 i j) (g2 i j))

  (** val mat0 : int -> int -> F.coq_X mat **)

  let mat0 _ _ _ _ =
    F.coq_X0

  (** val mat1 : int -> F.coq_X mat **)

  let mat1 _ i j =
    if (=) i j then F.coq_X1 else F.coq_X0

  (** val madd : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let madd r c m1 m2 =
    let g1 = mdata r c m1 in let g2 = mdata r c m2 in (fun i j -> F.coq_Xadd (g1 i j) (g2 i j))

  (** val mopp : int -> int -> F.coq_X mat -> F.coq_X mat **)

  let mopp r c m =
    let g = mdata r c m in (fun i j -> F.coq_Xopp (g i j))

  (** val msub : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let msub r c m1 m2 =
    let g1 = mdata r c m1 in
    let g2 = mdata r c m2 in
    (fun i j -> let x0 = g1 i j in let y0 = g2 i j in F.coq_Xadd x0 (F.coq_Xopp y0))

  (** val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat **)

  let mcmul r c a m =
    let g = mdata r c m in (fun i j -> F.coq_Xmul a (g i j))

  (** val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat **)

  let mmulc r c m a =
    let g = mdata r c m in (fun i j -> F.coq_Xmul (g i j) a)

  (** val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat **)

  let mtrans r c m =
    let g = mdata r c m in (fun x y -> g y x)

  (** val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let mmul r c t1 m1 m2 =
    let g1 = mdata r c m1 in
    let g2 = mdata c t1 m2 in
    (fun x z0 -> SequenceInst.seqsum (fun y -> F.coq_Xmul (g1 x y) (g2 y z0)) c)

  (** val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat **)

  let t2m_3x3 = function
  | (a, b) ->
    let (a0, b0) = a in
    let (a1, b1) = a0 in
    let (a2, b2) = a1 in
    let (a3, b3) = b0 in
    let (a4, b4) = a3 in let (a5, b5) = b in let (a6, b6) = a5 in mk_mat_3_3 a2 b2 b1 a4 b4 b3 a6 b6 b5

  (** val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3 **)

  let m2t_3x3 m =
    let g =
      mdata (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m
    in
    (((((g 0 0), (g 0 (Stdlib.Int.succ 0))), (g 0 (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
    (((g (Stdlib.Int.succ 0) 0), (g (Stdlib.Int.succ 0) (Stdlib.Int.succ 0))),
    (g (Stdlib.Int.succ 0) (Stdlib.Int.succ (Stdlib.Int.succ 0))))),
    (((g (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0),
    (g (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))),
    (g (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ (Stdlib.Int.succ 0)))))

  (** val scalar_of_mat : F.coq_X mat -> F.coq_X **)

  let scalar_of_mat m =
    mnth (Stdlib.Int.succ 0) (Stdlib.Int.succ 0) m 0 0

  (** val trace : int -> F.coq_X mat -> F.coq_X **)

  let trace n m =
    let g = mdata n n m in SequenceInst.seqsum (fun x -> g x x) n
 end

(** val locked_with : unit -> 'a1 -> 'a1 **)

let locked_with _ x =
  x

module Option =
 struct
  (** val apply : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

  let apply f x = function
  | Some y -> f y
  | None -> x

  (** val default : 'a1 -> 'a1 option -> 'a1 **)

  let default x =
    apply (fun x0 -> x0) x

  (** val bind : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option **)

  let bind f =
    apply f None

  (** val map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

  let map f =
    bind (fun x -> Some (f x))
 end

type ('aT, 'rT) simpl_fun = 'aT -> 'rT
  (* singleton inductive, whose constructor was SimplFun *)

(** val fun_of_simpl : ('a1, 'a2) simpl_fun -> 'a1 -> 'a2 **)

let fun_of_simpl f =
  f

(** val comp : ('a2 -> 'a1) -> ('a3 -> 'a2) -> 'a3 -> 'a1 **)

let comp f g x =
  f (g x)

(** val pcomp : ('a2 -> 'a1 option) -> ('a3 -> 'a2 option) -> 'a3 -> 'a1 option **)

let pcomp f g x =
  Option.bind f (g x)

(** val tag : ('a1, 'a2) sigT -> 'a1 **)

let tag =
  projT1

(** val tagged : ('a1, 'a2) sigT -> 'a2 **)

let tagged =
  projT2

(** val tagged0 : 'a1 -> 'a2 -> ('a1, 'a2) sigT **)

let tagged0 i x =
  ExistT (i, x)

(** val isSome : 'a1 option -> bool **)

let isSome = function
| Some _ -> true
| None -> false

type decidable = bool

(** val iffP : bool -> reflect -> reflect **)

let iffP _ pb =
  let _evar_0_ = fun _ _ _ -> ReflectT in
  let _evar_0_0 = fun _ _ _ -> ReflectF in
  (match pb with
   | ReflectT -> _evar_0_ __ __ __
   | ReflectF -> _evar_0_0 __ __ __)

(** val decP : bool -> reflect -> decidable **)

let decP b _ =
  let _evar_0_ = fun _ -> true in
  let _evar_0_0 = fun _ -> false in if b then _evar_0_ __ else _evar_0_0 __

(** val idP : bool -> reflect **)

let idP = function
| true -> ReflectT
| false -> ReflectF

(** val andP : bool -> bool -> reflect **)

let andP b1 b2 =
  if b1 then if b2 then ReflectT else ReflectF else ReflectF

type 't pred0 = 't -> bool

type 't predType = __ -> 't pred0
  (* singleton inductive, whose constructor was PredType *)

type 't pred_sort = __

(** val predPredType : 'a1 predType **)

let predPredType x =
  Obj.magic x

type 't simpl_pred = ('t, bool) simpl_fun

(** val simplPred : 'a1 pred0 -> 'a1 simpl_pred **)

let simplPred p =
  p

(** val predT : 'a1 simpl_pred **)

let predT =
  simplPred (fun _ -> true)

module PredOfSimpl =
 struct
  (** val coerce : 'a1 simpl_pred -> 'a1 pred0 **)

  let coerce =
    fun_of_simpl
 end

(** val pred_of_argType : 'a1 simpl_pred **)

let pred_of_argType =
  predT

type 't rel = 't -> 't pred0

type 't mem_pred = 't pred0
  (* singleton inductive, whose constructor was Mem *)

(** val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort **)

let pred_of_mem mp =
  Obj.magic mp

(** val in_mem : 'a1 -> 'a1 mem_pred -> bool **)

let in_mem x mp =
  Obj.magic pred_of_mem mp x

(** val simpl_of_mem : 'a1 mem_pred -> 'a1 simpl_pred **)

let simpl_of_mem mp =
  simplPred (fun x -> in_mem x mp)

(** val mem : 'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred **)

let mem pT =
  pT

module Equality =
 struct
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  (** val op : 'a1 mixin_of -> 'a1 rel **)

  let op m =
    m.op

  type coq_type = __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort mixin_of **)

  let coq_class cT =
    cT
 end

(** val eq_op : Equality.coq_type -> Equality.sort rel **)

let eq_op t1 =
  (Equality.coq_class t1).Equality.op

(** val eqP : Equality.coq_type -> Equality.sort Equality.axiom **)

let eqP t1 =
  let _evar_0_ = fun _ a -> a in
  let { Equality.op = op0; Equality.mixin_of__1 = a } = t1 in _evar_0_ op0 a

(** val pred1 : Equality.coq_type -> Equality.sort -> Equality.sort simpl_pred **)

let pred1 t1 a1 =
  simplPred (fun x -> eq_op t1 x a1)

type 't comparable = 't -> 't -> decidable

(** val eq_comparable : Equality.coq_type -> Equality.sort comparable **)

let eq_comparable t1 x y =
  decP (eq_op t1 x y) (eqP t1 x y)

type 't subType = { val0 : (__ -> 't); sub0 : ('t -> __ -> __);
                    subType__2 : (__ -> ('t -> __ -> __) -> __ -> __) }

type 't sub_sort = __

(** val sub0 : 'a1 pred0 -> 'a1 subType -> 'a1 -> 'a1 sub_sort **)

let sub0 _ s x =
  s.sub0 x __

(** val insub : 'a1 pred0 -> 'a1 subType -> 'a1 -> 'a1 sub_sort option **)

let insub p sT x =
  match idP (p x) with
  | ReflectT -> Some (sub0 p sT x)
  | ReflectF -> None

(** val insubd : 'a1 pred0 -> 'a1 subType -> 'a1 sub_sort -> 'a1 -> 'a1 sub_sort **)

let insubd p sT u0 x =
  Option.default u0 (insub p sT x)

(** val inj_eqAxiom : Equality.coq_type -> ('a1 -> Equality.sort) -> 'a1 Equality.axiom **)

let inj_eqAxiom eT f x y =
  iffP (eq_op eT (f x) (f y)) (eqP eT (f x) (f y))

(** val injEqMixin : Equality.coq_type -> ('a1 -> Equality.sort) -> 'a1 Equality.mixin_of **)

let injEqMixin eT f =
  { Equality.op = (fun x y -> eq_op eT (f x) (f y)); Equality.mixin_of__1 = (inj_eqAxiom eT f) }

(** val pcanEqMixin :
    Equality.coq_type -> ('a1 -> Equality.sort) -> (Equality.sort -> 'a1 option) -> 'a1
    Equality.mixin_of **)

let pcanEqMixin eT f _ =
  injEqMixin eT f

(** val val_eqP :
    Equality.coq_type -> Equality.sort pred0 -> Equality.sort subType -> Equality.sort sub_sort
    Equality.axiom **)

let val_eqP t1 _ sT =
  inj_eqAxiom t1 sT.val0

(** val pair_eq : Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort) rel **)

let pair_eq t1 t4 u v =
  (&&) (eq_op t1 (fst u) (fst v)) (eq_op t4 (snd u) (snd v))

(** val pair_eqP :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort) Equality.axiom **)

let pair_eqP t1 t4 __top_assumption_ =
  let _evar_0_ = fun x1 x2 __top_assumption_0 ->
    let _evar_0_ = fun y1 y2 ->
      iffP ((&&) (eq_op t1 (fst (x1, x2)) (fst (y1, y2))) (eq_op t4 (snd (x1, x2)) (snd (y1, y2))))
        (andP (eq_op t1 (fst (x1, x2)) (fst (y1, y2))) (eq_op t4 (snd (x1, x2)) (snd (y1, y2))))
    in
    let (a, b) = __top_assumption_0 in _evar_0_ a b
  in
  let (a, b) = __top_assumption_ in _evar_0_ a b

(** val prod_eqMixin :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort) Equality.mixin_of **)

let prod_eqMixin t1 t4 =
  { Equality.op = (pair_eq t1 t4); Equality.mixin_of__1 = (pair_eqP t1 t4) }

(** val prod_eqType : Equality.coq_type -> Equality.coq_type -> Equality.coq_type **)

let prod_eqType t1 t4 =
  Obj.magic prod_eqMixin t1 t4

(** val tagged_as :
    Equality.coq_type -> (Equality.sort, 'a1) sigT -> (Equality.sort, 'a1) sigT -> 'a1 **)

let tagged_as i u v =
  match eqP i (tag u) (tag v) with
  | ReflectT -> tagged v
  | ReflectF -> tagged u

(** val tag_eq :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> (Equality.sort, Equality.sort) sigT
    -> (Equality.sort, Equality.sort) sigT -> bool **)

let tag_eq i t_ u v =
  (&&) (eq_op i (tag u) (tag v)) (eq_op (t_ (tag u)) (tagged u) (tagged_as i u v))

(** val tag_eqP :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> (Equality.sort, Equality.sort) sigT
    Equality.axiom **)

let tag_eqP i t_ __top_assumption_ =
  let _evar_0_ = fun i0 x __top_assumption_0 ->
    let _evar_0_ = fun j ->
      let _evar_0_ = fun y ->
        iffP (eq_op (t_ i0) x (tagged_as i (ExistT (i0, x)) (ExistT (i0, y))))
          (eqP (t_ i0) x (tagged_as i (ExistT (i0, x)) (ExistT (i0, y))))
      in
      let _evar_0_0 = fun _ -> ReflectF in
      (match eqP i i0 j with
       | ReflectT -> _evar_0_
       | ReflectF -> _evar_0_0)
    in
    let ExistT (x0, p) = __top_assumption_0 in _evar_0_ x0 p
  in
  let ExistT (x, p) = __top_assumption_ in _evar_0_ x p

(** val tag_eqMixin :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> (Equality.sort, Equality.sort) sigT
    Equality.mixin_of **)

let tag_eqMixin i t_ =
  { Equality.op = (tag_eq i t_); Equality.mixin_of__1 = (tag_eqP i t_) }

(** val tag_eqType : Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> Equality.coq_type **)

let tag_eqType i t_ =
  Obj.magic tag_eqMixin i t_

(** val eqn : int -> int -> bool **)

let rec eqn m n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun _ -> false)
      n)
    (fun m' -> (fun fO fS n -> if n=0 then fO () else fS (n-1))
                 (fun _ -> false)
                 (fun n' -> eqn m' n')
                 n)
    m

(** val eqnP : int Equality.axiom **)

let eqnP n m =
  iffP (eqn n m) (idP (eqn n m))

(** val nat_eqMixin : int Equality.mixin_of **)

let nat_eqMixin =
  { Equality.op = eqn; Equality.mixin_of__1 = eqnP }

(** val nat_eqType : Equality.coq_type **)

let nat_eqType =
  Obj.magic nat_eqMixin

(** val subn_rec : int -> int -> int **)

let subn_rec =
  sub

(** val subn : int -> int -> int **)

let subn =
  subn_rec

(** val leq : int -> int -> bool **)

let leq m n =
  eq_op nat_eqType (Obj.magic subn m n) (Obj.magic 0)

(** val iteri : int -> (int -> 'a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iteri n f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> x)
    (fun i -> f i (iteri i f x))
    n

(** val iterop : int -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

let iterop n op0 x =
  let f = fun i y -> (fun fO fS n -> if n=0 then fO () else fS (n-1))
                       (fun _ -> x)
                       (fun _ -> op0 x y)
                       i in
  iteri n f

(** val muln_rec : int -> int -> int **)

let muln_rec =
  mul

(** val muln : int -> int -> int **)

let muln =
  muln_rec

(** val expn_rec : int -> int -> int **)

let expn_rec m n =
  iterop n muln m (Stdlib.Int.succ 0)

(** val expn : int -> int -> int **)

let expn =
  expn_rec

(** val double_rec : int -> int **)

let rec double_rec n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun n' -> Stdlib.Int.succ (Stdlib.Int.succ (double_rec n')))
    n

(** val double0 : int -> int **)

let double0 =
  double_rec

(** val size : 'a1 list -> int **)

let rec size = function
| [] -> 0
| _ :: s' -> Stdlib.Int.succ (size s')

(** val cat : 'a1 list -> 'a1 list -> 'a1 list **)

let rec cat s1 s2 =
  match s1 with
  | [] -> s2
  | x :: s1' -> x :: (cat s1' s2)

(** val nth1 : 'a1 -> 'a1 list -> int -> 'a1 **)

let rec nth1 x0 s n =
  match s with
  | [] -> x0
  | x :: s' -> ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> x)
                  (fun n' -> nth1 x0 s' n')
                  n)

(** val find : 'a1 pred0 -> 'a1 list -> int **)

let rec find a = function
| [] -> 0
| x :: s' -> if a x then 0 else Stdlib.Int.succ (find a s')

(** val filter : 'a1 pred0 -> 'a1 list -> 'a1 list **)

let rec filter a = function
| [] -> []
| x :: s' -> if a x then x :: (filter a s') else filter a s'

(** val eqseq : Equality.coq_type -> Equality.sort list -> Equality.sort list -> bool **)

let rec eqseq t1 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _ :: _ -> false)
  | x1 :: s1' -> (match s2 with
                  | [] -> false
                  | x2 :: s2' -> (&&) (eq_op t1 x1 x2) (eqseq t1 s1' s2'))

(** val eqseqP : Equality.coq_type -> Equality.sort list Equality.axiom **)

let eqseqP t1 _top_assumption_ =
  let _evar_0_ = fun __top_assumption_ ->
    let _evar_0_ = ReflectT in
    let _evar_0_0 = fun _ _ -> ReflectF in
    (match __top_assumption_ with
     | [] -> _evar_0_
     | a :: l -> _evar_0_0 a l)
  in
  let _evar_0_0 = fun x1 s1 iHs __top_assumption_ ->
    let _evar_0_0 = ReflectF in
    let _evar_0_1 = fun x2 s2 ->
      let __top_assumption_0 = eqP t1 x1 x2 in
      let _evar_0_1 = fun _ -> iffP (eqseq t1 s1 s2) (iHs s2) in
      let _evar_0_2 = fun _ -> ReflectF in
      (match __top_assumption_0 with
       | ReflectT -> _evar_0_1 __
       | ReflectF -> _evar_0_2 __)
    in
    (match __top_assumption_ with
     | [] -> _evar_0_0
     | a :: l -> _evar_0_1 a l)
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f _top_assumption_

(** val seq_eqMixin : Equality.coq_type -> Equality.sort list Equality.mixin_of **)

let seq_eqMixin t1 =
  { Equality.op = (eqseq t1); Equality.mixin_of__1 = (eqseqP t1) }

(** val seq_eqType : Equality.coq_type -> Equality.coq_type **)

let seq_eqType t1 =
  Obj.magic seq_eqMixin t1

(** val index : Equality.coq_type -> Equality.sort -> Equality.sort list -> int **)

let index t1 x =
  find (PredOfSimpl.coerce (pred1 t1 x))

(** val map1 : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map1 f = function
| [] -> []
| x :: s' -> (f x) :: (map1 f s')

(** val pmap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list **)

let rec pmap f = function
| [] -> []
| x :: s' -> let r = pmap f s' in Option.apply (fun x0 -> x0 :: r) r (f x)

(** val iota : int -> int -> int list **)

let rec iota m n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' -> m :: (iota (Stdlib.Int.succ m) n'))
    n

(** val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldr f z0 = function
| [] -> z0
| x :: s' -> f x (foldr f z0 s')

(** val flatten : 'a1 list list -> 'a1 list **)

let flatten s =
  foldr cat [] s

module CodeSeq =
 struct
  (** val code : int list -> int **)

  let code =
    foldr (fun n m ->
      muln (expn (Stdlib.Int.succ (Stdlib.Int.succ 0)) n) (Stdlib.Int.succ (double0 m))) 0

  (** val decode_rec : int -> int -> int -> int list **)

  let rec decode_rec v q0 r =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> v :: [])
      (fun q' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> v :: (decode_rec 0 q' q'))
        (fun n ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> decode_rec (Stdlib.Int.succ v) q' q')
          (fun r' -> decode_rec v q' r')
          n)
        r)
      q0

  (** val decode : int -> int list **)

  let decode n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> [])
      (fun _ -> decode_rec 0 (pred n) (pred n))
      n
 end

(** val tag_of_pair : ('a1 * 'a2) -> ('a1, 'a2) sigT **)

let tag_of_pair p =
  tagged0 (fst p) (snd p)

(** val pair_of_tag : ('a1, 'a2) sigT -> 'a1 * 'a2 **)

let pair_of_tag u =
  ((tag u), (tagged u))

module Choice =
 struct
  type 't mixin_of = 't pred0 -> int -> 't option
    (* singleton inductive, whose constructor was Mixin *)

  (** val find : 'a1 mixin_of -> 'a1 pred0 -> int -> 'a1 option **)

  let find m =
    m

  type 't class_of = { base : 't Equality.mixin_of; mixin : 't mixin_of }

  (** val base : 'a1 class_of -> 'a1 Equality.mixin_of **)

  let base c =
    c.base

  (** val mixin : 'a1 class_of -> 'a1 mixin_of **)

  let mixin c =
    c.mixin

  type coq_type = __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort class_of **)

  let coq_class cT =
    cT

  (** val pack : 'a1 mixin_of -> 'a1 Equality.mixin_of -> Equality.coq_type -> coq_type **)

  let pack m b _ =
    { base = (Obj.magic b); mixin = (Obj.magic m) }

  (** val eqType : coq_type -> Equality.coq_type **)

  let eqType cT =
    (coq_class cT).base

  module InternalTheory =
   struct
    (** val find : coq_type -> sort pred0 -> int -> sort option **)

    let find t1 =
      find (coq_class t1).mixin
   end
 end

(** val pcanChoiceMixin :
    Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1 option) -> 'a1 Choice.mixin_of **)

let pcanChoiceMixin t1 _ f' =
  let liftP = fun sP -> simplPred (fun x -> Option.apply sP false (f' x)) in
  let sf = fun sP n -> Option.bind f' (Choice.InternalTheory.find t1 (PredOfSimpl.coerce (liftP sP)) n)
  in
  (fun sP -> fun_of_simpl (sf sP))

(** val canChoiceMixin :
    Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1) -> 'a1 Choice.mixin_of **)

let canChoiceMixin t1 f f' =
  pcanChoiceMixin t1 f (fun y -> Some (f' y))

(** val sub_choiceMixin :
    Choice.coq_type -> Choice.sort pred0 -> Choice.sort subType -> Choice.sort sub_sort Choice.mixin_of **)

let sub_choiceMixin t1 p sT =
  pcanChoiceMixin t1 sT.val0 (insub p sT)

(** val tagged_choiceMixin :
    Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> (Choice.sort, Choice.sort) sigT
    Choice.mixin_of **)

let tagged_choiceMixin i t_ =
  let ft = fun tP n i0 ->
    Option.map (tagged0 i0) (Choice.InternalTheory.find (t_ i0) (comp tP (tagged0 i0)) n)
  in
  let fi = fun tP ni nt ->
    Option.bind (ft tP nt) (Choice.InternalTheory.find i (fun i0 -> isSome (ft tP nt i0)) ni)
  in
  (fun tP n ->
  match CodeSeq.decode n with
  | [] -> None
  | ni :: l ->
    (match l with
     | [] -> None
     | nt :: l0 -> (match l0 with
                    | [] -> fi tP ni nt
                    | _ :: _ -> None)))

(** val tagged_choiceType : Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> Choice.coq_type **)

let tagged_choiceType i t_ =
  { Choice.base =
    (Equality.coq_class (tag_eqType (Choice.eqType i) (fun i0 -> Choice.eqType (t_ i0))));
    Choice.mixin = (Obj.magic tagged_choiceMixin i t_) }

(** val nat_choiceMixin : int Choice.mixin_of **)

let nat_choiceMixin =
  let f = fun p n -> if p n then Some n else None in (fun p -> fun_of_simpl (f p))

(** val nat_choiceType : Choice.coq_type **)

let nat_choiceType =
  { Choice.base = (Equality.coq_class nat_eqType); Choice.mixin = (Obj.magic nat_choiceMixin) }

(** val prod_choiceMixin :
    Choice.coq_type -> Choice.coq_type -> (Choice.sort * Choice.sort) Choice.mixin_of **)

let prod_choiceMixin t1 t4 =
  canChoiceMixin (tagged_choiceType t1 (fun _ -> t4)) (Obj.magic tag_of_pair) (Obj.magic pair_of_tag)

(** val prod_choiceType : Choice.coq_type -> Choice.coq_type -> Choice.coq_type **)

let prod_choiceType t1 t4 =
  { Choice.base = (Equality.coq_class (prod_eqType (Choice.eqType t1) (Choice.eqType t4)));
    Choice.mixin = (Obj.magic prod_choiceMixin t1 t4) }

module Countable =
 struct
  type 't mixin_of = { pickle : ('t -> int); unpickle : (int -> 't option) }

  (** val pickle : 'a1 mixin_of -> 'a1 -> int **)

  let pickle m =
    m.pickle

  (** val unpickle : 'a1 mixin_of -> int -> 'a1 option **)

  let unpickle m =
    m.unpickle

  (** val coq_ChoiceMixin : 'a1 mixin_of -> 'a1 Choice.mixin_of **)

  let coq_ChoiceMixin m =
    pcanChoiceMixin nat_choiceType (Obj.magic m.pickle) (Obj.magic m.unpickle)

  type 't class_of = { base : 't Choice.class_of; mixin : 't mixin_of }

  (** val base : 'a1 class_of -> 'a1 Choice.class_of **)

  let base c =
    c.base

  (** val mixin : 'a1 class_of -> 'a1 mixin_of **)

  let mixin c =
    c.mixin

  type coq_type = __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort class_of **)

  let coq_class cT =
    cT

  (** val choiceType : coq_type -> Choice.coq_type **)

  let choiceType cT =
    (coq_class cT).base
 end

(** val unpickle0 : Countable.coq_type -> int -> Countable.sort option **)

let unpickle0 t1 =
  (Countable.coq_class t1).Countable.mixin.Countable.unpickle

(** val pickle0 : Countable.coq_type -> Countable.sort -> int **)

let pickle0 t1 =
  (Countable.coq_class t1).Countable.mixin.Countable.pickle

(** val pcanCountMixin :
    Countable.coq_type -> ('a1 -> Countable.sort) -> (Countable.sort -> 'a1 option) -> 'a1
    Countable.mixin_of **)

let pcanCountMixin t1 f f' =
  { Countable.pickle = (comp (pickle0 t1) f); Countable.unpickle = (pcomp f' (unpickle0 t1)) }

(** val canCountMixin :
    Countable.coq_type -> ('a1 -> Countable.sort) -> (Countable.sort -> 'a1) -> 'a1 Countable.mixin_of **)

let canCountMixin t1 f f' =
  pcanCountMixin t1 f (fun y -> Some (f' y))

(** val sub_countMixin :
    Countable.coq_type -> Countable.sort pred0 -> Countable.sort subType -> Countable.sort sub_sort
    Countable.mixin_of **)

let sub_countMixin t1 p sT =
  pcanCountMixin t1 sT.val0 (insub p sT)

(** val pickle_tagged :
    Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> (Countable.sort, Countable.sort)
    sigT -> int **)

let pickle_tagged i t_ u =
  CodeSeq.code ((pickle0 i (tag u)) :: ((pickle0 (t_ (tag u)) (tagged u)) :: []))

(** val unpickle_tagged :
    Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> int -> (Countable.sort,
    Countable.sort) sigT option **)

let unpickle_tagged i t_ s =
  match CodeSeq.decode s with
  | [] -> None
  | ni :: l ->
    (match l with
     | [] -> None
     | nx :: l0 ->
       (match l0 with
        | [] -> Option.bind (fun i0 -> Option.map (tagged0 i0) (unpickle0 (t_ i0) nx)) (unpickle0 i ni)
        | _ :: _ -> None))

(** val tag_countMixin :
    Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> (Countable.sort, Countable.sort)
    sigT Countable.mixin_of **)

let tag_countMixin i t_ =
  { Countable.pickle = (pickle_tagged i t_); Countable.unpickle = (unpickle_tagged i t_) }

(** val tag_countType :
    Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> Countable.coq_type **)

let tag_countType i t_ =
  { Countable.base =
    (Choice.coq_class
      (tagged_choiceType (Countable.choiceType i) (fun i0 -> Countable.choiceType (t_ i0))));
    Countable.mixin = (Obj.magic tag_countMixin i t_) }

(** val nat_countMixin : int Countable.mixin_of **)

let nat_countMixin =
  { Countable.pickle = (fun x -> x); Countable.unpickle = (fun x -> Some x) }

(** val nat_countType : Countable.coq_type **)

let nat_countType =
  { Countable.base = (Choice.coq_class nat_choiceType); Countable.mixin = (Obj.magic nat_countMixin) }

(** val prod_countMixin :
    Countable.coq_type -> Countable.coq_type -> (Countable.sort * Countable.sort) Countable.mixin_of **)

let prod_countMixin t1 t4 =
  canCountMixin (tag_countType t1 (fun _ -> t4)) (Obj.magic tag_of_pair) (Obj.magic pair_of_tag)

module Finite =
 struct
  type mixin_of = { mixin_base : Equality.sort Countable.mixin_of; mixin_enum : Equality.sort list }

  (** val mixin_base : Equality.coq_type -> mixin_of -> Equality.sort Countable.mixin_of **)

  let mixin_base _ m =
    m.mixin_base

  (** val mixin_enum : Equality.coq_type -> mixin_of -> Equality.sort list **)

  let mixin_enum _ m =
    m.mixin_enum

  type 't class_of = { base : 't Choice.class_of; mixin : mixin_of }

  (** val base : 'a1 class_of -> 'a1 Choice.class_of **)

  let base c =
    c.base

  (** val mixin : 'a1 class_of -> mixin_of **)

  let mixin c =
    c.mixin

  (** val base2 : 'a1 class_of -> 'a1 Countable.class_of **)

  let base2 c =
    { Countable.base = c.base; Countable.mixin = (Obj.magic c.mixin.mixin_base) }

  type coq_type = __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort class_of **)

  let coq_class cT =
    cT

  (** val eqType : coq_type -> Equality.coq_type **)

  let eqType cT =
    (coq_class cT).base.Choice.base

  (** val choiceType : coq_type -> Choice.coq_type **)

  let choiceType cT =
    (coq_class cT).base

  (** val countType : coq_type -> Countable.coq_type **)

  let countType cT =
    base2 (coq_class cT)

  module type EnumSig =
   sig
    val enum : coq_type -> sort list
   end

  module EnumDef =
   struct
    (** val enum : coq_type -> Equality.sort list **)

    let enum cT =
      (coq_class cT).mixin.mixin_enum

    (** val enumDef : __ **)

    let enumDef =
      __
   end
 end

(** val enum_mem : Finite.coq_type -> Finite.sort mem_pred -> Finite.sort list **)

let enum_mem t1 mA =
  filter (PredOfSimpl.coerce (simpl_of_mem mA)) (Finite.EnumDef.enum t1)

module type CardDefSig =
 sig
  val card : Finite.coq_type -> Finite.sort mem_pred -> int
 end

module CardDef =
 struct
  (** val card : Finite.coq_type -> Finite.sort mem_pred -> int **)

  let card t1 mA =
    size (enum_mem t1 mA)

  (** val cardEdef : __ **)

  let cardEdef =
    __
 end

(** val pred0b : Finite.coq_type -> Finite.sort pred0 -> bool **)

let pred0b t1 p =
  eq_op nat_eqType (Obj.magic CardDef.card t1 (mem predPredType (Obj.magic p))) (Obj.magic 0)

module FiniteQuant =
 struct
  type quantified = bool
    (* singleton inductive, whose constructor was Quantified *)

  (** val all : Finite.coq_type -> quantified -> Finite.sort -> Finite.sort -> quantified **)

  let all _ b _ _ =
    negb b
 end

(** val pred0P : Finite.coq_type -> Finite.sort pred0 -> reflect **)

let pred0P t1 p =
  iffP (eq_op nat_eqType (Obj.magic CardDef.card t1 (mem predPredType (Obj.magic p))) (Obj.magic 0))
    (eqP nat_eqType (Obj.magic CardDef.card t1 (mem predPredType (Obj.magic p))) (Obj.magic 0))

(** val forallPP : Finite.coq_type -> Finite.sort pred0 -> (Finite.sort -> reflect) -> reflect **)

let forallPP t1 p _ =
  iffP (pred0b t1 (PredOfSimpl.coerce (simplPred (fun x -> FiniteQuant.all t1 (p x) x x))))
    (pred0P t1 (PredOfSimpl.coerce (simplPred (fun x -> FiniteQuant.all t1 (p x) x x))))

(** val eqfunP :
    Finite.coq_type -> (Finite.sort -> Equality.coq_type) -> (Finite.sort -> Equality.sort) ->
    (Finite.sort -> Equality.sort) -> reflect **)

let eqfunP t1 rT f1 f2 =
  forallPP t1 (fun x -> eq_op (rT x) (f1 x) (f2 x)) (fun x -> eqP (rT x) (f1 x) (f2 x))

(** val image_mem : Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort mem_pred -> 'a1 list **)

let image_mem t1 f mA =
  map1 f (enum_mem t1 mA)

(** val codom : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 list **)

let codom t1 f =
  image_mem t1 f (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))

type ordinal = int
  (* singleton inductive, whose constructor was Ordinal *)

(** val nat_of_ord : int -> ordinal -> int **)

let nat_of_ord _ i =
  i

(** val ordinal_subType : int -> int subType **)

let ordinal_subType n =
  { val0 = (Obj.magic nat_of_ord n); sub0 = (Obj.magic (fun x _ -> x)); subType__2 = (fun _ k_S u ->
    k_S (Obj.magic u) __) }

(** val ordinal_eqMixin : int -> ordinal Equality.mixin_of **)

let ordinal_eqMixin n =
  { Equality.op = (fun x y -> eq_op nat_eqType (Obj.magic nat_of_ord n x) (Obj.magic nat_of_ord n y));
    Equality.mixin_of__1 =
    (Obj.magic val_eqP nat_eqType (fun x -> leq (Stdlib.Int.succ (Obj.magic x)) n) (ordinal_subType n)) }

(** val ordinal_eqType : int -> Equality.coq_type **)

let ordinal_eqType n =
  Obj.magic ordinal_eqMixin n

(** val ordinal_choiceMixin : int -> ordinal Choice.mixin_of **)

let ordinal_choiceMixin n =
  Obj.magic sub_choiceMixin nat_choiceType (fun x -> leq (Stdlib.Int.succ (Obj.magic x)) n)
    (ordinal_subType n)

(** val ordinal_choiceType : int -> Choice.coq_type **)

let ordinal_choiceType n =
  { Choice.base = (Equality.coq_class (ordinal_eqType n)); Choice.mixin =
    (Obj.magic ordinal_choiceMixin n) }

(** val ordinal_countMixin : int -> ordinal Countable.mixin_of **)

let ordinal_countMixin n =
  Obj.magic sub_countMixin nat_countType (fun x -> leq (Stdlib.Int.succ (Obj.magic x)) n)
    (ordinal_subType n)

(** val ord_enum : int -> ordinal list **)

let ord_enum n =
  pmap (Obj.magic insub (fun x -> leq (Stdlib.Int.succ x) n) (ordinal_subType n)) (iota 0 n)

(** val ordinal_finMixin : int -> Finite.mixin_of **)

let ordinal_finMixin n =
  { Finite.mixin_base = (Obj.magic ordinal_countMixin n); Finite.mixin_enum = (Obj.magic ord_enum n) }

(** val ordinal_finType : int -> Finite.coq_type **)

let ordinal_finType n =
  { Finite.base = (Choice.coq_class (ordinal_choiceType n)); Finite.mixin = (ordinal_finMixin n) }

(** val enum_rank_in :
    Finite.coq_type -> Finite.sort -> Finite.sort pred_sort -> Equality.sort -> int sub_sort **)

let enum_rank_in t1 _ a x =
  insubd (fun x0 ->
    leq (Stdlib.Int.succ x0)
      (CardDef.card t1 (mem predPredType (Obj.magic (fun x1 -> Obj.magic a x1)))))
    (ordinal_subType (CardDef.card t1 (mem predPredType (Obj.magic (fun x0 -> Obj.magic a x0)))))
    (Obj.magic 0) (index (Finite.eqType t1) x (enum_mem t1 (mem predPredType a)))

(** val enum_rank : Finite.coq_type -> Finite.sort -> int sub_sort **)

let enum_rank t1 x =
  enum_rank_in t1 x (Obj.magic PredOfSimpl.coerce pred_of_argType) x

(** val prod_enum : Finite.coq_type -> Finite.coq_type -> (Finite.sort * Finite.sort) list **)

let prod_enum t1 t4 =
  flatten
    (map1 (fun x1 ->
      map1 (fun x2 -> (x1, x2))
        (enum_mem t4 (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))))
      (enum_mem t1 (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))))

(** val prod_finMixin : Finite.coq_type -> Finite.coq_type -> Finite.mixin_of **)

let prod_finMixin t1 t4 =
  { Finite.mixin_base = (Obj.magic prod_countMixin (Finite.countType t1) (Finite.countType t4));
    Finite.mixin_enum = (Obj.magic prod_enum t1 t4) }

(** val prod_finType : Finite.coq_type -> Finite.coq_type -> Finite.coq_type **)

let prod_finType t1 t4 =
  { Finite.base = (Choice.coq_class (prod_choiceType (Finite.choiceType t1) (Finite.choiceType t4)));
    Finite.mixin = (prod_finMixin t1 t4) }

type 't tuple_of = 't list
  (* singleton inductive, whose constructor was Tuple *)

(** val tval : int -> 'a1 tuple_of -> 'a1 list **)

let tval _ t1 =
  t1

(** val tuple_subType : int -> 'a1 list subType **)

let tuple_subType n =
  { val0 = (Obj.magic tval n); sub0 = (Obj.magic (fun x _ -> x)); subType__2 = (fun _ k_S u ->
    k_S (Obj.magic u) __) }

(** val tnth_default : int -> 'a1 tuple_of -> ordinal -> 'a1 **)

let tnth_default n t1 =
  let _evar_0_ = fun _ -> assert false (* absurd case *) in
  let _evar_0_0 = fun a _ _ -> a in (match tval n t1 with
                                     | [] -> _evar_0_
                                     | a :: l -> _evar_0_0 a l)

(** val tnth : int -> 'a1 tuple_of -> ordinal -> 'a1 **)

let tnth n t1 i =
  nth1 (tnth_default n t1 i) (tval n t1) (nat_of_ord n i)

(** val tuple : int -> 'a1 tuple_of -> (__ -> 'a1 tuple_of) -> 'a1 tuple_of **)

let tuple _ _ mkT =
  mkT __

(** val map_tuple : int -> ('a1 -> 'a2) -> 'a1 tuple_of -> 'a2 tuple_of **)

let map_tuple n f t1 =
  map1 f (tval n t1)

(** val tuple_eqMixin : int -> Equality.coq_type -> Equality.sort tuple_of Equality.mixin_of **)

let tuple_eqMixin n t1 =
  { Equality.op = (fun x y -> eq_op (seq_eqType t1) (Obj.magic tval n x) (Obj.magic tval n y));
    Equality.mixin_of__1 =
    (Obj.magic val_eqP (seq_eqType t1) (fun x -> eq_op nat_eqType (Obj.magic size x) (Obj.magic n))
      (tuple_subType n)) }

(** val tuple_eqType : int -> Equality.coq_type -> Equality.coq_type **)

let tuple_eqType n t1 =
  Obj.magic tuple_eqMixin n t1

(** val enum_tuple : Finite.coq_type -> Finite.sort pred_sort -> Finite.sort tuple_of **)

let enum_tuple t1 a =
  enum_mem t1 (mem predPredType a)

(** val codom_tuple : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 tuple_of **)

let codom_tuple t1 f =
  tuple (CardDef.card t1 (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType)))
    (map_tuple (CardDef.card t1 (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))) f
      (enum_tuple t1 (Obj.magic PredOfSimpl.coerce pred_of_argType))) (fun _ -> codom t1 f)

type 'rT finfun_on =
| Finfun_nil
| Finfun_cons of Finite.sort * Finite.sort list * 'rT * 'rT finfun_on

(** val finfun_rec : Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort list -> 'a1 finfun_on **)

let rec finfun_rec aT g = function
| [] -> Finfun_nil
| x1 :: s1 -> Finfun_cons (x1, s1, (g x1), (finfun_rec aT g s1))

(** val fun_of_fin_rec :
    Finite.coq_type -> Equality.sort -> Finite.sort list -> 'a1 finfun_on -> 'a1 **)

let fun_of_fin_rec aT x s f_s =
  let rec fun_of_fin_rec0 x0 _ = function
  | Finfun_nil -> (fun _ -> assert false (* absurd case *))
  | Finfun_cons (x1, s1, y1, f_s1) ->
    (match eqP (Finite.eqType aT) x0 x1 with
     | ReflectT -> (fun _ -> y1)
     | ReflectF -> fun_of_fin_rec0 x0 s1 f_s1)
  in fun_of_fin_rec0 x s f_s __

type 'rT finfun_of = 'rT finfun_on
  (* singleton inductive, whose constructor was FinfunOf *)

type 'rT dfinfun_of = 'rT finfun_of

(** val fun_of_fin : Finite.coq_type -> 'a1 finfun_of -> Equality.sort -> 'a1 **)

let fun_of_fin aT f x =
  fun_of_fin_rec aT x (enum_mem aT (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))) f

module type FinfunDefSig =
 sig
  val finfun : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 finfun_of
 end

module FinfunDef =
 struct
  (** val finfun : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 finfun_of **)

  let finfun aT g =
    finfun_rec aT g (enum_mem aT (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType)))

  (** val finfunE : __ **)

  let finfunE =
    __
 end

(** val total_fun :
    Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort -> (Finite.sort, 'a1) sigT **)

let total_fun _ g x =
  tagged0 x (g x)

(** val tfgraph : Finite.coq_type -> 'a1 finfun_of -> (Finite.sort, 'a1) sigT tuple_of **)

let tfgraph aT f =
  codom_tuple aT (total_fun aT (fun_of_fin aT f))

(** val tfgraph_inv : Finite.coq_type -> (Finite.sort, 'a1) sigT tuple_of -> 'a1 finfun_of option **)

let tfgraph_inv aT g =
  match eqfunP aT (fun _ -> Finite.eqType aT) (fun x ->
          tag
            (tnth (CardDef.card aT (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType)))
              g (Obj.magic enum_rank aT x))) (fun x -> x) with
  | ReflectT ->
    Some
      (FinfunDef.finfun aT (fun x ->
        tagged
          (tnth (CardDef.card aT (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))) g
            (Obj.magic enum_rank aT x))))
  | ReflectF -> None

(** val eqMixin :
    Finite.coq_type -> (Finite.sort -> Equality.coq_type) -> Equality.sort dfinfun_of Equality.mixin_of **)

let eqMixin aT rT =
  pcanEqMixin
    (tuple_eqType (CardDef.card aT (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType)))
      (tag_eqType (Finite.eqType aT) rT)) (Obj.magic tfgraph aT) (Obj.magic tfgraph_inv aT)

(** val finfun_eqType : Finite.coq_type -> Equality.coq_type -> Equality.coq_type **)

let finfun_eqType aT rT =
  Obj.magic eqMixin aT (fun _ -> rT)

type ('r, 'i) bigbody =
| BigBody of 'i * ('r -> 'r -> 'r) * bool * 'r

(** val applybig : ('a1, 'a2) bigbody -> 'a1 -> 'a1 **)

let applybig body x =
  let BigBody (_, op0, b, v) = body in if b then op0 v x else x

(** val reducebig : 'a1 -> 'a2 list -> ('a2 -> ('a1, 'a2) bigbody) -> 'a1 **)

let reducebig idx r body =
  foldr (comp applybig body) idx r

module type BigOpSig =
 sig
  val bigop : 'a1 -> 'a2 list -> ('a2 -> ('a1, 'a2) bigbody) -> 'a1
 end

module BigOp =
 struct
  (** val bigop : 'a1 -> 'a2 list -> ('a2 -> ('a1, 'a2) bigbody) -> 'a1 **)

  let bigop =
    reducebig

  (** val bigopE : __ **)

  let bigopE =
    __
 end

(** val index_enum_key : unit **)

let index_enum_key =
  ()

(** val index_enum : Finite.coq_type -> Finite.sort list **)

let index_enum t1 =
  locked_with index_enum_key (Finite.EnumDef.enum t1)

module GRing =
 struct
  module Zmodule =
   struct
    type 'v mixin_of = { zero : 'v; opp : ('v -> 'v); add : ('v -> 'v -> 'v) }

    (** val zero : 'a1 mixin_of -> 'a1 **)

    let zero m =
      m.zero

    (** val add : 'a1 mixin_of -> 'a1 -> 'a1 -> 'a1 **)

    let add m =
      m.add

    type 't class_of = { base : 't Choice.class_of; mixin : 't mixin_of }

    (** val mixin : 'a1 class_of -> 'a1 mixin_of **)

    let mixin c =
      c.mixin

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    (** val coq_class : coq_type -> sort class_of **)

    let coq_class cT =
      cT
   end

  (** val zero : Zmodule.coq_type -> Zmodule.sort **)

  let zero v =
    (Zmodule.coq_class v).Zmodule.mixin.Zmodule.zero

  (** val add : Zmodule.coq_type -> Zmodule.sort -> Zmodule.sort -> Zmodule.sort **)

  let add v =
    (Zmodule.coq_class v).Zmodule.mixin.Zmodule.add

  module Ring =
   struct
    type mixin_of = { one : Zmodule.sort; mul : (Zmodule.sort -> Zmodule.sort -> Zmodule.sort) }

    (** val mul : Zmodule.coq_type -> mixin_of -> Zmodule.sort -> Zmodule.sort -> Zmodule.sort **)

    let mul _ m =
      m.mul

    type 'r class_of = { base : 'r Zmodule.class_of; mixin : mixin_of }

    (** val base : 'a1 class_of -> 'a1 Zmodule.class_of **)

    let base c =
      c.base

    (** val mixin : 'a1 class_of -> mixin_of **)

    let mixin c =
      c.mixin

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    (** val coq_class : coq_type -> sort class_of **)

    let coq_class cT =
      cT

    (** val zmodType : coq_type -> Zmodule.coq_type **)

    let zmodType cT =
      (coq_class cT).base
   end

  (** val mul : Ring.coq_type -> Ring.sort -> Ring.sort -> Ring.sort **)

  let mul r =
    (Ring.coq_class r).Ring.mixin.Ring.mul
 end

type 'r matrix = 'r finfun_of
  (* singleton inductive, whose constructor was Matrix *)

(** val mx_val : int -> int -> 'a1 matrix -> 'a1 finfun_of **)

let mx_val _ _ a =
  a

(** val matrix_subType : int -> int -> 'a1 finfun_of subType **)

let matrix_subType m n =
  { val0 = (Obj.magic mx_val m n); sub0 = (fun x _ -> Obj.magic x); subType__2 = (fun _ iH u ->
    iH (Obj.magic u) __) }

(** val matrix_of_fun_def : int -> int -> (Finite.sort -> Finite.sort -> 'a1) -> 'a1 matrix **)

let matrix_of_fun_def m n f =
  FinfunDef.finfun (prod_finType (ordinal_finType m) (ordinal_finType n)) (fun ij ->
    f (fst (Obj.magic ij)) (snd (Obj.magic ij)))

(** val matrix_of_fun : int -> int -> unit -> (Finite.sort -> Finite.sort -> 'a1) -> 'a1 matrix **)

let matrix_of_fun m n k =
  locked_with k (matrix_of_fun_def m n)

(** val fun_of_matrix : int -> int -> 'a1 matrix -> ordinal -> ordinal -> 'a1 **)

let fun_of_matrix m n a i j =
  fun_of_fin (prod_finType (ordinal_finType m) (ordinal_finType n)) (mx_val m n a) (Obj.magic (i, j))

(** val matrix_eqMixin : Equality.coq_type -> int -> int -> Equality.sort matrix Equality.mixin_of **)

let matrix_eqMixin r m n =
  { Equality.op = (fun x y ->
    eq_op (finfun_eqType (prod_finType (ordinal_finType m) (ordinal_finType n)) r)
      (Obj.magic mx_val m n x) (Obj.magic mx_val m n y)); Equality.mixin_of__1 =
    (Obj.magic val_eqP (finfun_eqType (prod_finType (ordinal_finType m) (ordinal_finType n)) r)
      (fun _ -> true) (matrix_subType m n)) }

(** val matrix_eqType : Equality.coq_type -> int -> int -> Equality.coq_type **)

let matrix_eqType r m n =
  Obj.magic matrix_eqMixin r m n

(** val mulmx_key : unit **)

let mulmx_key =
  ()

(** val mulmx :
    GRing.Ring.coq_type -> int -> int -> int -> GRing.Ring.sort matrix -> GRing.Ring.sort matrix ->
    GRing.Ring.sort matrix **)

let mulmx r m n p a b =
  matrix_of_fun m p mulmx_key (fun i k ->
    BigOp.bigop (GRing.zero (GRing.Ring.zmodType r)) (Obj.magic index_enum (ordinal_finType n))
      (fun j -> BigBody (j, (GRing.add (GRing.Ring.zmodType r)), true,
      (GRing.mul r (fun_of_matrix m n a (Obj.magic i) j) (fun_of_matrix n p b j (Obj.magic k))))))

module Coq2_MatrixThy =
 functor (F:FieldSig) ->
 struct
  module FieldThyInst = FieldThy(F)

  module X_carrier_of_matrix =
   struct
    (** val coq_X_eqType : Equality.coq_type **)

    let coq_X_eqType =
      let x_eqbP = fun x y -> let s = F.coq_Xeqdec x y in if s then ReflectT else ReflectF in
      let x_eqMixin = { Equality.op = F.coq_Xeqb; Equality.mixin_of__1 = x_eqbP } in
      Obj.magic x_eqMixin

    (** val pickle : F.coq_X -> int **)

    let pickle _ =
      0

    (** val unpickle : int -> F.coq_X option **)

    let unpickle _ =
      None

    (** val coq_X_choiceType_mixin_of : F.coq_X Countable.mixin_of **)

    let coq_X_choiceType_mixin_of =
      { Countable.pickle = pickle; Countable.unpickle = unpickle }

    (** val coq_X_choiceType : Choice.coq_type **)

    let coq_X_choiceType =
      let x_choiceMixin = Countable.coq_ChoiceMixin coq_X_choiceType_mixin_of in
      Choice.pack (Obj.magic x_choiceMixin) (Equality.coq_class coq_X_eqType) coq_X_eqType

    (** val coq_X_zmodType : GRing.Zmodule.coq_type **)

    let coq_X_zmodType =
      let x_zmodMixin = { GRing.Zmodule.zero = F.coq_X0; GRing.Zmodule.opp = F.coq_Xopp;
        GRing.Zmodule.add = F.coq_Xadd }
      in
      { GRing.Zmodule.base = (Choice.coq_class coq_X_choiceType); GRing.Zmodule.mixin =
      (Obj.magic x_zmodMixin) }

    (** val coq_X_ringType : GRing.Ring.coq_type **)

    let coq_X_ringType =
      let x_ringMixin = { GRing.Ring.one = (Obj.magic F.coq_X1); GRing.Ring.mul =
        (Obj.magic F.coq_Xmul) }
      in
      { GRing.Ring.base = (GRing.Zmodule.coq_class coq_X_zmodType); GRing.Ring.mixin = x_ringMixin }
   end

  type 'x mat = 'x matrix

  (** val meq_dec : int -> int -> F.coq_X mat -> F.coq_X mat -> bool **)

  let meq_dec r c m1 m2 =
    eq_comparable (matrix_eqType X_carrier_of_matrix.coq_X_eqType r c) (Obj.magic m1) (Obj.magic m2)

  (** val mnth' : int -> int -> F.coq_X mat -> int -> int -> F.coq_X **)

  let mnth' r c m ri ci =
    let b = Nat.ltb ri r in
    if b then let b0 = Nat.ltb ci c in if b0 then fun_of_matrix r c m ri ci else F.coq_X0 else F.coq_X0

  (** val mnth : int -> int -> F.coq_X mat -> int -> int -> F.coq_X **)

  let mnth r c m ri ci =
    let b = leq (Stdlib.Int.succ ri) r in
    if b
    then let b0 = leq (Stdlib.Int.succ ci) c in if b0 then fun_of_matrix r c m ri ci else F.coq_X0
    else F.coq_X0

  (** val mk_mat_1_1 : F.coq_X -> F.coq_X mat **)

  let mk_mat_1_1 a11 =
    matrix_of_fun_def (Stdlib.Int.succ 0) (Stdlib.Int.succ 0) (fun i j ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> a11)
          (fun _ -> F.coq_X0)
          (Obj.magic j))
        (fun _ -> F.coq_X0)
        (Obj.magic i))

  (** val mk_mat_3_1 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_3_1 a1 a2 a3 =
    matrix_of_fun_def (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)
      (fun i j ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> a1)
          (fun _ -> F.coq_X0)
          (Obj.magic j))
        (fun n ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> a2)
            (fun _ -> F.coq_X0)
            (Obj.magic j))
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> a3)
              (fun _ -> F.coq_X0)
              (Obj.magic j))
            (fun _ -> F.coq_X0)
            n0)
          n)
        (Obj.magic i))

  (** val mk_mat_3_3 :
      F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X
      -> F.coq_X mat **)

  let mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 =
    matrix_of_fun_def (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ 0))) (fun i j ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> a11)
          (fun n ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> a12)
            (fun n0 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> a13)
              (fun _ -> F.coq_X0)
              n0)
            n)
          (Obj.magic j))
        (fun n ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> a21)
            (fun n0 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> a22)
              (fun n1 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> a23)
                (fun _ -> F.coq_X0)
                n1)
              n0)
            (Obj.magic j))
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> a31)
              (fun n1 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> a32)
                (fun n2 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> a33)
                  (fun _ -> F.coq_X0)
                  n2)
                n1)
              (Obj.magic j))
            (fun _ -> F.coq_X0)
            n0)
          n)
        (Obj.magic i))

  (** val mk_mat_2_2 : F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X -> F.coq_X mat **)

  let mk_mat_2_2 a11 a12 a21 a22 =
    matrix_of_fun_def (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ (Stdlib.Int.succ 0))
      (fun i j ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> a11)
          (fun n ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> a12)
            (fun _ -> F.coq_X0)
            n)
          (Obj.magic j))
        (fun n ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> a21)
            (fun n0 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> a22)
              (fun _ -> F.coq_X0)
              n0)
            (Obj.magic j))
          (fun _ -> F.coq_X0)
          n)
        (Obj.magic i))

  (** val mat0 : int -> int -> F.coq_X mat **)

  let mat0 r c =
    matrix_of_fun_def r c (fun _ _ -> F.coq_X0)

  (** val mat1 : int -> F.coq_X mat **)

  let mat1 n =
    matrix_of_fun_def n n (fun i j ->
      if eq_op (Finite.eqType (ordinal_finType n)) i j then F.coq_X1 else F.coq_X0)

  (** val mmap : int -> int -> (F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat **)

  let mmap r c f m =
    matrix_of_fun_def r c (fun i j -> f (fun_of_matrix r c m (Obj.magic i) (Obj.magic j)))

  (** val mmap2 :
      int -> int -> (F.coq_X -> F.coq_X -> F.coq_X) -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let mmap2 r c f m1 m2 =
    matrix_of_fun_def r c (fun i j ->
      f (fun_of_matrix r c m1 (Obj.magic i) (Obj.magic j))
        (fun_of_matrix r c m2 (Obj.magic i) (Obj.magic j)))

  (** val madd : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X matrix **)

  let madd r c m1 m2 =
    matrix_of_fun_def r c (fun i j ->
      F.coq_Xadd (fun_of_matrix r c m1 (Obj.magic i) (Obj.magic j))
        (fun_of_matrix r c m2 (Obj.magic i) (Obj.magic j)))

  (** val mopp : int -> int -> F.coq_X mat -> F.coq_X mat **)

  let mopp r c m =
    matrix_of_fun_def r c (fun i j -> F.coq_Xopp (fun_of_matrix r c m (Obj.magic i) (Obj.magic j)))

  (** val msub : int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X matrix **)

  let msub r c m1 m2 =
    matrix_of_fun_def r c (fun i j ->
      F.coq_Xadd (fun_of_matrix r c m1 (Obj.magic i) (Obj.magic j))
        (F.coq_Xopp (fun_of_matrix r c m2 (Obj.magic i) (Obj.magic j))))

  (** val mcmul : int -> int -> F.coq_X -> F.coq_X mat -> F.coq_X mat **)

  let mcmul r c a m =
    matrix_of_fun_def r c (fun i j -> F.coq_Xmul a (fun_of_matrix r c m (Obj.magic i) (Obj.magic j)))

  (** val mmulc : int -> int -> F.coq_X mat -> F.coq_X -> F.coq_X mat **)

  let mmulc r c m a =
    matrix_of_fun_def r c (fun i j -> F.coq_Xmul (fun_of_matrix r c m (Obj.magic i) (Obj.magic j)) a)

  (** val mtrans : int -> int -> F.coq_X mat -> F.coq_X mat **)

  let mtrans r c m =
    matrix_of_fun_def c r (fun i j -> fun_of_matrix r c m (Obj.magic j) (Obj.magic i))

  (** val mmul : int -> int -> int -> F.coq_X mat -> F.coq_X mat -> F.coq_X mat **)

  let mmul r c s m1 m2 =
    Obj.magic mulmx X_carrier_of_matrix.coq_X_ringType r c s m1 m2

  (** val l2m : int -> int -> F.coq_X list list -> F.coq_X mat **)

  let l2m r c _ =
    matrix_of_fun_def r c (fun _ _ -> F.coq_X0)

  (** val finfun_on_to_dlist : int -> int -> F.coq_X finfun_on -> F.coq_X list list **)

  let finfun_on_to_dlist _ _ _ =
    []

  (** val m2l : int -> int -> F.coq_X mat -> F.coq_X list list **)

  let m2l =
    finfun_on_to_dlist

  (** val t2m_3x3 : F.coq_X t_3x3 -> F.coq_X mat **)

  let t2m_3x3 = function
  | (a, b) ->
    let (a0, b0) = a in
    let (a1, b1) = a0 in
    let (a2, b2) = a1 in
    let (a3, b3) = b0 in
    let (a4, b4) = a3 in let (a5, b5) = b in let (a6, b6) = a5 in mk_mat_3_3 a2 b2 b1 a4 b4 b3 a6 b6 b5

  (** val m2t_3x3 : F.coq_X mat -> F.coq_X t_3x3 **)

  let m2t_3x3 m =
    (((((mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ 0))) m 0 0),
      (mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m 0 (Stdlib.Int.succ 0))),
      (mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m 0 (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
      (((mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ 0))) m (Stdlib.Int.succ 0) 0),
      (mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m (Stdlib.Int.succ 0) (Stdlib.Int.succ 0))),
      (mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m (Stdlib.Int.succ 0) (Stdlib.Int.succ (Stdlib.Int.succ 0))))),
      (((mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ 0))) m (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0),
      (mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))),
      (mnth (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))) m (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))

  (** val scalar_of_mat : F.coq_X mat -> F.coq_X **)

  let scalar_of_mat m =
    mnth (Stdlib.Int.succ 0) (Stdlib.Int.succ 0) m 0 0

  (** val det_of_mat_3_3 : F.coq_X mat -> F.coq_X **)

  let det_of_mat_3_3 m =
    let (p, t1) = m2t_3x3 m in
    let (t4, t5) = p in
    let (t6, a13) = t4 in
    let (a11, a12) = t6 in
    let (t7, a23) = t5 in
    let (a21, a22) = t7 in
    let (t8, a33) = t1 in
    let (a31, a32) = t8 in
    let b1 = F.coq_Xmul (F.coq_Xmul a11 a22) a33 in
    let b2 = F.coq_Xmul (F.coq_Xmul a12 a23) a31 in
    let b3 = F.coq_Xmul (F.coq_Xmul a13 a21) a32 in
    let c1 = F.coq_Xmul (F.coq_Xmul a11 a23) a32 in
    let c2 = F.coq_Xmul (F.coq_Xmul a12 a21) a33 in
    let c3 = F.coq_Xmul (F.coq_Xmul a13 a22) a31 in
    let b = F.coq_Xadd (F.coq_Xadd b1 b2) b3 in
    let c = F.coq_Xadd (F.coq_Xadd c1 c2) c3 in F.coq_Xadd b (F.coq_Xopp c)
 end

module MatrixAll =
 functor (F:FieldSig) ->
 struct
  module DP = MatrixThy(F)

  module DL = Coq_MatrixThy(F)

  module DR = Coq0_MatrixThy(F)

  module NF = Coq1_MatrixThy(F)

  module FF = Coq2_MatrixThy(F)

  (** val dr2nf : int -> int -> F.coq_X DR.mat -> F.coq_X NF.mat **)

  let dr2nf r c m =
    NF.l2m r c (DR.m2l r c m)

  (** val nf2dr : int -> int -> F.coq_X NF.mat -> F.coq_X DR.mat **)

  let nf2dr r c m =
    DR.l2m r c (NF.m2l r c m)

  (** val dr2ff : int -> int -> F.coq_X DR.mat -> F.coq_X FF.mat **)

  let dr2ff r c m =
    FF.l2m r c (DR.m2l r c m)

  (** val ff2dr : int -> int -> F.coq_X FF.mat -> F.coq_X DR.mat **)

  let ff2dr r c m =
    DR.l2m r c (FF.m2l r c m)

  (** val dr2dp : int -> int -> F.coq_X DR.mat -> F.coq_X DP.mat **)

  let dr2dp r c m =
    DP.l2m r c (DR.m2l r c m)

  (** val dp2dr : int -> int -> F.coq_X DP.mat -> F.coq_X DR.mat **)

  let dp2dr r c m =
    DR.l2m r c (DP.m2l r c m)

  (** val dr2dl : int -> int -> F.coq_X DR.mat -> F.coq_X DL.mat **)

  let dr2dl r c m =
    DL.l2m r c (DR.m2l r c m)

  (** val dl2dr : int -> int -> F.coq_X DL.mat -> F.coq_X DR.mat **)

  let dl2dr r c m =
    DR.l2m r c (DL.m2l r c m)

  (** val nf2ff : int -> int -> F.coq_X NF.mat -> F.coq_X FF.mat **)

  let nf2ff r c m =
    FF.l2m r c (NF.m2l r c m)

  (** val ff2nf : int -> int -> F.coq_X FF.mat -> F.coq_X NF.mat **)

  let ff2nf r c m =
    NF.l2m r c (FF.m2l r c m)

  (** val nf2dp : int -> int -> F.coq_X NF.mat -> F.coq_X DP.mat **)

  let nf2dp r c m =
    DP.l2m r c (NF.m2l r c m)

  (** val dp2nf : int -> int -> F.coq_X DP.mat -> F.coq_X NF.mat **)

  let dp2nf r c m =
    NF.l2m r c (DP.m2l r c m)

  (** val nf2dl : int -> int -> F.coq_X NF.mat -> F.coq_X DL.mat **)

  let nf2dl r c m =
    DL.l2m r c (NF.m2l r c m)

  (** val dl2nf : int -> int -> F.coq_X DL.mat -> F.coq_X NF.mat **)

  let dl2nf r c m =
    NF.l2m r c (DL.m2l r c m)

  (** val ff2dp : int -> int -> F.coq_X FF.mat -> F.coq_X DP.mat **)

  let ff2dp r c m =
    DP.l2m r c (FF.m2l r c m)

  (** val dp2ff : int -> int -> F.coq_X DP.mat -> F.coq_X FF.mat **)

  let dp2ff r c m =
    FF.l2m r c (DP.m2l r c m)

  (** val ff2dl : int -> int -> F.coq_X FF.mat -> F.coq_X DL.mat **)

  let ff2dl r c m =
    DL.l2m r c (FF.m2l r c m)

  (** val dl2ff : int -> int -> F.coq_X DL.mat -> F.coq_X FF.mat **)

  let dl2ff r c m =
    FF.l2m r c (DL.m2l r c m)

  (** val dp2dl : int -> int -> F.coq_X DP.mat -> F.coq_X DL.mat **)

  let dp2dl r c m =
    DL.l2m r c (DP.m2l r c m)

  (** val dl2dp : int -> int -> F.coq_X DL.mat -> F.coq_X DP.mat **)

  let dl2dp r c m =
    DP.l2m r c (DL.m2l r c m)
 end

module MatrixAllR = MatrixAll(FieldR.FieldDefR)

module MatrixR_DR = MatrixAllR.DR

module MatrixR_DP = MatrixAllR.DP

module MatrixR_DL = MatrixAllR.DL

module MatrixR_NF = MatrixAllR.NF

module MatrixR_FF = MatrixAllR.FF

module DL = MatrixR_DL

module DP = MatrixR_DP

module DR = MatrixR_DR

module NF = MatrixR_NF

module FF = MatrixR_FF
