
type __ = Obj.t

type unit0 =
| Tt

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 't vec = __

(** val vmake_aux : nat -> nat -> (nat -> 'a1) -> 'a1 vec **)

let rec vmake_aux n i f =
  match n with
  | O -> Obj.magic Tt
  | S n' -> Obj.magic (Pair ((f i), (vmake_aux n' (S i) f)))

(** val vmake : nat -> (nat -> 'a1) -> 'a1 vec **)

let vmake n f =
  vmake_aux n O f

(** val vnth : 'a1 -> nat -> nat -> 'a1 vec -> 'a1 **)

let rec vnth t0 n i x =
  match n with
  | O -> t0
  | S n' -> (match i with
             | O -> fst (Obj.magic x)
             | S i' -> vnth t0 n' i' (snd (Obj.magic x)));;

let n1 = S O;;
let n2 = S n1;;
let n3 = S n2;;
let n4 = S n3;;
let n5 = S n4;;
let v1 = vmake n5 (fun i -> i);;

              
              
