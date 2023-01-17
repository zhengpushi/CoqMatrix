
type __ = Obj.t

type unit0 =
| Tt

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 't vec = __

val vmake_aux : nat -> nat -> (nat -> 'a1) -> 'a1 vec

val vmake : nat -> (nat -> 'a1) -> 'a1 vec

val vnth : 'a1 -> nat -> nat -> 'a1 vec -> 'a1
