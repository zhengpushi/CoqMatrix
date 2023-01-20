(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : Extension for string
  author      : ZhengPu Shi
  date        : 2022.08

*)

Require Export Nat List.
Export ListNotations.

Require Export Ascii String.

Open Scope string.
Open Scope nat.

(** nat to ascii：只有0~9能正确转换，其余的都会转换为'A' *)
Definition nat2ascii (n:nat) : ascii :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | _ => "A"
  end.

(** nat to string 的辅助函数。
  cnt     用于循环计数，初始值至少是位数那么大，比如125的位数是3
  n       输入的自然数
  suffix  后缀字符串，初始值为 ""，随着循环会逐步构成 "5", "25", "125"
*)
Fixpoint nat2str_aux (cnt:nat) (n:nat) (suffix:string) : string :=
  let suffix' := String (nat2ascii (n mod 10)) suffix in
  match cnt with
  | O => suffix'
  | S cnt' => match (n/10) with
    | O => suffix'
    | n' => nat2str_aux cnt' n' suffix'
    end
  end.

(** nat to string *)
Definition nat2str (n : nat) : string := nat2str_aux n n "".

(* Compute map (fun n => nat2str n) (seq 0 103). *)

(** 生成 n 个字符串：a1,a2,...,an *)
Definition create_nstrs (n:nat) (prefix:string) : list string :=
  map (fun i => prefix ++ nat2str i) (seq 1 n).
