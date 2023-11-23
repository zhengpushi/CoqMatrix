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

(** 用指定字符构成的字符串 *)
Definition str_repeat (c : ascii) (len : nat) : string :=
  let fix f (aux:string) (n:nat) :=
    match n with
    | O => aux
    | S n => String c (f aux n)
    end in
  f "" len.

(** 左填充的定长字符串。不足右侧用空格填充，多余时剪掉右侧 *)
Definition str_alignl (s : string) (len : nat) : string :=
  let len_s := length s in      (* 给定字符串长度 *)
  if len_s =? len
  then s
  else if len_s <? len
       then s ++ (str_repeat " " (len - len_s)) (* 不足，右侧用空格填充 *)
       else
         substring 0 len s.     (* 多余，截掉右侧 *)

(* Compute str_alignl "abcdef" 2. *)
(* Compute str_alignl "abcdef" 10. *)
                
(** 右对齐的定长字符串。不足时左侧填充空格，多余时剪掉左侧 *)
Definition str_alignr (s : string) (len : nat) : string :=
  let len_s := length s in      (* 给定字符串长度 *)
  if len_s =? len
  then s
  else if len_s <? len
       then (str_repeat " " (len - len_s)) ++ s (* 不足，左侧用空格填充 *)
       else
         substring (len_s - len) len s.     (* 多余，截掉左侧 *)

(* Compute str_alignr "abcd" 2. *)
(* Compute str_alignr "abcd" 8. *)


(** * LF and CR strings *)
Section LF_CR.

  (* 换行(Line Feed)，即 \n (new line) *)
  Definition CharLF : ascii := ascii_of_nat 10.

  (* 回车(CarryReturn)，即 \r *)
  Definition CharCR : ascii := ascii_of_nat 13.
  
  (* 在Unix/Linux使用LF，在Widows使用\r\n, Mac使用\n *)
  Definition strNewlineUnix : string := String CharLF "".
  Definition strNewlineWin : string := String CharCR (String CharLF "").
  Definition strNewlineMac : string := String CharCR "".
  Definition strNewline : string := strNewlineUnix.
  
End LF_CR.

