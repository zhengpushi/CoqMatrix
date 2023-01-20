(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : test for ListExt
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Import SetoidListListExt.


(** ** Zero list *)

Compute lzero 99 3.


(** ** map one list to another one *)

Compute map Nat.succ [1;2;3].


(** ** map two lists to a list *)

Compute map2 Nat.add [1;2;3] [4;5;6].


(** ** lmap2 is considered as ladd *)

Compute ladd Nat.add [1;2] [3;4;5].


(** ** list sub, opp *)

Compute lsub Nat.sub [4;5;6] [1;2].


(** ** constant multiplication of list *)

Compute lcmul Nat.mul 3 [1;2;3].
Compute lmulc Nat.mul [1;2;3] 3.
Compute lcmul Nat.mul 3 [].


(** ** product of two lists *)

Compute ldot 0 Nat.add Nat.mul [1;2;3] [4;5;6].


(** ** a dlist with same element nil *)

Compute dnil 3.


(** ** lmap2 and dnil *)

  (** Convert a list to a dlist, it looks like converting a row to a column. *)
Compute cvt_row2col [1;2;3].
Compute cvt_col2row 0 [].
Compute cvt_col2row 0 [[]].
Compute cvt_col2row 0 [[1];[];[3]].
Compute cvt_col2row 0 [[1];[2];[3]].

  (** Convert a dlist to a list which contain head element, it looks like 
    converting a column to a row. *)
Compute cvt_row2col (cvt_col2row 0 []).
Compute cvt_row2col (cvt_col2row 0 [[1];[2];[3]]).
Compute cvt_col2row 0 (cvt_row2col []).
Compute cvt_col2row 0 (cvt_row2col [1;2;3]).


(** ** head column of a dlist *)

Compute hdc 0 [].
Compute hdc 0 [[];[];[]].
Compute hdc 0 [[];[2];[]].
Compute hdc 0 [[1;2;3];[4;5;6]].


(** ** tail columns of a dlist *)

Compute tlc [].
Compute tlc [[];[]].
Compute tlc [[2;3;4];[];[]].
Compute tlc [[1;2;3];[4;5;6]].


(** ** construct a dlist with a list and a dlist by column *)

Compute consc [] [].
Compute consc [1;2;3] [].
Compute consc [] [[1;2];[3;4]].
Compute consc [1;2] [[];[]].
Compute consc [1;2] [[];[];[]].
Compute consc [1;2;3] [[5;6];[7;8];[9;10]].
Compute consc [1;2;3] [[5;6];[7;8];[9;10];[11;12]].


(** ** Append two objects of dlist type to one object of dlist *)

Compute dlappr [[1;2;3];[4;5;6]] [[7;8;9];[10;11;12]].
Compute dlappc [[1;2;3];[4;5;6]] [[7;8;9];[10;11;12]].

Compute [[1;2;3];[4;5;6]] ++ [[7;8;9];[10;11;12]].
Compute [[1;2;3];[4;5;6]] @@ [[7;8;9];[10;11;12]].


(** ** Zero dlist *)

Compute dlzero 99 3 2.


(** ** dlist unit, like a identity matrix *)

Compute dlunit 0 1 0.
Compute dlunit 0 1 1.
Compute dlunit 0 1 2.
Compute dlunit 0 1 3.


(** ** transpose a dlist *)

Compute consc [1;2;3] [].
Compute (dltrans (consc [1;2;3] []) 3).
Compute [1;2;3] :: (dltrans [] 2).

Compute dltrans [] 2.
Compute dltrans [[];[]] 0.
Compute dltrans [[];[]] 2.  (* input error, colums must be <= 0 *)
Compute dltrans [[1;2;3];[4;5;6]] 2.
Compute dltrans [[1;2;3];[4;5;6]] 3.
Compute dltrans [[1;2;3];[4;5;6]] 4.  (* error, colums must be <= 3*)
Compute dltrans [[1;2;3];[]] 2.

Compute (dltrans (dltrans [] 2) 2).
Compute (dltrans (dltrans [[];[]] 0) 2).


(** ** map of dlist *)

Compute dmap Nat.succ [[1;2;3];[4;5;6]].


(** ** map2 of dlist *)

Compute dmap2 Nat.add [[1;2];[3;4]] [[5;6];[7;8]].


(** list dot dlist *)

Compute ldotdl 0 Nat.add Nat.mul [1;2;3] [[1;2;3];[4;5;6]].
Compute ldotdl 0 Nat.add Nat.mul [1;2;3] (dnil 5).
Compute ldotdl 0 Nat.add Nat.mul [6;7;8;5;1;2;3] (dnil 5).


(** dlist dot dlist *)

Compute dldotdl 0 Nat.add Nat.mul [[];[]] [[];[]].
Compute dldotdl 0 Nat.add Nat.mul [[1;2;3];[4;5;6]] [[7;8;9];[10;11;12]].
Compute dldotdl 0 Nat.add Nat.mul [[7;8;9];[10;11;12]] [[1;2;3];[4;5;6]].

