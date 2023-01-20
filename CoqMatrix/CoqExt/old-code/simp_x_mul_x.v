(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  author:     ZhengPu Shi
  date:       Mar 11, 2021
  purpose:
    平方表达式的证明是一个常见问题，需要总结一下。
*)

Require Import Reals.
Open Scope R_scope.

(* 关于平方表达式的一些记号：
1. x * x
  THIS IS NORMAL VIEW.
2. x²
  THIS IS AN NOTATION OF Rsqr
  Notation "r ²" := (Rsqr r) : R_scope
3. Rsqr x
  THIS IS AN FUN
  Rsqr = fun r : R => r * r : R -> R
4. x ^ 2
  THIS IS AN NOTATION
  Notation "x ^ y" := (pow x y) : R_scope
5. pow x 2
  THIS IS AN FUN
  pow : R -> nat -> R
*)

(* 它们之间的转换 *)

(* 1. x * x to other *)
Lemma trans_1_to_2 x : x * x = x².
  unfold Rsqr. reflexivity.
  Back 2. auto. Qed.

Lemma trans_1_to_3 x : x * x = Rsqr x.
  unfold Rsqr. reflexivity. 
  Back 2. auto. Qed.

Lemma trans_1_to_4 x : x * x = x ^ 2.
  rewrite <- Rsqr_pow2. auto. Qed.

Lemma trans_1_to_5 x : x * x = pow x 2.
  rewrite <- Rsqr_pow2. auto. Qed.

(* 2. x² to other *)
Lemma trans_2_to_3 x : x² = Rsqr x.
  reflexivity. Qed.

Lemma trans_2_to_4 x : x² = x ^ 2.
  rewrite <- Rsqr_pow2. auto. Qed.

Lemma trans_2_to_5 x : x² = pow x 2.
  rewrite <- Rsqr_pow2. auto. Qed.

(* 3. Rsqr to other *)
Lemma trans_3_to_4 x : Rsqr x = x ^ 2.
  rewrite <- Rsqr_pow2. auto. Qed.

Lemma trans_3_to_5 x : Rsqr x = pow x 2.
  rewrite <- Rsqr_pow2. auto. Qed.

(* 4. x ^ 2 to other *)
Lemma trans_4_to_5 x : x ^ 2 = pow x 2.
  reflexivity. Qed.

Lemma trans_4_to_1 x : x ^ 2 = x * x.
  rewrite <- Rsqr_pow2. unfold Rsqr. auto.
Qed.

(* 5. pow 2 to other *)
Lemma trans_5_to_1 x : pow x 2 = x * x.
  rewrite <- Rsqr_pow2. unfold Rsqr. auto.
Qed.
