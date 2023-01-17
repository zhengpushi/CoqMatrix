(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : Matrix of multi-dimensions.
  author      : ZhengPu Shi
  date        : 2022.04
  
  remark      :
  1. First attemption.
    We use list to store data and the dimensions.
    It is a extension method of matrix-record-style
    (1). A : Type, it is basic type or carrier type of element.
    (2). multi dimensions data.
      Type    Data            Dims
      dim0    (x : A)         []
      dim1    list A          [n]
      dim2    list (list A)   [n1;n2]
*)



Require Import List.
Import ListNotations.

(*
  Record mat (dims : list nat) := {
    mat_data  : tpMatData dims;
    Cond  : Cond_type dims mat_data
  }
*)


(** ** Dimensions *)
Section Dimensions.
  
  Definition Dims := list nat.
  
  Definition dim0 : Dims := [].
  Definition dim1 n1 : Dims := [n1].
  Definition dim2 n1 n2 : Dims := [n1;n2].
  Definition dim3 n1 n2 n3 : Dims := [n1;n2;n3].
  Definition dimx (l : list nat) : Dims := l.
  
End Dimensions.


(** ** matrix data *)
Section Data.

  Fixpoint Data {A : Type} (dims : Dims) : Type :=
    match dims with
    | [] => A (* list A *)
    | n :: dims' => list (@Data A dims')
    end.

  Compute @Data nat [].
  Compute @Data nat [1].
  Compute @Data nat [1;2].

  Definition data0 {A} := @Data A [].
  Definition data1 {A} n := @Data A [n].
  Definition data2 {A} n1 n2 := @Data A [n1;n2].
  Definition data3 {A} n1 n2 n3 := @Data A [n1;n2;n3].

  (** any data ∈ dim0 *)
  Check 3 : data0.
  Check [] : data0.
  Check [1;2] : data0.

  (** list ∈ dim1 *)
  Check [] : data1 2.
  Check [] : data1 3.
  Check [1;2] : data1 2.
  Check [1;2] : data1 3.
  Check [[1];[]] : data1 3.

  (** list list ∈ dim2 *)
  Check [] : data2 1 1.  (* note that, [] ∈ dimx, x >= 1 *)
  Check [[]] : data2 1 1.
  Check [[1;2];[3;4;5]] : data2 2 3.

  (** list list list ∈ dim3 *)
  Check [] : data3 1 1 1.
  Check [[]] : data3 1 1 1.
  Check [[[]]] : data3 1 1 1.
  Check [[[1;2];[3;4]];[[4;5];[6;7]]] : data3 2 2 2.

End Data.


(** matrix condition is a proposition *)
Section Cond.
  
  (** Length condition *)
  Definition CondL {A} (dims : Dims) (data : @Data A dims) : Prop.
    induction dims as [|n1 n'].
    - exact True.
    - induction data as [|d' d1].
      + exact (n1 = length n').
      + exact (n1 = S (length d1) /\ (IHn' d')).
(*    simpl in *. destruct d'. inversion d'. exact (width data).   *)
(*    exact (and (n1 = S (length d1)) (IHn' d')). *)
  Defined.

  (** dim0, any data is ok *)
  Compute CondL [] _.
  
  (** dim1, a list must have exact length *)
  Compute CondL [1] [].
  Compute CondL [2] [1;2].
  Compute CondL [3] [1;2;3].
  
  (** dim2, a list list must have exact length *)
  Compute CondL [4;5] [].
  Compute CondL [4;5] [[];[]].
  Compute CondL [4;5] [[1;2;3];[3;4];[4;5]].  (* Problem *)
  
  Reset CondL.
  
  
  Print Dims. (* Dims = list nat *)
  Print Data. (* Data = 
    fix Data (A : Type) (dims : Dims) {struct dims} :
        Type :=
      match dims with
      | [] => A
      | _ :: dims' => list (Data A dims')
      end
         : Type -> Dims -> Type 
  *)
  
  (* We must find a bility to destruct the Data structure *)
  (* Why the system could "destruct data" in CondL? what's the principle?
  *)

  (** A proposition that every list of a list list has same length *)
  Fixpoint width {A : Type} (dl : list (list A)) n : Prop :=
    match dl with
    | [] => True
    | x :: t => (n = length x) /\ width t n
    end.
  
  (* a demo data with dims[2;3;4] *)
  Section test.
    Let dims : Dims := [2;3;4].
    Let data : Data dims := [
      [[1;2;3;4];[1;2;3;4];[1;2;3;4]];
      [[1;2;3;4];[1;2;3;4];[1;2;3;4]]
     ].
    
    Variable Cond : forall A d, (@Data A d) -> Prop.
    Compute Cond _ dims data.
    Compute (tl data) : Data [3;4].
    
    (* top properties *)
    Compute length data = hd 0 dims.
    Compute width data 2.
    
    (* small problem *)
    Compute Cond _ [3;4] (tl data).
  
  End test.
  
  (* a demo data with a variable parameter *)
  Section test.
  
    Variable dimsx' : Dims.
    Definition dimsx : Dims := 3 :: dimsx'.
    Definition dims : Dims := 2 :: dimsx.
    
    Variable datax' : @Data nat dimsx'.
    Definition datax : Data dimsx := [datax'; datax'].
    Definition data : Data dims := [datax; datax].
    
    Variable Cond : forall A d, (@Data A d) -> Prop.
    
    (* top properties *)
    Compute length data = hd 0 dims.
    Compute width data 2.
    
    (* small problem *)
    Compute Cond _ dims data.
    Compute Cond _ dimsx datax.
    Compute Cond _ dimsx' datax'.
    
    (* write another form *)
    Compute (hd _ data).
    Compute Cond _ dimsx (hd _ data).
    Compute Cond _ dimsx' (hd _ (hd _ data)).
  
  End test.
  
  Fixpoint Cond {A} (dims : Dims) {struct dims} : (@Data A dims) -> Prop.
    destruct dims as [|n1 n'].
    - simpl. intros. apply True.  (* dims=[] *)
    - simpl. intros d.
      destruct d as [|d1 d'].
      + exact (n1 = 0). (* dims=n1::n', data=[] *)
      + destruct n' as [|n2 n''] eqn: Hn'.
        * exact True. (* dims=[n1], data=d1::d' *)
        * (* dims=[n1;n2;n'], data=d1::d' *)
          (* top properties *)
          Check n1 = length (d1 :: d').
          Check width (d') n1.
          
          (* small problem *)
          Check Cond _ (n2::n'') d1.
          
          exact (n1 = length (d1 :: d') 
            /\ width d' n1 
(*             /\ Cond _ (n2::n'') d1 *)  (* why here fail? *)
            ).
  Defined.
  
  (* 4=3 /\ 5=3 /\ 5=2 /\ 5=4 *)
  Compute Cond [4;5] [[1;2;3];[3;4];[5;6;7;8]].
  Compute Cond [2;3;4] [
    [[1;2;3;4];[1;2;3;4];[1;2;3;4]];
    [[1;2;3;4];[1;2;3;4];[1;2;3;4]]
   ].
  
  (** Rewrite with match *)
  Reset Cond.
  
  Fixpoint Cond {A : Type} (dims : Dims) 
(*     {struct dims}  *)
    : (@Data A dims) -> Prop :=
    match dims with
    (* dims=[] *)
    | [] => fun (data : @Data A []) => True
    (* dims=n1::n' *)
    | n1 :: n' => fun (data : list (@Data A n')) => 
      match data with
      (* data=[] *)
      | [] => n1 = 0 
      (* data=d1::d *)
      | d1 :: d' => match n' with
        (* dims=[n1] *)
        | [] => True
        (* dims=[n1;n2;n'] *)
        | n2 :: n'' =>
          n1 = length (d1 :: d')
(*             /\ width d' n1  *)
            /\ Cond _ d1  (* why here fail? *)
        end
      end
    end.
  
  Compute Cond [4;5] [[1;2;3];[3;4];[5;6;7;8]].
  Compute Cond [2;3;4] [
    [[1;2;3;4];[1;2;3;4];[1;2;3;4]];
    [[1;2;3;4];[1;2;3;4];[1;2;3;4]]
  ].
  
  (* last problem, width *)
  Reset Cond.
  
  (* Coq said Recursive ill-formed, because (n2::n'') *)
  Fail Fixpoint Cond {A : Type} (dims : Dims) 
    {struct dims} 
    : (@Data A dims) -> Prop :=
    match dims with
    (* dims=[] *)
    | [] => fun (data : @Data A []) => True
    (* dims=n1::n' *)
    | n1 :: n' => 
      match n' with
      (* dims=[n1] *)
      | [] => fun data => n1 = length data
      (* dims=n1::n2::n'' *)
      | n2 :: n'' => fun (data : list (@Data A (n2::n''))) => 
        match data with
        (* data=[] *)
        | [] => n1 = 0 
        (* data=d1::d' *)
        | d1 :: d' =>
          n1 = length (d1 :: d')
          /\ width d' n1   (* why here fail? *)
          /\ Cond _ d1
        end
      end
    end.
  
  
  (* again. width and Cond these two calling is hard to write together *)
  
  (* Coq said Recursive ill-formed *)
  Fixpoint Cond {A : Type} (dims : Dims) 
    {struct dims} 
    : (@Data A dims) -> Prop :=
    match dims with
    (* dims=[] *)
    | [] => fun (data : @Data A []) => True
    (* dims=n1::n' *)
    | n1 :: n' => fun (data : @Data A (n1::n')) => 
      match n' with
      (* dims=[n1] *)
      | [] => n1 = length data
      (* dims=n1::n2::n'' *)
      | n2 :: n'' => 
        match data with
        (* data=[] *)
        | [] => n1 = 0 
        (* data=d1::d' *)
        | d1 :: d' =>
          n1 = length (d1 :: d')
(*           /\ width d' n1   (* why here fail? *) *)
          /\ Cond _ d1
        end
      end
    end.
  
  Compute Cond [4;5] [[1;2;3];[3;4];[5;6;7;8]].
  Compute Cond [2;3;4] [
    [[1;2;3;4];[1;2;3;4];[1;2;3;4]];
    [[1;2;3;4];[1;2;3;4];[1;2;3;4]]
  ].
  
End Cond.

?

  (* 任意维矩阵定义 *)
  Record mat (dims : list nat) := {
    mat_data : mat_data_type dims;
    Cond : Cond_prop dims mat_data
  }

  (* 
    [2;3;4] 表示最内层是4个元素；然后是3层；最外面是2层。
    [] 表示空的矩阵。
  *)
  Variable dims' : list nat.

  Check list A.
  Check list (list A).

  (* 矩阵数据的类型 *)
  Fixpoint MatDataType (dims : list nat) : Type :=
    match dims with
    | [] => A
    | n :: dims' => list (MatDataType dims')
    end.

  Compute MatDataType [].
  Compute MatDataType [1].
  Compute MatDataType [1;2].
  Compute MatDataType [1;2;3].
  
  
(*   Inductive MatShape *)
(*   | 
   *)
  (* 矩阵形状要求：每个维度的数据都要满足长度要求 *)
(*   Fixpoint MatShapeProp (dims : list nat) : Prop :=
    match dims with
    | [] => True
    | n :: dims' => 
 *)
End Def.  

Check MatDataType nat [1;2].
Definition t1 := MatDataType nat [1;2].

(* 
1. 列表中元素数目，必然是 dims 的第一个元素的个数 
2. 列表
*)
Check [[1];[2]] : t1.

