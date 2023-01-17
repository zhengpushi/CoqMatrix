编译注意事项
1. 由于Coq生成OCaml代码时，Extraction指定了如下操作
Extract Constant Rabst => "__".
Extract Constant Rrepr => "__".
导致，mat.mli 与 mat.ml 在编译时报签名不一致的错误，
所以暂时不要用 mli 文件了。
