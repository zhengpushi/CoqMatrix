# Copyright 2024 ZhengPu Shi
# This file is part of VFCS. It is distributed under the MIT
# "expat license". You should have recieved a LICENSE file with it.


# byte-code version
# matrix : matrix.ml
# 	@ocamlc -c matrix.mli
# 	@ocamlfind ocamlc -o $@ -linkpkg matrix.ml -package unix

# opt version
matrix : matrix.ml
	@ocamlc.opt -c matrix.mli
	@ocamlfind opt -o $@ -linkpkg matrix.ml -package unix

clean :
	rm -f *.cmi *.cmo *.o
	rm -f matrix

.PHONY : clean
