# Copyright 2023 ZhengPu Shi
# This file is part of CoqMatrix. It is distributed under the MIT
# "expat license". You should have recieved a LICENSE file with it.


test : test.ml matrix.ml
	@ocamlc -o $@ uint63.ml parray.ml matrix.mli matrix.ml test.ml
	# @ocamlc -c matrix.mli
	# @ocamlfind ocamlc -o $@ -linkpkg matrix.ml -package unix Uint63

# matrix : matrix.ml
# 	@ocamlc.opt -c matrix.mli
# 	@ocamlfind opt -o $@ -linkpkg matrix.ml -package unix

clean :
	rm -f matrix *.cmi *.cmo *.o

.PHONY : clean
