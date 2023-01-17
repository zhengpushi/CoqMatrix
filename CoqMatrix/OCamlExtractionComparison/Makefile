# Copyright 2022 ZhengPu Shi
# This file is part of CoqMatrix. It is distributed under the MIT
# "expat license". You should have recieved a LICENSE file with it.


matrix : matrix.ml
	@ocamlc -c matrix.mli
	@ocamlfind ocamlc -o $@ -linkpkg matrix.ml -package unix

clean :
	rm -f matrix *.cmi *.cmo *.o

.PHONY : clean
