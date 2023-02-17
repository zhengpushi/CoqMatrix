# Copyright 2022 ZhengPu Shi
# This file is part of CoqMatrix. It is distributed under the MIT
# "expat license". You should have recieved a LICENSE file with it.



mat_test.exe : mat_test.ml mat.cmo inv.cmo
	-@rm -f *.mli
	ocamlc.opt.exe -o mat_test.exe mat.cmo inv.cmo $<

%.cmo : %.ml
	ocamlc.opt.exe -o $@ -c $<

# %.cmi : %.mli
# 	ocamlc.opt.exe -o $@ -c $<

exec: mat_test.exe
	./mat_test.exe

clean:
	rm -f *.cmo *.cmi
