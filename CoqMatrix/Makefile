# ===================================================================
# Copyright 2022 ZhengPu Shi
#  This file is part of CoqMatrix. It is distributed under the MIT
#  "expat license". You should have recieved a LICENSE file with it.
# ===================================================================

COQMAKEFILE ?= Makefile.coq

HTML_EXTRA_DIR = html-extra
COQDOCFLAGS ?= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage \
  --no-lib-name \
  --with-header $(HTML_EXTRA_DIR)/header.html \
  --with-footer $(HTML_EXTRA_DIR)/footer.html \
  --parse-comments
export COQDOCFLAGS

all: $(COQMAKEFILE)
	$(MAKE) -f $^ $@

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

clean: $(COQMAKEFILE)
	$(MAKE) -f $^ cleanall

cleanall: $(COQMAKEFILE)
	$(MAKE) -f $^ cleanall
	$(RM) $^ $^.conf

html: $(COQMAKEFILE)
	$(MAKE) -f $^ $@
	cp $(HTML_EXTRA_DIR)/* html/ -R

install: $(COQMAKEFILE)
	$(MAKE) -f $^ install

uninstall: $(COQMAKEFILE)
	$(MAKE) -f $^ uninstall


.PHONY: all clean cleanall html install uninstall
