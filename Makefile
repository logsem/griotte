EXTRA_DIR:=extra
COQDOCFLAGS:= \
  --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
  --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
MAKEFILE_COQ_CONF:=Makefile.coq.conf

# Adapted from https://gist.github.com/diegolagoglez/76b28c60054aa20d665f
ifeq ($(MAKECMDGOALS),check-admitted)
    ifeq ($(strip $(wildcard $(MAKEFILE_COQ_CONF))),)
        $(error Config file '$(MAKEFILE_COQ_CONF)' does not exist. Please, use 'make Makefile.coq' before)
    else
        include $(MAKEFILE_COQ_CONF)
    endif
endif

.PHONY: all coq clean Makefile.coq html
all: coq

fundamental: Makefile.coq
	$(MAKE) -f Makefile.coq only TGTS="theories/fundamental.vo"

fundamental-binary: Makefile.coq
	$(MAKE) -f Makefile.coq only TGTS="theories/binary_model/fundamental_binary.vo"

full-abstraction: Makefile.coq
	$(MAKE) -f Makefile.coq only TGTS="theories/full_abstraction.vo"

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

html: Makefile.coq
	rm -rf html
	$(MAKE) -f Makefile.coq html
	cp $(EXTRA_DIR)/resources/* html

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

# Adapted from https://github.com/AbsInt/CompCert/blob/master/Makefile
check-admitted: Makefile.coq
	@grep -w 'admit\|Admitted\|ADMITTED' $(COQMF_VFILES) || echo "Nothing admitted."

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	rm -rf html
