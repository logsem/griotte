FUNDAMENTAL		:=	 theories/fundamental.v
COQMAKEFILE 	?=   Makefile.coq
COQ_PROJ 		?= _CoqProject

all: $(COQMAKEFILE)
		+@$(MAKE) -f $^ $@

# Forward `make` commands to `$(COQMAKEFILE)`
%: $(COQMAKEFILE)
		+@$(MAKE) -f $^ $@

fundamental: export TGTS=${FUNDAMENTAL:.v=.vo}
fundamental: $(COQMAKEFILE) only

$(COQMAKEFILE): $(COQ_PROJ)
		coq_makefile -f $^ -o $@

.PHONY: all fundamental ci

# Thanks to Vincent Lafeychine for the help to refactor the Makefile

# # Adapted from https://github.com/AbsInt/CompCert/blob/master/Makefile
# check-admitted: $(COQMAKEFILE)
# 	@grep -w 'admit\|Admitted\|ADMITTED' $(COQMF_VFILES) || echo "Nothing admitted."
