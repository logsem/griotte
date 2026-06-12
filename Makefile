EXTRA_DIR = rocqdoc_extra
BUILD_DOC_DIR = _build/default/theories/cap_machine.html
PUBLISH_DIR = html

.PHONY: all theories rocqdoc html

all: theories rocqdoc

theories:
	dune build --display short --trace-file griotte.trc

pretty-timed: theories
	./pretty-print-trace.sh griotte.trc

rocqdoc: theories
	dune build @doc --display short

html: rocqdoc
	rm -rf $(PUBLISH_DIR)
	mkdir $(PUBLISH_DIR)
	cp $(BUILD_DOC_DIR)/* $(PUBLISH_DIR)
	chmod -R +w $(PUBLISH_DIR)
	cp $(EXTRA_DIR)/resources/* $(PUBLISH_DIR)

clean:
	dune clean
	rm -rf $(PUBLISH_DIR)
	rm -f griotte.trc

# Adapted from https://github.com/AbsInt/CompCert/blob/master/Makefile
check-admitted:
	@grep -w 'admit\|Admitted\|ADMITTED' -r ./theories ./machine_utils/theories || echo "Nothing admitted."
