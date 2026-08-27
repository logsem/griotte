EXTRA_DIR = rocqdoc_extra
BUILD_DOC_DIR = _build/default/theories/griotte.html
PUBLISH_DIR = html

.PHONY: all theories rocqdoc html extract-files extract

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

extract-files:
	dune build extraction/griotte_extracted.ml extraction/griotte_extracted.mli

extract: extract-files
	@if [ -n "$(EXTRACT_DEST)" ]; then \
		mkdir -p "$(EXTRACT_DEST)"; \
		install -m 0644 _build/default/extraction/griotte_extracted.ml \
			"$(EXTRACT_DEST)/griotte_extracted.ml"; \
		install -m 0644 _build/default/extraction/griotte_extracted.mli \
			"$(EXTRACT_DEST)/griotte_extracted.mli"; \
		echo "Updated extracted OCaml files in $(EXTRACT_DEST)"; \
	else \
		echo "Generated OCaml files in $(CURDIR)/_build/default/extraction"; \
	fi
