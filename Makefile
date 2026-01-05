.PHONY: all theories doc

all: theories doc

theories:
	dune build --display short --trace-file griotte.trc --trace-extended

pretty-timed: theories
	./pretty-print-trace.sh griotte.trc

doc:
	dune build @doc --display short

clean:
	dune clean
	rm -f griotte.trc

# Adapted from https://github.com/AbsInt/CompCert/blob/master/Makefile
check-admitted:
	@grep -w 'admit\|Admitted\|ADMITTED' -r ./theories ./machine_utils/theories || echo "Nothing admitted."
