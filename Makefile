.PHONY: all theories doc

all: theories doc

theories:
	dune build --display short

doc:
	dune build @doc --display short

clean:
	dune clean

# Adapted from https://github.com/AbsInt/CompCert/blob/master/Makefile
check-admitted:
	@grep -w 'admit\|Admitted\|ADMITTED' -r ./theories ./machine_utils/theories || echo "Nothing admitted."
