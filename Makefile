.PHONY: all theories doc

all: theories doc

theories:
	dune build --display short

doc:
	dune build @doc --display short

clean:
	dune clean
