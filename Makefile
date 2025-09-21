.PHONY: all theories

all: theories

theories:
	dune build --display short

clean:
	dune clean
