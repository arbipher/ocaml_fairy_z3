default: build

run:
	dune exec bin/main.exe

build:
	dune build

see:
	dune build --auto-promote

test:
	dune runtest -f

utop:
	dune utop . -- -implicit-bindings

promote:
	dune runtest -f --auto-promote

install:
	dune install

uninstall:
	dune uninstall

clean:
	dune clean

.PHONY: default build install uninstall test clean