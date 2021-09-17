.PHONY: all clean dep
all:
	ocamlbuild -j 4 -use-ocamlfind soliditystar.native

clean:
	rm soliditystar.native _build -fr

dep:
	ocamlfind -query batteries str unix menhirLib ulex camlp4 -format "%p (%D): %v"

