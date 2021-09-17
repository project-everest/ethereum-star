.PHONY: all clean

OCAML = ocamlfind ocamlc
OCAMLOPTS=-package batteries -linkpkg -g -thread

MLFILES=Ast.ml GasCost.ml Parse.ml Disasm.ml EvmParser.ml

OBJ=EvmStar

all: evmparser

clean:
	rm -rf $(OBJ) a.out *.o *.a *.cmi *.cm? *~ *.exe

evmparser: $(MLFILES)
	$(OCAML) $(OCAMLOPTS) $^ -o $(OBJ).exe


#disasm: Ast.ml Parse.ml Disasm.ml
#	$(OCAML) $(OCAMLOPTS) $^ -o Disasm.exe

