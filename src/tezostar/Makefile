FSTAR_HOME?=~/everest/FStar

TEZOS?=~/tezos

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

include $(FSTAR_HOME)/ulib/ml/Makefile.include

NOEXTRACT=Classical FunctionalExtensionality List.Tot List.Tot.Properties Map \
	OrdMap OrdSet PredicateExtensionality Preorder PropositionalExtensionality \
	Reflection Reflection.Formula Reflection.Syntax Reflection.Syntax.Lemmas \
	StrongExcludedMiddle TSet Tactics Tactics.Derived Tactics.Effect Tactics.Logic

NOEXTRACT_MODULES+=$(addprefix FStar., $(NOEXTRACT))

FSTARINTERFACE=FStar_interface.fsti

CRYPTOINTERFACE=CryptoInterface.fsti

ERROR=Tezos.Error.fst

ERRORML=Tezos_Error.ml

TEZREPR=Tezos.TezRepr.fst

TEZREPRML=Tezos_TezRepr.ml

SCRIPTREPR=Tezos.ScriptRepr.fst

SCRIPTREPRML=Tezos_ScriptRepr.ml

LANGUAGE=Tezos.LanguageGadt.fst

LANGUAGEML=Tezos_LanguageGadt.ml

PRIMITIVES=Tezos.Primitives.fst

PRIMITIVESML=Tezos_Primitives.ml

DEFINITIONS=Tezos.Definitions.fst

DEFINITIONSML=Tezos_Definitions.ml

UNTYPED_DEFINITIONS=Tezos.UntypedDefinitions.fst

UNTYPED_DEFINITIONSML=Tezos_UntypedDefinitions.ml

STORAGE=Tezos.Storage.fst

STORAGEML=Tezos_Storage.ml

INTERPRETER=Tezos.Interpreter.fst

INTERPRETERML=Tezos_Interpreter.ml

SERIALIZATION=Tezos.Serialization.fst

SERIALIZATIONML=Tezos_Serialization.ml

TRANSLATION=Tezos.Translation.fst

TRANSLATIONML=Tezos_Translation.ml

ABS_INT=Tezos.AbstractInterpreter.fst

ABS_INTML=Tezos_AbstractInterpreter.ml

TEST=Tezos.Test.fst

TESTML=Tezos_Test.ml

TYPEDEXAMPLES=Tezos.TypedExamples.fst

TYPEDEXAMPLESML=Tezos_TypedExamples.ml

UNTYPEDEXAMPLES=Tezos.UntypedExamples.fst

UNTYPEDEXAMPLESML=Tezos_UntypedExamples.ml

$(PRIMITIVESML): $(PRIMITIVES)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(PRIMITIVES) --codegen OCaml

$(SCRIPTREPRML): $(SCRIPTREPR)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(SCRIPTREPR) --codegen OCaml

$(LANGUAGEML): $(LANGUAGE)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(LANGUAGE) --codegen OCaml

$(DEFINITIONSML): $(DEFINITIONS)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(DEFINITIONS) --codegen OCaml

$(UNTYPED_DEFINITIONSML): $(UNTYPED_DEFINITIONS) $(DEFINITIONS) $(PRIMITIVES)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(UNTYPED_DEFINITIONS) --codegen OCaml

$(STORAGEML):
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(STORAGE) --codegen OCaml

$(INTERPRETERML): $(PRIMITIVES) $(INTERPRETER) $(UNTYPED_DEFINITIONS) $(DEFINITIONS) $(STORAGE) $(ERROR)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(INTERPRETER) --codegen OCaml

$(SERIALIZATIONML):
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(SERIALIZATION) --codegen OCaml

$(ABS_INTML): $(ABS_INT)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(ABS_INT) --codegen OCaml

$(TRANSLATIONML): $(TRANSLATION) $(ABS_INT) $(PRIMITIVES) $(LANGUAGE) $(UNTYPED_DEFINITIONS) $(DEFINITIONS) $(ERROR) $(SCRIPTREPR) $(STORAGE) $(CRYPTOINTERFACE) $(FSTARINTERFACE)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(TRANSLATION) --codegen OCaml

$(TESTML): $(TEST) $(PRIMITIVES) $(DEFINITIONS) $(UNTYPED_DEFINITIONS) $(TEZREPR) $(STORAGE) $(SERIALIZATION) $(ABS_INT) $(LANGUAGE) $(TRANSLATION) $(INTERPRETER) $(CRYPTOINTERFACE) $(FSTARINTERFACE) 
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(TEST) --codegen OCaml


# abs_int: $(DEFINITIONSML) $(ABS_INTML)
# 	$(OCAMLOPT) $(DEFINITIONSML) $(ABS_INTML) -o abs_int.exe
# 	./abs_int.exe

factorial: $(LANGUAGEML) $(DEFINITIONSML)
	$(OCAMLOPT) $(DEFINITIONSML) $(LANGUAGEML) -o factorial.exe
	./factorial.exe

test_prelim: $(FSTARINTERFACE) $(SCRIPTREPRML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(FSTARINTERFACE) --codegen OCaml
	$(OCAMLOPT) -i $(SCRIPTREPRML) > Tezos_ScriptRepr.mli
	$(OCAMLOPT) -c -I . $(SCRIPTREPRML) ocaml/CryptoInterface.mli -o CryptoInterface.cmi
	$(OCAMLOPT) -c -I . -I ocaml/ ocaml/Tezos_ScriptRepr.mli  -o FStar_interface.cmi # create FStar_interface.cmi

	$(OCAMLOPT) -c -I . -I ocaml/ ocaml/Tezos_ScriptRepr.mli $(SCRIPTREPRML) ocaml/FStar_interface.mli -o FStar_interface.cmi # create FStar_interface.cmi

test: $(TESTML)
	$(OCAMLOPT)  -I $(TEZOS)/src/ -I $(TEZOS)/src/proto/ -I $(TEZOS)/src/client/embedded/ -I $(TEZOS)/src/utils -I $(TEZOS)/src/minutils -I $(TEZOS)/src/node/updater -I . -I ocaml -thread -package calendar -package cohttp -package conduit -package ezjsonm -package git -package git-unix -package irmin -package irmin-unix -package lwt -package lwt_ssl -package mtime.clock.os -package ocplib-endian -package ocplib-json-typed.bson -package ocplib-resto.directory -package dynlink -package reactiveData -package sodium -package compiler-libs.optcomp -package magic-mime -package leveldb -package kaputt -package bisect_ppx $(TEZOS)/src/minutils.cmxa $(TEZOS)/src/utils.cmxa $(TEZOS)/src/compiler.cmxa $(TEZOS)/src/node.cmxa  $(TEZOS)/src/client.cmxa $(TEZOS)/src/proto/client_embedded_proto_alpha.cmxa  $(TEZOS)/src/client/embedded/client_alpha.cmx $(SCRIPTREPRML) ocaml/FStar_interface.mli ocaml/FStar_interface.ml $(ERRORML)  ocaml/CryptoInterface.mli ocaml/CryptoInterface.ml $(PRIMITIVESML) $(DEFINITIONSML) $(UNTYPED_DEFINITIONSML) $(TEZREPRML) $(STORAGEML) $(SERIALIZATIONML) $(ABS_INTML) $(LANGUAGEML) $(TRANSLATIONML) $(INTERPRETERML) $(TESTML) -o test.exe
	./test.exe

interpreter: $(PRIMITIVESML) $(DEFINITIONSML) $(SCRIPTREPRML) $(UNTYPED_DEFINITIONSML) $(ERRORML) $(TEZREPRML) $(STORAGEML) $(INTERPRETERML)
	$(OCAMLOPT) $(PRIMITIVESML) $(DEFINITIONSML) $(SCRIPTREPRML) $(UNTYPED_DEFINITIONSML) $(ERRORML) $(TEZREPRML) $(STORAGEML)  $(INTERPRETERML) -o interpreter.exe
	./interpreter.exe

all:
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(DEFINITIONS) $(STORAGE) $(UNTYPED_DEFINITIONS) $(LANGUAGE_GADT) $(SERIALIZATION) $(TRANSLATION) $(TEST) $(TYPEDEXAMPLES) $(UNTYPEDEXAMPLES)

clean:
	rm -f $(SCRIPTREPRML) $(DEFINITIONSML) $(STORAGEML) $(UNTYPED_DEFINITIONSML) $(LANGUAGE_GADTML) $(SERIALIZATIONML) $(TRANSLATIONML) $(TESTML) $(TYPEDEXAMPLESML) $(UNTYPEDEXAMPLESML) *.out *.ml *.o *.cmo *.cma *.cmi *.cmx ocaml/*.o ocaml/*.cmo ocaml/*.cma ocaml/*.cmi ocaml/*.cmx *.exe

# $(DEFINITIONS:.fst=.c): $(DEFINITIONS)
# 	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(DEFINITIONS) --codegen Kremlin

# $(ABS_INT:.fst=.c): $(ABS_INT)
# 	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(ABS_INT) --codegen Kremlin

# abs_int_c: $(DEFINITIONS:.fst=.c) $(ABS_INT:.fst=.c)
# 	gcc $(DEFINITIONS:.fst=.c) $(ABS_INT:.fst=.c) -o abs_int_c.exe
# 	./abs_int_c.exe
