# FStar variables
FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

OPTIONS_VER=

LIB_DIR=.
LIB_FILES=$(addprefix $(LIB_DIR)/, Solidity.fst)

.PHONY: lib-ver

all: lib-ver lockmyether-lax lockmyether-ver

# Verification target for the low-level libraries of F* in universes
ver:
	$(FSTAR) $(OPTIONS_VER) $(LIB_FILES)

# lax typechecking
lockmyether-lax:
	$(FSTAR) $(OPTIONS_VER) $(LIB_FILES) lockmyether.fst --lax

# verification
lockmyether-ver:
	$(FSTAR) $(OPTIONS_VER) $(LIB_FILES) lockmyether.fst 

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f *~

