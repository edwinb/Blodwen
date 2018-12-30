PREFIX = ${HOME}/.blodwen
export BLODWEN_PATH = ${CURDIR}/prelude/build:${CURDIR}/base/build
export BLODWEN_DATA = ${CURDIR}/support
PLATFORM =
BLODWEN = ../blodwen$(PLATFORM)
COMPILER_PLATFORM := $(if $(PLATFORM),$(PLATFORM),c)

.PHONY: ttimp blodwen prelude test base clean lib_clean src/CompilerRuntime.idr

all: ttimp blodwen prelude base test

ttimp: src/CompilerRuntime.idr
	idris --build ttimp$(PLATFORM).ipkg

blodwen: src/BlodwenPaths.idr src/CompilerRuntime.idr
	idris --build blodwen$(PLATFORM).ipkg

src/CompilerRuntime.idr:
	cp src/CompilerRuntime.$(COMPILER_PLATFORM).idr src/CompilerRuntime.idr

src/BlodwenPaths.idr:
	echo 'module BlodwenPaths; export bprefix : String; bprefix = "${PREFIX}"' > src/BlodwenPaths.idr

prelude:
	make -C prelude BLODWEN=$(BLODWEN)

base: prelude
	make -C base BLODWEN=$(BLODWEN)

libs : prelude base

clean: lib_clean
	make -C src clean
	make -C tests clean
	rm -f blodwen
	rm -f runtests
	rm -f ttimp

lib_clean:
	make -C prelude clean
	make -C base clean

test:
	idris --build test.ipkg
	make -C tests

install:
	mkdir -p ${PREFIX}/bin
	mkdir -p ${PREFIX}/blodwen/support/chez
	mkdir -p ${PREFIX}/blodwen/support/chicken
	mkdir -p ${PREFIX}/blodwen/support/racket
	make -C prelude install BLODWEN=$(BLODWEN)
	make -C base install BLODWEN=$(BLODWEN)

	install blodwen ${PREFIX}/bin
	install support/chez/* ${PREFIX}/blodwen/support/chez
	install support/chicken/* ${PREFIX}/blodwen/support/chicken
	install support/racket/* ${PREFIX}/blodwen/support/racket
