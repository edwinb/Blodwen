INSTALL ?= install
MKDIR   ?= $(INSTALL) -d
DESTDIR ?=
PREFIX  ?= ${HOME}/.blodwen
BINDIR  ?= $(PREFIX)/bin

export BLODWEN_PATH = ${CURDIR}/prelude/build:${CURDIR}/base/build
export BLODWEN_DATA = ${CURDIR}/support

.PHONY: ttimp blodwen prelude test base clean lib_clean

all: ttimp blodwen prelude base

ttimp:
	idris --build ttimp.ipkg

blodwen: src/BlodwenPaths.idr
	idris --build blodwen.ipkg

src/BlodwenPaths.idr:
	echo 'module BlodwenPaths; export bprefix : String; bprefix = "${PREFIX}"' > src/BlodwenPaths.idr

prelude: blodwen
	make -C prelude BLODWEN=../blodwen

base: prelude
	make -C base BLODWEN=../blodwen

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

test: base
	idris --build test.ipkg
	make -C tests

install:
	$(MKDIR) ${DESTDIR}${BINDIR}
	$(MKDIR) ${DESTDIR}${PREFIX}/blodwen/support/chez
	$(MKDIR) ${DESTDIR}${PREFIX}/blodwen/support/chicken
	$(MKDIR) ${DESTDIR}${PREFIX}/blodwen/support/racket

	$(INSTALL) blodwen ${DESTDIR}${BINDIR}
	$(INSTALL) support/chez/* ${DESTDIR}${PREFIX}/blodwen/support/chez
	$(INSTALL) support/chicken/* ${DESTDIR}${PREFIX}/blodwen/support/chicken
	$(INSTALL) support/racket/* ${DESTDIR}${PREFIX}/blodwen/support/racket
