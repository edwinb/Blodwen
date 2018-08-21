PREFIX = ${HOME}/.blodwen
export BLODWEN_PATH = ${CURDIR}/prelude/build
export BLODWEN_DATA = ${CURDIR}/support

.PHONY: ttimp blodwen prelude test

all: ttimp blodwen prelude test

ttimp:
	idris --build ttimp.ipkg

blodwen: src/BlodwenPaths.idr
	idris --build blodwen.ipkg

src/BlodwenPaths.idr:
	echo 'module BlodwenPaths; export bprefix : String; bprefix = "${PREFIX}"' > src/BlodwenPaths.idr

prelude:
	make -C prelude BLODWEN=../blodwen

test:
	idris --build test.ipkg
	make -C tests

install:
	mkdir -p ${PREFIX}/bin
	mkdir -p ${PREFIX}/blodwen/support/chez
	mkdir -p ${PREFIX}/blodwen/support/chicken
	mkdir -p ${PREFIX}/blodwen/support/racket
	make -C prelude install BLODWEN=../blodwen

	install blodwen ${PREFIX}/bin
	install support/chez/* ${PREFIX}/blodwen/support/chez
	install support/chicken/* ${PREFIX}/blodwen/support/chicken
	install support/racket/* ${PREFIX}/blodwen/support/racket
