PREFIX = ${HOME}/.blodwen
export BLODWEN_PATH = ${CURDIR}/prelude/build

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
	mkdir -p ${PREFIX}/blodwen/prelude
	install blodwen ${PREFIX}/bin
	install prelude/build/* ${PREFIX}/blodwen/prelude
