.PHONY: ttimp blodwen prelude test

all: ttimp blodwen prelude test

ttimp:
	idris --build ttimp.ipkg

blodwen:
	idris --build blodwen.ipkg

prelude: blodwen
	make -C prelude BLODWEN=../blodwen

test:
	idris --build test.ipkg
	make -C tests
