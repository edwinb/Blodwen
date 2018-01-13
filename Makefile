.PHONY: ttimp blodwen test

ttimp:
	idris --build ttimp.ipkg

blodwen:
	idris --build blodwen.ipkg

test:
	idris --build test.ipkg
	./runtests
