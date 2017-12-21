.PHONY: blodwen test

blodwen:
	idris --build blodwen.ipkg

test:
	idris --build test.ipkg
	./runtests
