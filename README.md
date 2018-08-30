Blodwen
=======

This is a prototype of a possible successor to Idris. To build and install 
what exists of it so far:

+ Optionally, set the `PREFIX` in `Makefile`
+ `make all`
  + This builds the main executable `blodwen`, and a minimal dependently
    typed language with implicit syntax, `ttimp`. Most likely you'll only
    need `blodwen`; `ttimp` is useful for testing/debugging.
+ `make install`

You'll need to set your `PATH` to `$PREFIX/bin`
You may also want to set `IDRIS_CC` to `clang`, since this seems to build
the generated C significantly faster.

Note: If you edit `blodwen.ipkg` to use the `opts` with optimisation set
(`--cg-opt -O2`) you'll find it runs about twice as fast, at the cost of
taking a couple of minutes to generate the `blodwen` executable.

I make no promises how well this works yet, or even if it'll work at all. 
Good luck :).

(Why "Blodwen"? The answer is here: http://ivortheengine.wikia.com/wiki/Idris)

Things still missing
--------------------

+ Some high level syntax, notably 'with', 'rewrite', dependent pairs,
  numeric ranges 
+ Cumulativity and totality checking
+ Codata (or rather, you can have it, but there's no productivity check...)
+ Any kind of interactive editing/IDE mode
+ Documentation strings
+ The rest of this "Things still missing" list
