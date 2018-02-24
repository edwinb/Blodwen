Some unsorted notes on aspects of the implementation. Sketchy, but hopefully
give some hints as to what's going on and some ideas where to look in the
code to see how certain features work.

Overview
--------
Core language TT (defined in Core.TT), indexed over the names in scope so
that we know terms are always well scoped. Values (i.e. normal forms) also
defined in Core.TT as NF; constructors do not evaluate their arguments until
explicitly requested.

Elaborate to TT from a higher level language TTImp (defined in TTImp.TTImp),
which is TT with implicit arguments, local function definitions, case blocks,
as patterns, qualified names with automatic type-directed disambiguation, and
proof search.

Elaboration relies on unification (in Core.Unify), which allows postponing
of unification problems. Essentially works the same way as Agda as described
in Ulf Norrel's thesis.

General idea is that high level languages will provide a translation to TT.
In the Idris/ namespace we define the high level syntax for Idris, which
translates to TTImp by desugaring operators, do notation, etc.

Where to find things:

Core/ -- anything related to the core TT, typechecking and unification
TTImp/ -- anything related to the implicit TT and its elaboration
Parser/ -- various utilities for parsing and lexing TT and TTImp (and other things)
Utils/ -- some generally useful utilities
Idris/ -- anything relating to the high level language, translating to TTImp

The Core Type, and Ref
----------------------
Core is a "monad" (not really, for efficiency reasons, at the moment...)
supporting Errors and IO [TODO: Allow restricting to specific IO operations]
and parameterised by an "annotation" type. The "annotation" type can be used
to propagate location information through elaboration - the raw syntax is
defined by a type RawImp which has an annotation at each node, and any
errors in elaboration note the annotation at the point where the error
occurred.

'Ref' is essentially an IORef. Typically we pass them implicitly and use
labels to disambiguate which one we mean. See Core.Core for their
definition. Again, IORef is for efficiency - even if it would be neater to
use a state monad this turned out to be about 2-3 times faster, so I'm
going with the "ugly" choice...

Context
-------
Core.Context defines all the things needed for TT. Most importantly: Def 
gives definitions of names (case trees, builtins, constructors and
holes, mostly); GlobalDef is a definition with all the other information
about it (type, visibility, totality, etc); Gamma is a context mapping names
to GlobalDef, and 'Defs' is the core data structure with everything needed to
typecheck more definitions.

Contexts are, essentially, hierarchical dictionaries. You can either
use a lookupXExact if you know an exact name, or lookupX if you want a list
of all the things which match a fragment of a name.

TTC format
----------
We can save things to binary if we have an implementaiton of the TTC interface
for it. See Utils.Binary to see how this is done. It uses a global reference
'Ref Bin Binary' which uses Data.Buffer underneath.

Bound Implicits
---------------
The RawImp type has a constructor IBindVar. The first time we encounter an
IBindVar, we record the name as one which will be implicitly bound. At the
end of elaboration, we decide which holes should turn into bound variables
(Pi bound in types, Pattern bound on a LHS, still holes on the RHS) by
looking at the list of names bound as IBindVar, the things they depend on,
and sorting them so that they are bound in dependency order. This happens
in State.getToBind.

Once we know what the bound implicits need to be, we bind them in 
'bindImplicits'. Any application of a hole which stands for a bound implicit
gets turned into a local binding (either Pi or Pat as appropriate, or PLet for
@-patterns).

Implicit arguments
------------------
When we encounter an implicit argument ('_' in the raw syntax, or added when
we elaborate an application and see that there is an implicit needed) we
make a new hole which is a fresh name applied to the current environment,
and return that as the elaborated term. If there's enough information elsewhere
we'll find the definition of the hole by unification.

We never substitute holes in a term during elaboration and rely on normalisation
if we need to look inside it. After elaboration, we normalise all the holes in
a term, so it's safe to remove their definitions if elaboration is successful.
If there are holes remaining after elaboration of a definition, report an
error (it's okay for a hole in a type as long as it's resolved by the time the
definition is done).

See Term.makeImplicit and Term.makeAutoImplicit to see where we add holes for
the implicit arguments in applications

Core.Unify.solveConstraints revisits all of the currently unsolved holes and
constrained definitions, and tries again to unify any constraints which they
require. It also tries to resolve anything defined by proof search.

Dot Patterns
------------
IMustUnify is a constructor of RawImp. When we elaborate this, we generate a
hole, then elaborate the term, and add a constraint that the generated hole
must unify with the term which was explicitly given (in UnifyState.addDot),
finally checked in 'UnifyState.checkDots'

Proof Search
------------
A definition with the body 'BySearch' is a hole which will be resolved
by searching for something which fits the type. This happens in
Core.AutoSearch.

At the minute, it just takes the first thing which fits the type - we'll need
to add various constraints on it later (e.g. for dealing with interfaces
effectively)

@-Patterns
----------
There a pattern binding PLet in the core theory, which binds a name as
being equal to something using other pattern bindings. See 
TTImp.Elab.Term.checkAs. To elaborate, we check the pattern term as usual,
add a new hole for the @-pattern variable name and assert that it converts
(therefore unifies) with the pattern. Then, when we get to bindImplicits,
we'll see that the @-pattern name is defined, so turn it into a PLet.

Linear Types
------------
Following Conor McBride and Bob Atkey's work, all binders have a multiplicity
annotation ("RigCount"). After elaboration in TTImp.Elab, we do a separate
linearity check which: a) makes sure that linear variables are used exactly
once; b) updates hole types to properly reflect usage information.

Local definitions
-----------------
We elaborate relative to an environment, meaning that we can elaborate local
function definitions. We keep track of the names being defined in a nested
block of declarations, and ensure that they are lifted to top level definitions
in TT by applying them to every name in scope.

Since we don't know how many times a loca definition will be applied, in general,
anything bound with multiplicity 1 is passed to the local definition with
multiplicity 0, so if you want to use it in a local definition, you need to
pass it explicitly.

Case blocks
-----------
Similar to local definitions, these are lifted to top level definitions which
represent the case block, which is immediately applied to the scrutinee of
the case.  The function which defines the block takes as arguments: the entire
current environment (so that it can use any name in scope); any names in
the environment which the scrutinee's type depends on (to support dependent
case, but not counting parameters which are unchanged across the structure).

Parameters
----------
The parameters to a data type are taken to be the arguments which appear,
unchanged, in the same position, everywhere across a data definition.

Forcing
-------
Forced arguments to constructors are those which are constructor guarded in
the indices of the constructor. They get erased during elaboration (in
TTImp.Elab.Term) in 'checkExp' so the result of type checking has already
erased arguments.
