module Core.Metadata

import Core.Context
import Core.TT

-- Additional data we keep about the context to support interactive editing

public export
record Metadata annot where
       constructor MkMetadata
       -- A mapping from source annotation (location, typically) to
       -- the LHS defined at that location
       lhsapps : List (annot, (vars ** (Env Term vars, Term vars)))

export
initMetadata : Metadata annot
initMetadata = MkMetadata []

-- A label for metadata in the global state
export
data Meta : Type where
