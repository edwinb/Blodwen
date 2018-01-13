module Idris.ProcessIdr

import Core.Binary
import Core.TT
import Core.Normalise
import Core.Typecheck
import Core.Unify
import Core.Context

import TTImp.Elab
import TTImp.ProcessData
import TTImp.ProcessDef
import TTImp.ProcessType
import TTImp.TTImp

import Idris.Syntax

import Control.Catchable
import Interfaces.FileIO

export
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState ())} ->
          String -> Core () ()
