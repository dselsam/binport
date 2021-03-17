/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import MathPort.Util
import MathPort.Path
import Lean
import Std.Data.HashSet
import Std.Data.HashMap

namespace MathPort

open Lean Lean.Meta Lean.Elab Lean.Elab.Command
open Std (HashSet mkHashSet HashMap mkHashMap)

structure Context where
  proofs : Bool
  path   : Path34

structure ExportInfo where
  names  : Array Name        := #[Name.anonymous]
  levels : Array Level       := #[levelZero]
  exprs  : Array Expr        := #[]

structure Rules where
  newNames     : HashMap Name Name := {}
  ignored      : HashSet Name      := {}
  sorries      : HashSet Name      := {}
  neverSorries : HashSet Name      := {} -- e.g. of_as_true
  noInsts      : HashSet Name      := {}

structure State extends ExportInfo, Rules where
  decl           : Name                     := `unknown
  irreducibles   : HashSet Name             := {}
  nNotations     : Nat                      := 0
  name2equations : HashMap Name (List Name) := {}


abbrev PortM := ReaderT Context $ StateRefT State CommandElabM

variable {α : Type}

def warnStr (msg : String) : PortM Unit := do
  let ctx ← read
  let s ← get
  println! "[warning] while processing {ctx.path.mrpath.path}::{s.decl}:\n{msg}"

def warn (ex : Exception) : PortM Unit := do warnStr (← ex.toMessageData.toString)

def liftMetaM {α} (x : MetaM α) : PortM α := do
  let s ← get
  liftTermElabM (declName? := some s.decl) (liftM x)

-- TODO: thread more implicits through
def PortM.toIO (x : PortM α) (ctx : Context) (env : Environment) : IO α := do
  let x₁ : CommandElabM α := (x ctx).run' {}

  let cmdCtx : Lean.Elab.Command.Context := {
    fileName := ctx.path.mrpath.toDotPath.path,
    fileMap  := FileMap.ofString "code panics if there is nothing here"
  }

  let cmdState : Lean.Elab.Command.State := Lean.Elab.Command.mkState env

  let x₂ : Except Exception α ← (x₁ cmdCtx).run' cmdState |>.toIO'
  match x₂ with
  | Except.error (Exception.error _ msg)   => do let e ← msg.toString; throw $ IO.userError e
  | Except.error (Exception.internal id _) => throw $ IO.userError $ "internal exception #" ++ toString id.idx
  | Except.ok a => pure a

def mkOldRecName (n : Name) : Name := n ++ "_oldrec"

end MathPort
