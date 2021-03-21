/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Std.Data.HashSet

open Lean Lean.Meta Lean.Elab.Term
open Std (HashSet mkHashSet)

namespace DelaborateExperiment

def BLACK_LIST : HashSet Name :=
  (({} : HashSet Name).insert `Mathlib.CommRing.colimits.relation.casesOn).insert `Mathlib.Mon.colimits.relation.casesOn

inductive DelaborateResult where
  | success           : DelaborateResult
  | failedToElaborate : DelaborateResult
  | sorryAx           : DelaborateResult
  | nonDefEq          : DelaborateResult
  | timeout           : DelaborateResult
  | other             : DelaborateResult
  deriving Inhabited

instance : ToString DelaborateResult := ⟨fun
  | DelaborateResult.success           => "success"
  | DelaborateResult.failedToElaborate => "failedToElaborate"
  | DelaborateResult.sorryAx           => "sorryAx"
  | DelaborateResult.nonDefEq          => "nonDefEq"
  | DelaborateResult.timeout           => "timeout"
  | DelaborateResult.other             => "other"
⟩

structure DataPoint where
  declName : Name
  inType   : Bool
  result   : DelaborateResult

abbrev Job := Task (Except IO.Error (Array DataPoint))

instance : Inhabited Job := ⟨⟨pure #[]⟩⟩

structure Context where

structure State where
  datapoints : Array DataPoint := #[]

abbrev DelaborateExperimentM := ReaderT Context (StateRefT State MetaM)

def emit (datapoint : DataPoint) : DelaborateExperimentM Unit :=
  modify fun s => { s with datapoints := s.datapoints.push datapoint }

def elabCtx : Lean.Elab.Term.Context := {
  fileName := "<no-file>"
  fileMap  := FileMap.ofString "code panics if there is nothing here"
}

def checkExpr (declName : Name) (inType : Bool) (e : Expr) : DelaborateExperimentM Unit := do
  -- TODO: huh? why the errors without the braces?
  try {
    let type ← inferType e
    -- Notes:
    --   - declName.getPrefix is also the currentNamespace passed to CoreM
    --   - the pretty printing options are declared in `withEnvOpts` below
    --     - (by default, pp.all is set to true)
    let stx ← Lean.PrettyPrinter.delab declName.getPrefix [] e
    try {
      let e' ← TermElabM.run' (ctx := elabCtx) $ elabTerm stx (some type)
      if Option.isSome $ e'.find? (fun e => e.isConstOf `sorryAx) then do
        emit  { declName := declName, inType := inType, result := DelaborateResult.sorryAx }
        return ()
      match ← isDefEq e e' with
      | true  => emit { declName := declName, inType := inType, result := DelaborateResult.success }
      | false => emit { declName := declName, inType := inType, result := DelaborateResult.nonDefEq }
    } catch ex => {
      let msg ← ex.toMessageData.toString;
      println! "[warn:no-elab] {msg}";
      emit { declName := declName, inType := inType, result := DelaborateResult.failedToElaborate }
    }
  } catch ex => {
    let msg ← ex.toMessageData.toString;
    println! "[warn:other] {msg}";
    emit { declName := declName, inType := inType, result := DelaborateResult.other }
  }

def checkConstant (env : Environment) (opts : Options) (cinfo : ConstantInfo) : IO (Array DataPoint) := do
  -- Note: currNamespace is the prefix of the constant's name.
  -- This is also the namespace we pass to delab
  let ((_, s), _, _) ← MetaM.toIO ((core.run {}).run {}) { options := opts, currNamespace := cinfo.name.getPrefix } { env := env }
  pure s.datapoints

  where
    core : DelaborateExperimentM (Array DataPoint) := do
      checkExpr cinfo.name true cinfo.type
      match cinfo.value? with
      | some value => pure () -- TODO: checkExpr cinfo.name false value
      | _ => pure ()
      (← get).datapoints

def runDelaborateExperiment (env : Environment) (opts : Options) : IO Unit := do
  let jobs ← env.constants.map₁.foldM (init := #[]) collectJobs
  let jobs ← env.constants.map₂.foldlM (init := jobs) collectJobs
  IO.FS.withFile "results.csv" IO.FS.Mode.write fun handle => do
    println! "-- waiting for {jobs.size} jobs --"
    let mut i := 0
    for (declName, job) in jobs do
      println! "[{i}] {declName}"
      (← IO.getStdout).flush
      i := i + 1
      match ← IO.wait job with
      | Except.ok datapoints => dumpResults handle datapoints
      | Except.error err => println! "[warn:task] {err}"

  where
    collectJobs (jobs : Array (Name × Job)) (name : Name) (cinfo : ConstantInfo) : IO (Array (Name × Job)) := do
      -- if !jobs.isEmpty then return jobs
      if BLACK_LIST.contains name then return jobs
      if isPrivateName name then return jobs
      if name.isInternal then return jobs
      if not ((`Mathlib).isPrefixOf name) then return jobs
      jobs.push (name, ← IO.asTask $ checkConstant env opts cinfo)

    dumpResults handle datapoints := do
      for ⟨declName, inType, result⟩ in datapoints do
        handle.putStr s!"{declName} {toString inType} {toString result}\n"

end DelaborateExperiment

open DelaborateExperiment

unsafe def withEnvOpts {α : Type} (f : Environment → Options → IO α) : IO α := do
  initSearchPath s!"../../lean4/build/release/stage1/lib/lean:../../Lib4"

  let opts : Options := {}
  let opts : Options := opts.insert `pp.all (DataValue.ofBool true)
  -- let opts : Options := opts.insert `synthInstance.maxHeartbeats (DataValue.ofNat 50000)

  let imports : List Import := [
    { module := `Init : Import },
    { module := `PrePort : Import },
    { module := `Lean3Lib.all : Import }
--    { module := `Mathlib.all : Import },
--    { module := `PostPort : Import }
  ]

  withImportModules imports (opts := opts) (trustLevel := 0) fun env => f env opts

unsafe def main : IO Unit := withEnvOpts runDelaborateExperiment
