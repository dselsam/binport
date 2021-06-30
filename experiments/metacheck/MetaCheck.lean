/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Std.Data.HashSet

open Lean Lean.Meta
open Std (HashSet mkHashSet)

namespace MetaCheckExperiment

def BLACK_LIST : HashSet Name :=
  ({} : HashSet Name)

def WHITE_LIST : HashSet Name :=
  ({} : HashSet Name)

inductive MetaCheckResult where
  | success      : MetaCheckResult
  | failed       : MetaCheckResult
  | timeout      : MetaCheckResult
  | other        : MetaCheckResult
  deriving Inhabited

instance : ToString MetaCheckResult := ⟨fun
  | MetaCheckResult.success      => "success"
  | MetaCheckResult.failed       => "failed"
  | MetaCheckResult.timeout      => "timeout"
  | MetaCheckResult.other        => "other"
⟩

structure DataPoint where
  declName : Name
  result   : MetaCheckResult

abbrev Job := Task (Except IO.Error (Array DataPoint))

instance : Inhabited Job := ⟨⟨pure #[]⟩⟩

structure Context where

structure State where
  datapoints : Array DataPoint := #[]

abbrev MetaCheckExperimentM := ReaderT Context (StateRefT State MetaM)

def emit (datapoint : DataPoint) : MetaCheckExperimentM Unit :=
  modify fun s => { s with datapoints := s.datapoints.push datapoint }

def checkTypeValue (declName : Name) (type value : Expr) : MetaCheckExperimentM Unit := do
  try
    let typeType ← inferType type -- (sanity test)
    let valueType ← inferType value
    let b ← isDefEq type valueType
    match b with
    | true  => emit { declName := declName, result := MetaCheckResult.success }
    | false => emit { declName := declName, result := MetaCheckResult.failed }
  catch ex =>
    let msg ← ex.toMessageData.toString
    println! "[warn:checkTypeValue:{declName}] {msg}"
    emit { declName := declName, result := MetaCheckResult.other }

def checkConstant (env : Environment) (opts : Options) (cinfo : ConstantInfo) : IO (Array DataPoint) := do
  let ((_, s), _, _) ← MetaM.toIO ((core.run {}).run {}) { options := opts } { env := env }
  pure s.datapoints

  where
    core : MetaCheckExperimentM (Array DataPoint) := do
      match cinfo.value? with
      | some value => checkTypeValue cinfo.name cinfo.type value
      | _ => pure ()
      (← get).datapoints

def runMetaCheckExperiment (env : Environment) (opts : Options) : IO Unit := do
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
      if !WHITE_LIST.isEmpty && !WHITE_LIST.contains name then return jobs
      if BLACK_LIST.contains name then return jobs
      if isPrivateName name then return jobs
      if name.isInternal then return jobs
      if not ((`Mathlib).isPrefixOf name) then return jobs
      jobs.push (name, ← IO.asTask $ checkConstant env opts cinfo)

    dumpResults handle datapoints := do
      for ⟨declName, result⟩ in datapoints do
        handle.putStr s!"{declName} {toString result}\n"

end MetaCheckExperiment

open MetaCheckExperiment

unsafe def withEnvOpts {α : Type} (f : Environment → Options → IO α) : IO α := do
  let imports := [{ module := `Init : Import }, { module := `Mathlib : Import }]
  let some LEAN_PATH ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH not set")
  initSearchPath LEAN_PATH

  let opts : Options := {}
  let opts : Options := opts.setNat `maxHeartbeats 100000
  let opts : Options := opts.setNat `synthInstance.maxHeartbeats 50000

  let imports : List Import := [
    -- { module := `Init : Import },
    -- { module := `PrePort : Import },
    -- { module := `Lean3Lib.init.data.nat.basic : Import },
    { module := `Mathlib : Import }
    -- { module := `PostPort : Import }
  ]

  withImportModules imports (opts := opts) (trustLevel := 0) fun env => f env opts

unsafe def main : IO Unit := withEnvOpts runMetaCheckExperiment
