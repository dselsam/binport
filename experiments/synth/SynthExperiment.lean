import Lean
import Std.Data.HashSet

open Lean Lean.Meta
open Std (HashSet mkHashSet)

namespace SynthExperiment

def BLACK_LIST : HashSet Name :=
  ({} : HashSet Name)

inductive SynthResult where
  | success      : SynthResult
  | timeout      : SynthResult
  | failed       : SynthResult
  | instExpected : SynthResult
  | other        : SynthResult
  deriving Inhabited

instance : ToString SynthResult := ⟨fun
  | SynthResult.success      => "success"
  | SynthResult.timeout      => "timeout"
  | SynthResult.failed       => "failed"
  | SynthResult.instExpected => "instExpected"
  | SynthResult.other        => "other"
⟩

structure DataPoint where
  goal     : Expr
  clsName  : Name
  declName : Name
  inType   : Bool
  result   : SynthResult

abbrev Job := Task (Except IO.Error (Array DataPoint))

instance : Inhabited Job := ⟨⟨pure #[]⟩⟩

structure Context where

structure State where
  datapoints : Array DataPoint := #[]

abbrev SynthExperimentM := ReaderT Context (StateRefT State MetaM)

def emit (datapoint : DataPoint) : SynthExperimentM Unit :=
  modify fun s => { s with datapoints := s.datapoints.push datapoint }

def checkExpr (name : Name) (inType : Bool) (e : Expr) : SynthExperimentM Unit := transform e (pre := check) *> pure () where
  check (e : Expr) : SynthExperimentM TransformStep := do
    try
      if !e.isApp then return TransformStep.visit e
      if !e.getAppFn.isConst then return TransformStep.visit e
      if !(isGlobalInstance (← getEnv) e.getAppFn.constName!) then return TransformStep.visit e

      let type ← inferType e
      if !type.isApp then return TransformStep.visit e
      let f := type.getAppFn
      if !f.isConst then return TransformStep.visit e
      let clsName := f.constName!
      if !(isClass (← getEnv) clsName) then return TransformStep.visit e

      -- println! "[synth] {clsName} {name}"
      try
        let _ ← withCurrHeartbeats $ synthInstance type
        emit { goal := e, clsName := clsName, declName := name, inType := inType, result := SynthResult.success }
      catch ex =>
        let msg ← ex.toMessageData.toString
        let result ←
          if msg.take 6 == "failed" then SynthResult.failed
          else if msg.take 5 == "(dete" then SynthResult.timeout
          else if msg.take 28 == "type class instance expected" then SynthResult.instExpected
          else println! "[warn:other] {clsName} {name} {inType} '{msg}'" ; SynthResult.other
        emit { goal := e, clsName := clsName, declName := name, inType := inType, result := result }
      return TransformStep.done e
    catch ex =>
      println! "[warn:check] {name} {← ex.toMessageData.toString}"
      -- TODO: some of these are slow on every step
      -- return TransformStep.visit e
      return TransformStep.done e

def checkConstant (env : Environment) (opts : Options) (cinfo : ConstantInfo) : IO (Array DataPoint) := do
  let ((_, s), _, _) ← MetaM.toIO ((core.run {}).run {}) { options := opts } { env := env }
  pure s.datapoints

  where
    core : SynthExperimentM (Array DataPoint) := do
      checkExpr cinfo.name true cinfo.type
      match cinfo with
      | ConstantInfo.defnInfo d => checkExpr cinfo.name false d.value
      | ConstantInfo.thmInfo d  => checkExpr cinfo.name false d.value
      | _ => pure ()
      (← get).datapoints

def runSynthExperiment (env : Environment) (opts : Options) : IO Unit := do
  let jobs ← env.constants.map₁.foldM (init := #[]) collectJobs
  let jobs ← env.constants.map₂.foldlM (init := jobs) collectJobs
  IO.FS.withFile "results.csv" IO.FS.Mode.write fun handle => do
    println! "-- waiting for {jobs.size} jobs --"
    -- TODO: cache | let mut visited : HashSet Expr := {}
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
      if BLACK_LIST.contains name then return jobs
      if isPrivateName name then return jobs
      if name.isInternal then return jobs
      if not ((`Mathlib).isPrefixOf name) then return jobs
      jobs.push (name, ← IO.asTask $ checkConstant env opts cinfo)

    dumpResults handle datapoints := do
      for ⟨goal, clsName, declName, inType, result⟩ in datapoints do
        handle.putStr s!"{clsName} {declName} {inType} {toString result}\n"

end SynthExperiment

open SynthExperiment

unsafe def withEnvOpts {α : Type} (f : Environment → Options → IO α) : IO α := do
  initSearchPath s!"../../lean4/build/release/stage1/lib/lean:../../Lib4"

  let opts : Options := {}
  let opts : Options := opts.insert `maxHeartbeats (DataValue.ofNat 1000)
  let opts : Options := opts.insert `synthInstance.maxHeartbeats (DataValue.ofNat 50000)

  let imports : List Import := [
    { module := `Init : Import },
    { module := `PrePort : Import },
    { module := `Mathlib.all : Import },
    { module := `PostPort : Import }
  ]

  withImportModules imports (opts := opts) (trustLevel := 0) fun env => f env opts

unsafe def main : IO Unit := withEnvOpts runSynthExperiment
