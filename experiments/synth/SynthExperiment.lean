import Lean
import Std.Data.HashSet

open Lean Lean.Meta
open Std (HashSet mkHashSet)

namespace SynthExperiment

structure Context where

structure State where
  handle : IO.FS.Handle
  visited : HashSet Expr := {}

abbrev SynthExperimentM := ReaderT Context (StateRefT State MetaM)

def checkExpr (name : Name) (inType : Bool) (e : Expr) : SynthExperimentM Unit := transform e (pre := check) *> pure () where
  check (e : Expr) : SynthExperimentM TransformStep := do
    if (← get).visited.contains e then return TransformStep.done e
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
      println! "[synth] {clsName} {name}"
      try
        let _ ← withCurrHeartbeats $ synthInstance type
        (← get).handle.putStr s!"{clsName} {name} {inType} 1\n"
      catch ex =>
        println! "[warn:synth] {clsName} {name} {inType} {← ex.toMessageData.toString}"
        (← get).handle.putStr s!"{clsName} {name} {inType} 0\n"
      modify fun s => { s with visited := s.visited.insert e }
      return TransformStep.done e
    catch ex =>
      modify fun s => { s with visited := s.visited.insert e }
      println! "[warn:check] {name} {← ex.toMessageData.toString}"
      return TransformStep.visit e

def checkConstant (cinfo : ConstantInfo) : SynthExperimentM Unit := do
  checkExpr cinfo.name true cinfo.type
  match cinfo.value? with
  | some v => checkExpr cinfo.name false v
  | _ => pure ()

def runSynthExperiment : SynthExperimentM Unit := withReducible $ do
  (← getEnv).constants.map₁.foldM (init := ()) check
  (← getEnv).constants.map₂.foldlM (init := ()) check
  where
    check _ name cinfo := do
      if isPrivateName name then return ()
      if name.isInternal then return ()
      if not ((`Mathlib).isPrefixOf name) then return ()
      println! "[check] {name}"
      try withCurrHeartbeats $ checkConstant cinfo
      catch ex => println! "[warn:uncaught] {name} {← ex.toMessageData.toString}"

end SynthExperiment

open SynthExperiment

unsafe def main : IO Unit := do
  initSearchPath s!"../../lean4/build/release/stage1/lib/lean:../../Lib4"

  let opts : Options := ({} : Options).insert `maxHeartbeats (DataValue.ofNat 1000)

  let imports : List Import := [
    { module := `Init : Import },
    { module := `PrePort : Import },
    { module := `Mathlib.all : Import },
    { module := `PostPort : Import }
  ]

  withImportModules imports (opts := {}) (trustLevel := 0) $ λ env => do
    IO.FS.withFile "results.csv" IO.FS.Mode.write fun handle => do
      let _ ← MetaM.toIO ((runSynthExperiment.run {}).run' { handle := handle }) { options := opts } { env := env }
      pure ()

  println! "[ok]"