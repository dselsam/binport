import Lean

open Lean Lean.Meta

namespace SynthExperiment

structure Context where

structure State where
  handle : IO.FS.Handle

abbrev SynthExperimentM := ReaderT Context (StateRefT State MetaM)

def checkExpr (name : Name) (inType : Bool) (e : Expr) : SynthExperimentM Unit := transform e (pre := check) *> pure () where
  check (e : Expr) : SynthExperimentM TransformStep := do
    let type ← inferType e
    -- let type ← whnf type
    if !type.isApp then return TransformStep.visit e
    let f := type.getAppFn
    -- let f ← whnf f
    if !f.isConst then return TransformStep.visit e
    let clsName := f.constName!
    if !(isClass (← getEnv) clsName) then return TransformStep.visit e
    println! "[synth] {clsName} {name}"
    try
      let _ ← withCurrHeartbeats $ synthInstance type
      (← get).handle.putStr s!"{clsName}, {name}, {inType}, 1\n"
    catch ex =>
      println! "[warn] {← ex.toMessageData.toString}"
      (← get).handle.putStr s!"{clsName}, {name}, {inType}, 0\n"
    return TransformStep.done e

def checkConstant (cinfo : ConstantInfo) : SynthExperimentM Unit := do
  checkExpr cinfo.name true cinfo.type
  match cinfo.value? with
  | some v => checkExpr cinfo.name false v
  | _ => pure ()


def runSynthExperiment : SynthExperimentM Unit := do
  (← getEnv).constants.map₁.foldM (init := ()) check
  (← getEnv).constants.map₂.foldlM (init := ()) check
  where
    check _ name cinfo := do
      if isPrivateName name then return ()
      if name.isInternal then return ()
      if not ((`Mathlib).isPrefixOf name) then return ()
      try checkConstant cinfo
      catch ex => println! "[warn] {← ex.toMessageData.toString}"

end SynthExperiment

open SynthExperiment

unsafe def main : IO Unit := do
  initSearchPath s!"../../lean4/build/release/stage1/lib/lean:../../Lib4"
  let imports : List Import := [
    { module := `Init : Import },
    { module := `PrePort : Import },
    { module := `Mathlib.all : Import },
    { module := `PostPort : Import }
  ]
  withImportModules imports (opts := {}) (trustLevel := 0) $ λ env => do
    IO.FS.withFile "results.csv" IO.FS.Mode.write fun handle => do
      let _ ← MetaM.toIO ((runSynthExperiment.run {}).run' { handle := handle }) {} { env := env }
      pure ()

  println! "[ok]"
