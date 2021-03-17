/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import MathPort.Basic
import MathPort.Rules
import MathPort.ParseExport
import MathPort.ProcessActionItem
import MathPort.Path

import Lean
import Std.Data.HashMap
import Std.Data.HashSet

open Lean Lean.Meta
open Std (HashMap HashSet)

namespace MathPort
namespace Run -- TODO: better name. runAll? schedule?

abbrev Job := Task (Except IO.Error Unit)

instance : Inhabited Job := ⟨⟨pure ()⟩⟩

structure Context where
  proofs    : Bool

structure State where
  path2task : HashMap String Job := {}

abbrev RunM := ReaderT Context (StateRefT State IO)

-- TODO: weave
def rulesFilename := "rules.txt"

def parseTLeanImports (target : Path34) : IO (List Path34) := do
  let line ← IO.FS.withFile target.toTLean IO.FS.Mode.read fun h => h.getLine
  let tokens := line.trim.splitOn " " |>.toArray
  let nImports := tokens[1].toNat!
  let mut paths := #[]
  for i in [:nImports] do
    if tokens[2+2*i+1] ≠ "-1" then throw $ IO.userError "found relative import!"
    let dotPath : DotPath := ⟨tokens[2+2*i]⟩
    paths := paths.push $ ← resolveDotPath dotPath
  return paths.toList

def bindTasks (tasks : List Job) (k : Unit → IO Job) : IO Job :=
  match tasks with
  | []          => k ()
  | task::tasks => IO.bindTask task λ
    | Except.ok _ => bindTasks tasks k
    | Except.error err => throw err

@[implementedBy withImportModules]
constant withImportModulesConst {α : Type} (imports : List Import) (opts : Options) (trustLevel : UInt32 := 0) (x : Environment → IO α) : IO α :=
  throw $ IO.userError "NYI"

def genOLeanFor (proofs : Bool) (target : Path34) : IO Unit := do
  println! s!"[genOLeanFor] START {target.mrpath.path}"
  createDirectoriesIfNotExists target.toLean4olean

  let imports : List Import := [{ module := `Init : Import }, { module := `PrePort : Import }]
    ++ (← parseTLeanImports target).map fun path => { module := parseName path.toLean4dot }

  withImportModulesConst imports (opts := {}) (trustLevel := 0) $ λ env₀ => do
    let env₀ := env₀.setMainModule target.mrpath.toDotPath.path
    let _ ← PortM.toIO (ctx := { proofs := proofs, path := target }) (env := env₀) do
      parseRules rulesFilename
      IO.FS.withFile target.toTLean IO.FS.Mode.read fun h => do
       let _ ← h.getLine -- discard imports
       let mut actionItems := #[]
       while (not (← h.isEof)) do
         let line := (← h.getLine).dropRightWhile λ c => c == '\n'
         if line == "" then continue
         actionItems := actionItems.append (← processLine line).toArray

       let mut isIrreducible : Bool := false
       for actionItem in actionItems do
         processActionItem actionItem

      let env ← getEnv
      writeModule env target.toLean4olean
      println! s!"[genOLeanFor] END   {target.mrpath.path}"
    pure ()

partial def visit (target : Path34) : RunM Job := do
  match (← get).path2task.find? target.toTLean with
  | some task => pure task
  | none      => do
    if (← IO.fileExists target.toLean4olean) then
      IO.asTask (pure ())
    else
      let paths ← parseTLeanImports target
      let cjobs ← paths.mapM visit
      let job : Job ← bindTasks cjobs λ _ => IO.asTask $ genOLeanFor (← read).proofs target
      modify λ s => { s with path2task := s.path2task.insert target.toTLean job }
      pure job


end Run

open Run

unsafe def run (proofs : Bool) (target : Path34) : IO Unit := do
  initSearchPath s!"{Lean4LibPath}:{Lib4Path}"
  let job ← (visit target) { proofs := proofs } |>.run' (s := {})
  let result ← IO.wait job
  match result with
  | Except.ok _ => pure ()
  | Except.error err => throw err


end MathPort
