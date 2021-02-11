/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import MathPort.Run
import MathPort.Path
import Lean

open Lean
open Lean.Meta

open MathPort

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [proofs, lib] =>
    let proofs : Bool ← match proofs.toNat? with
      -- TODO: why is the : Bool annotation ignored?
      | some k => if k > 0 then true else false
      | none   => throw $ IO.userError s!"First argument <proof> must be 0 or 1"
    match lib with
    | "lean3"   => MathPort.run proofs $ Path34.mk MODULES[1] ⟨"all"⟩
    | "mathlib" => MathPort.run proofs $ Path34.mk MODULES[0] ⟨"all"⟩
    | _         => throw $ IO.userError "Second argument <lib> must be 'lean3' or 'mathlib'"
  | _ => throw $ IO.userError "Expected <proof> <lib>"
