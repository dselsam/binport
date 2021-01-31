/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Gabriel Ebner
-/
import MathPort.Util
import MathPort.Basic
import Lean
import Std.Data.HashSet
import Std.Data.HashMap

namespace MathPort

open Lean
open Std (HashSet mkHashSet HashMap mkHashMap)

def parseRules (rulesFilename : String) : PortM Unit :=
  IO.FS.withFile rulesFilename IO.FS.Mode.read fun h => do
    while (not (← h.isEof)) do
      match (← h.getLine).trim.splitOn " " with
      | ("#" :: _)         => pure ()
      | ["align", n₁, n₂]  => align (parseName n₁) (parseName n₂)
      | ["unchanged", n]   => unchanged (parseName n)
      | ["rename", n₁, n₂] => rename (parseName n₁) (parseName n₂)
      | ["sorry", n]       => addSorry (parseName n)
      | ["neversorry", n]  => addNeverSorry (parseName n)
      | ["noinst", n]      => addNoInst (parseName n)
      | [""]               => pure ()
      | tokens             => throwError s!"[loadRules] unexpected: '{tokens}'"

    where
      align (f t : Name) := modify $ λ s =>
        { s with newNames := s.newNames.insert f t,
                 ignored  := s.ignored.insert f }

      rename (f t : Name) := modify $ λ s =>
        { s with newNames := s.newNames.insert f t }

      unchanged (n : Name) := align n n

      addSorry (n : Name) := modify $ λ s =>
        { s with sorries := s.sorries.insert n }

      addNeverSorry (n : Name) := modify $ λ s =>
        { s with sorries := s.neverSorries.insert n }

      addNoInst (n : Name) := modify $ λ s =>
        { s with noInsts := s.noInsts.insert n }
