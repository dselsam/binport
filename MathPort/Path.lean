/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Lean3 structure:

- <lean3>/library/init/data/nat/basic.tlean
- <mathlib3>/src/data/nat/basic.tlean

Lean4 structure:

- Lib4/Lean3Lib/data/nat/basic.olean
- Lib4/Mathlib/data/nat/basic.olean

-/
import Lean

open Lean
open System (FilePath)

namespace MathPort

-- Example: data.nat.basic
structure DotPath where
  path : String
  deriving Inhabited, Repr

-- Example: data/nat/basic
structure ModRelPath where
  path   : FilePath
  deriving Inhabited, Repr

def DotPath.toModRelPath (p : DotPath) : ModRelPath :=
  ⟨System.mkFilePath $ p.path.splitOn "."⟩

def ModRelPath.toDotPath (p : ModRelPath) : DotPath :=
  ⟨".".intercalate $ p.path.components⟩

-- Example: Mathlib mathlib/src
structure ModuleInfo where
  l4name : FilePath
  l3path : FilePath
  deriving Inhabited, Repr

structure Path34 where
  modInfo : ModuleInfo
  mrpath  : ModRelPath
  deriving Inhabited, Repr

-------------------------------
-- START CONFIG
-- TODO: config file?
-------------------------------
def MODULES : Array ModuleInfo := #[
  ModuleInfo.mk "Mathlib"  "../mathlib3/src",
  ModuleInfo.mk "Lean3Lib" "../lean3/library",
  ModuleInfo.mk "Lean3Pkg" "../lean3/leanpkg"
]

def Lib4Path : FilePath := "Lib4"

def Lean4LibPath : FilePath := "../lean4/build/release/stage1/lib/lean"
-------------------------------
-- END CONFIG
-------------------------------

def Path34.toLean3 (p : Path34) (suffix : String) : FilePath :=
  (p.modInfo.l3path.join p.mrpath.path).withExtension suffix

def Path34.toTLean (p : Path34) : FilePath :=
  p.toLean3 "tlean"

def Path34.toLean4dot (p : Path34) : String :=
  ".".intercalate [p.modInfo.l4name.toString, p.mrpath.toDotPath.path]

def Path34.toLean4path (p : Path34) (suffix : String) : FilePath :=
  ((Lib4Path.join p.modInfo.l4name).join p.mrpath.path).withExtension suffix

def Path34.toLean4olean (p : Path34) : FilePath := 
  p.toLean4path "olean"

def resolveDotPath (dotPath : DotPath) : IO Path34 := do
  let mrp : ModRelPath := dotPath.toModRelPath
  for modInfo in MODULES do
    let p34 := Path34.mk modInfo mrp
    if ← p34.toTLean.pathExists then return p34
    let p34 := Path34.mk modInfo $ ⟨mrp.path.join "default"⟩
    if ← p34.toTLean.pathExists then return p34
  throw $ IO.userError s!"[resolveImport3] failed to resolve '{mrp.path}'"

end MathPort
