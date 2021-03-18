/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Lean3 structure:

- ./lean3/library/init/data/nat/basic.tlean
- ./mathlib/src/data/nat/basic.tlean

Lean4 structure:

- lib4/auto/Lean3Lib/data/nat/basic.olean
- lib4/auto/Mathlib/data/nat/basic.olean

-/
import Lean

open Lean

namespace MathPort

-- Example: data.nat.basic
structure DotPath where
  path : String
  deriving Inhabited, Repr

-- Example: data/nat/basic
structure ModRelPath where
  path   : String
  deriving Inhabited, Repr

def DotPath.toModRelPath (p : DotPath) : ModRelPath :=
  ⟨System.mkFilePath $ p.path.splitOn "."⟩

def ModRelPath.toDotPath (p : ModRelPath) : DotPath :=
  ⟨".".intercalate $ p.path.splitOn "/"⟩

def ModRelPath.toUnderscorePath (p : ModRelPath) : String :=
  ".".intercalate $ p.path.splitOn "_"

-- Example: Mathlib mathlib/src
structure ModuleInfo where
  l4name : String
  l3path : String
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
  ModuleInfo.mk "Mathlib"  "mathlib/src",
  ModuleInfo.mk "Lean3Lib" "lean3/library",
  ModuleInfo.mk "Lean3Pkg" "lean3/leanpkg"
]

def Lib4Path : String := "Lib4"

def Lean4LibPath : String := "lean4/build/release/stage1/lib/lean"
-------------------------------
-- END CONFIG
-------------------------------

def Path34.toLean3 (p : Path34) (suffix : String) : String :=
  System.mkFilePath [p.modInfo.l3path, p.mrpath.path] ++ suffix

def Path34.toTLean (p : Path34) : String :=
  p.toLean3 ".tlean"

def Path34.toLean4dot (p : Path34) : String :=
  ".".intercalate [p.modInfo.l4name, p.mrpath.toDotPath.path]

def Path34.toLean4path (p : Path34) (suffix : String) : String :=
  System.mkFilePath [Lib4Path, p.modInfo.l4name, p.mrpath.path] ++ suffix

def Path34.toLean4olean (p : Path34) : String := p.toLean4path ".olean"

def Path34.toLean4autolean (p : Path34) : String := p.toLean4path "_auto.lean"

def resolveDotPath (dotPath : DotPath) : IO Path34 := do
  let mrp : ModRelPath := dotPath.toModRelPath
  for modInfo in MODULES do
    let p34 := Path34.mk modInfo mrp
    if ← IO.fileExists p34.toTLean then return p34
    let p34 := Path34.mk modInfo $ ⟨mrp.path ++ "/default"⟩
    if ← IO.fileExists p34.toTLean then return p34
  throw $ IO.userError s!"[resolveImport3] failed to resolve '{mrp.path}'"

end MathPort
