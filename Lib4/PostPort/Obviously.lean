/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Strings do not easily align, and mathlib seems to only use `auto_param` with `obviously`.
So, for now we just always do the same.
-/
import Lean.Elab.Tactic

namespace Mathlib
open Lean.Elab.Tactic

def obviously : TacticM Unit := do
  throwError s!"tactic `obviously` not implemented"

end Mathlib
