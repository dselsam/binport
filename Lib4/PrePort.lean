/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import PrePort.Numbers

-- TODO: put elsewhere
axiom _placeholder_ (α : Prop) : α

@[appUnexpander _placeholder_] def unexpandPlaceholder : Lean.PrettyPrinter.Unexpander
  | `(_placeholder_ $prop:term) => `(?_)
  | _                           => throw ()

#check _placeholder_ (2 + 2 = 4)
