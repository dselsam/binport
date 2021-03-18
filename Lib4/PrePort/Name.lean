/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import PrePort.Numbers
import PrePort.String

namespace Mathlib

def unsignedSz : Nat := Nat.succ 4294967295
def unsigned := Fin unsignedSz

inductive Name
| anonymous  : Name
| mk_string  : String → Name → Name
| mk_numeral : unsigned  → Name → Name

def Name.fromName3 : Name → Lean.Name
--  | anonymous      => Lean.Name.anonymous
  | mk_string s n  => Lean.Name.mkStr n.fromName3 s.fromString3
--  | mk_numeral k n => Lean.Name.num k.fromUnsigned (fromName3 n)



end Mathlib
