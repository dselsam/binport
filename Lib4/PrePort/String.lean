/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import PrePort.Number

namespace Mathlib
namespace PrePort

inductive Nat.LessThanOrEqual (a : Nat) : Nat → Prop
| refl : LessThanOrEqual a a
| step : ∀ {b}, LessThanOrEqual a b → LessThanOrEqual a b.succ

abbrev Nat.le (n m : Nat) := LessThanOrEqual n m
abbrev Nat.lt (n m : Nat) := LessThanOrEqual n.succ m

def Fin (n : Nat) := { i : Nat // Nat.lt i n }

abbrev isValidChar (n : Nat) : Prop :=
  Nat.lt n 0xd800 ∨ (Nat.lt 0xdfff n ∧ Nat.lt n 0x110000)

structure Char where
  val   : Nat
  valid : isValidChar val

def toChar3 (c : _root_.Char) : Char := {
  val   := c.val.val.val,
  valid := sorry
}

def fromChar3 (c : Char) : _root_.Char := {
  val   := ⟨⟨c.val, sorry⟩⟩,
  valid := sorry
}

structure String where
  data : List Char

def toString3 : _root_.String → String
  | ⟨data⟩ => ⟨data.map toChar3⟩

section ListAll

variable {α β : Type} {p : α → Bool}

def fromString3 (s : String) : _root_.String :=
  ⟨s.data.map fromChar3⟩

end ListAll

#check @String
#check @toString3
#check @fromString3

end PrePort
end Mathlib
