/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
namespace Mathlib
namespace PrePort

def Fin (n : Nat) := {i : Nat // i < n}

abbrev is_valid_char (n : Nat) : Prop :=
  n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)

structure Char where
  val   : Nat
  valid : is_valid_char val

def toChar3 (c : _root_.Char) : Char := {
  val   := c.val.val.val,
  valid := c.valid
}

def fromChar3 (c : Char) (h : c.val < UInt32.size) : _root_.Char := {
  val   := ⟨⟨c.val, h⟩⟩,
  valid := c.valid
}

structure String where
  data : List Char

def toString3 (s : _root_.String) : String :=
  ⟨s.data.map toChar3⟩

section ListAll

variable {α β : Type} {p : α → Bool}

-- TODO: prove these
theorem allHead {x : α} {xs : List α} (h : (List.cons x xs).all p = true) : p x = true      := sorry
theorem allTail {x : α} {xs : List α} (h : (List.cons x xs).all p = true) : xs.all p = true := sorry

def mapAll (f : ∀ (x:α), p x = true → β) (xs : List α) (h : xs.all p = true) : List β :=
  match xs, h with
  | []   , _ => []
  | x::xs, h => f x (allHead h) :: mapAll f xs (allTail h)

def fromString3 (s : String) (h : s.data.all (λ c => Nat.ble c.val.succ UInt32.size) = true) : _root_.String :=
  ⟨mapAll fromChar3 s.data h⟩

end ListAll

#check @toString3
#check @fromString3


end PrePort
end Mathlib
