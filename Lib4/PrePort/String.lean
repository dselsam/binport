/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import PrePort.Number

namespace Mathlib
namespace PrePort

def Fin (n : Nat) := {i : Nat // i < n}

abbrev is_valid_char (n : Nat) : Prop :=
  n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)

set_option pp.all true in
#print is_valid_char

/-
  ∀ n,
    @Eq.{1} Prop (Mathlib.PrePort.is_valid_char n)
      (Or
        (@HasLess.Less.{0} Nat Mathlib.nat.has_lt n
          (@OfNat.ofNat.{0} Nat 55296
            (@Mathlib.PrePort.instBits2Nat.{0} Nat Mathlib.nat.has_one Mathlib.nat.has_add 55295)))
        (And
          (@HasLess.Less.{0} Nat Mathlib.nat.has_lt
            (@OfNat.ofNat.{0} Nat 57343
              (@Mathlib.PrePort.instBits2Nat.{0} Nat Mathlib.nat.has_one Mathlib.nat.has_add 57342))
            n)
          (@HasLess.Less.{0} Nat Mathlib.nat.has_lt n
            (@OfNat.ofNat.{0} Nat 1114112
              (@Mathlib.PrePort.instBits2Nat.{0} Nat Mathlib.nat.has_one Mathlib.nat.has_add 1114111)))))

fun n =>
  Or (@HasLess.Less.{0} Nat instHasLessNat n (@OfNat.ofNat.{0} Nat 55296 (instOfNatNat 55296)))
    (And (@HasLess.Less.{0} Nat instHasLessNat (@OfNat.ofNat.{0} Nat 57343 (instOfNatNat 57343)) n)
      (@HasLess.Less.{0} Nat instHasLessNat n (@OfNat.ofNat.{0} Nat 1114112 (instOfNatNat 1114112))))
-/
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
