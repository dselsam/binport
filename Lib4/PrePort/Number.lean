/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

In Lean3, numerals are encoded using 0, 1, bit0, and bit1,
whereas in Lean4, nats are encoded as kernel literals
and numerals of type α are encoded using the following class:

class OfNat (α : Type u) (n : Nat) where
  ofNat : α

Specifically, the numeral (17 : α) is notation for

@OfNat.ofNat α 17 (inst : OfNat α 17)

We automatically replace the bit-representation with the OfNat representation
during porting (the two can be made definitionally equal).

Note that this file needs to coordinate with PrePost/Heterogeneous.lean.
-/
namespace Mathlib
namespace PrePort

-- We define these classes here so that we can align Mathlib's
-- classes to them.
class HasZero (α : Type u) := (zero : α)
class HasOne  (α : Type u) := (one : α)

universes u
variable {α : Type u} [HasZero α] [HasOne α] [Add α]

def bit0 (x : α) : α := x + x
def bit1 (x : α) : α := bit0 x + HasOne.one

instance instZero2Nat : OfNat α (noindex! 0) := ⟨HasZero.zero⟩
instance instOne2Nat  : OfNat α (noindex! 1) := ⟨HasOne.one⟩

-- TODO: well-founded
def nat2bits (n : Nat) (h : n > 0) : α := nat2bitsAux 1000 n where
  nat2bitsAux (fuel : Nat) (n : Nat) : α :=
    match fuel with
    | 0        => HasOne.one -- TODO: well-founded
    | fuel + 1 =>
      if n == 0 then HasOne.one -- note: this cannot occur and we don't want HasZero dep
      else if n == 1 then HasOne.one
      else if n % 2 == 1 then bit1 (nat2bitsAux fuel (n / 2))
      else bit0 (nat2bitsAux fuel (n / 2))

instance instBits2Nat (n : Nat) : OfNat α (noindex! (n+1)) := ⟨nat2bits (n+1) sorry⟩

namespace Number

theorem zeroSimp : @HasZero.zero α _ = 0 := rfl
theorem oneSimp  : @HasOne.one α   _ = 1 := rfl

end Number

#print OfNat.ofNat
#print instZero2Nat
#print instOne2Nat
#print instBits2Nat

end PrePort
end Mathlib
