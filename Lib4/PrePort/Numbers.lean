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

We automatically wrap the bit-representation with the OfNat representation
during porting (the two are definitionally equal).

The non-kernel-computing `nat2bits` instance cannot be used during porting,
since mathlib currently relies on e.g. 2+2=4 computing in the kernel.
We keep it in PrePort to support various typeclass experiments.
-/
namespace Mathlib

-- We define these classes here so that we can align Mathlib's
-- classes to them.
class HasZero (α : Type u) := (zero : α)
class HasOne  (α : Type u) := (one : α)

universes u
variable {α : Type u} [HasZero α] [HasOne α] [Add α] [Inhabited α]

def bit0 (x : α) : α := x + x
def bit1 (x : α) : α := bit0 x + HasOne.one

-- TODO: these should be nat-lits, but currently the auto-porter
-- is sometimes creating terms with `OfNat.ofNat Nat ...` instead
instance instZero2Nat : OfNat α (no_index 0) /- (nat_lit 0) -/ := ⟨HasZero.zero⟩
instance instOne2Nat  : OfNat α (no_index 1) /- (nat_lit 1) -/ := ⟨HasOne.one⟩

-- TODO: well-founded
partial def nat2bits (n : Nat) : α :=
  if n == 0 then arbitrary
  else if n == 1 then HasOne.one
  else if n % 2 == 1 then bit1 (nat2bits (n / 2))
  else bit0 (nat2bits (n / 2))

instance instBits2Nat (n : Nat) : OfNat α (no_index (n+1)) /- (n+1) -/ := ⟨nat2bits (n+1)⟩

#print instZero2Nat
#print instOne2Nat
#print instBits2Nat

end Mathlib
