import Lean3Lib.init.default

namespace Mathlib

universes u
variable {α : Type u} [has_zero α] [has_one α] [Add α]

-- TODO: well-founded
noncomputable def nat2bits (n : Nat) : α := nat2bitsAux 1000 n where
  nat2bitsAux (fuel : Nat) (n : Nat) : α :=
    match fuel with
    | 0 => has_zero.zero
    | fuel + 1 =>
      if n == 0 then has_zero.zero
      else if n == 1 then has_one.one
      else if n % 2 == 1 then bit1 (nat2bitsAux fuel (n / 2))
      else bit0 (nat2bitsAux fuel (n / 2))

noncomputable instance instNat2Bits (n : Nat) : OfNat α n  := ⟨nat2bits n⟩
noncomputable instance instZero2Nat : OfNat α (noindex! 0) := ⟨has_zero.zero⟩
noncomputable instance instOne2Nat  : OfNat α (noindex! 1) := ⟨has_one.one⟩

end Mathlib
