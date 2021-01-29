import Mathlib.data.nat.prime

open Mathlib Mathlib.nat

theorem exists_infinite_primes (n : Nat) : ∃ p, n ≤ p ∧ prime p :=
  let p := min_fac (factorial n + 1)
  have f1 : factorial n + 1 ≠ 1 := ne_of_gt $ succ_lt_succ $ factorial_pos _
  have pp : prime p := min_fac_prime f1
  have np : n ≤ p := le_of_not_ge λ h =>
    have h₁ : p ∣ factorial n := dvd_factorial (min_fac_pos _) h
    have h₂ : p ∣ 1 := (nat.dvd_add_iff_right h₁).2 (min_fac_dvd _)
    pp.not_dvd_one h₂
  Exists.intro p ⟨np, pp⟩
